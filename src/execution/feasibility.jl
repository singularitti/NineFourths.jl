"""
    DEFAULT_COEFFICIENT_VISITS

Default limit on the total number of coefficient reads across all scheme layers.
"""
const DEFAULT_COEFFICIENT_VISITS = 10_000_000

"""
    DEFAULT_WORKSPACE_ENTRIES

Default limit on the number of live dense matrix entries in a product.
"""
const DEFAULT_WORKSPACE_ENTRIES = 10_000_000

"""
    ExecutionInfeasible
    ExecutionInfeasible(reason, input_size, input_shape, block_side, limit)

The requested multiplication could not run a scheme layer. The `reason` symbol
identifies the failed check. The `input_shape::NTuple{3,Int}` gives `(m, k, n)`
for an `m×k` by `k×n` product. The `input_size` is the common `Int` dimension
for square inputs of equal size and `nothing` otherwise. The `block_side` may
be an integer, a symbolic `WitnessSide`, or `nothing` for a zero dimension.
The `limit` is the relevant resource bound as a `BigInt` or `nothing`.
"""
struct ExecutionInfeasible{S} <: Exception
    reason::Symbol
    input_size::Union{Int,Nothing}
    input_shape::NTuple{3,Int}
    block_side::S
    limit::Union{BigInt,Nothing}
end

"""
    showerror(io::IO, error::ExecutionInfeasible)

Write the product shape and the failed feasibility check to `io`.
"""
function Base.showerror(io::IO, error::ExecutionInfeasible)
    m, k, n = error.input_shape
    print(io, "cannot multiply ", m, '×', k, " by ", k, '×', n, " matrices")
    if !isnothing(error.block_side)
        print(io, " with requested block side ", error.block_side)
    end
    print(io, ". ")
    return if error.reason === :matrix_size
        print(io, "the dense matrix dimensions exceed the machine's array bounds")
    elseif error.reason === :scheme_dimensions
        _show_dimension_failure(io, error.block_side, error.limit)
    elseif error.reason === :coefficient_visits
        print(
            io,
            "the recursive product requires more than ",
            error.limit,
            " coefficient visits",
        )
    else
        print(
            io, "the product requires more than ", error.limit, " dense workspace entries"
        )
    end
end

"""
    _show_dimension_failure(io::IO, side::Integer, visits)

Write the failed side or rank bound for a numerical `side` to `io`.

Use the integer `visits` budget to bound rank when the side fits machine indices.
"""
function _show_dimension_failure(io::IO, side::Integer, visits)
    max_side = isqrt(typemax(Int))
    return if side > max_side
        print(io, "the block side exceeds the largest addressable side ", max_side)
    else
        max_rank = min(typemax(Int), div(visits, 3))
        print(
            io,
            "the scheme has more than ",
            max_rank,
            " addressable rank terms allowed by the coefficient-visit budget",
        )
    end
end

"""
    _show_dimension_failure(io::IO, side::WitnessSide, visits)

Write the failed dimension check for a symbolic Shpilka block side to `io`.

Report a symbolic lower bound when it already exceeds the largest indexable side.
"""
function _show_dimension_failure(io::IO, side::WitnessSide, visits)
    scheme = side.scheme
    lower_log = 2 * scheme.program.copies * scheme.derivation.parameters.q
    max_side = isqrt(typemax(Int))
    return if lower_log >= ndigits(max_side; base=2)
        print(
            io,
            "the construction requires a block side of at least 2^",
            lower_log,
            ", exceeding the largest addressable side ",
            max_side,
        )
    else
        print(
            io,
            "the scheme exceeds the index bounds or the budget of ",
            visits,
            " coefficient visits",
        )
    end
end

"""
    _execution_failure(reason, shape, scheme, limit=nothing)::ExecutionInfeasible

Package a feasibility failure with its symbolic `reason` and `(m, k, n)` shape.

Record the scheme's `block_side` for positive shapes, the common dimension for
square factors of equal size, and the resource `limit` when supplied.
"""
function _execution_failure(reason, shape, scheme, limit=nothing)
    m, k, n = shape
    square_side = m == k == n ? m : nothing
    side = any(iszero, shape) ? nothing : block_side(scheme)
    return ExecutionInfeasible(
        reason, square_side, shape, side, isnothing(limit) ? nothing : big(limit)
    )
end

"""
    _matrix_entries((m, k, n)) -> (left, right, output)

Return `BigInt` entry counts for the two factors and result of an `m×k` by `k×n` product.
"""
_matrix_entries((m, k, n)) = (big(m) * k, big(k) * n, big(m) * n)

"""
    _has_addressable_matrices(entries)

Check a nonempty collection of matrix entry counts against the array byte bound.

Use the larger of an `Int` slot and a `Rational{BigInt}` slot for the estimate.
"""
function _has_addressable_matrices(entries)
    bytes_per_entry = max(sizeof(Int), Base.elsize(Matrix{Rational{BigInt}}))
    return maximum(entries) <= div(typemax(Int), bytes_per_entry)
end

"""
    _child_shape(shape, side)

Divide each of the three dimensions by `side` and round up to give the child block shape.
"""
_child_shape(shape, side) = map(dimension -> cld(dimension, side), shape)

"""
    _active_blocks(shape, child)

Count the blocks containing input or output coordinates along each of three axes.

The `shape` and positive `child` dimensions are `(m, k, n)` triples.
"""
_active_blocks(shape, child) = map(cld, shape, child)

"""
    _apply_child_layer(side, child_shape)

Test whether another recursive layer fits all child dimensions and can shrink them.
"""
_apply_child_layer(side, child_shape) = side > 1 && minimum(child_shape) >= side

"""
    _minimum_dimensions(scheme, max_side, max_rank)

Return a `(side, rank)` pair within the limits for preflight, or `nothing`.

Use the scheme's `execution_dimensions` unless field specialization can change its rank.
"""
function _minimum_dimensions(scheme, max_side, max_rank)
    return execution_dimensions(scheme, max_side, max_rank)
end

"""
    _minimum_dimensions(scheme::LoweredScheme, max_side, max_rank)

Check the block side and a lower bound on the rank after field specialization.

A previously specialized seed can shrink in another field. Preflight uses
its minimum possible rank, and planning checks the actual rank after selecting
the Fourier orders for the input field.
"""
function _minimum_dimensions(scheme::LoweredScheme, max_side, max_rank)
    side = block_side(scheme)
    side <= max_side || return nothing
    polynomial = scheme.seed.polynomial
    rank_count(polynomial) == size(polynomial, 3) &&
        return execution_dimensions(scheme, max_side, max_rank)
    rank = _bounded_power(size(polynomial, 3), 6 * scheme.seed.copies, max_rank)
    return isnothing(rank) ? nothing : (Int(side), Int(rank))
end

"""
    _execution_plan(shape, scheme, max_coefficient_visits, max_workspace_entries;
                    dimensions_for=execution_dimensions)

Check a positive `(m, k, n)` product and its recursive layers against both budgets.

Call `dimensions_for(scheme, max_side, max_rank)` to obtain positive, bounded
scheme dimensions or `nothing`. Return a named tuple with `side` and `rank` on
success or an `ExecutionInfeasible` value describing the failed check.
"""
function _execution_plan(
    shape,
    scheme,
    max_coefficient_visits,
    max_workspace_entries;
    dimensions_for=execution_dimensions,
)
    top_level_entries = _matrix_entries(shape)
    _has_addressable_matrices(top_level_entries) ||
        return _execution_failure(:matrix_size, shape, scheme)
    # Every rank term visits at least one coordinate in each of the three legs.
    max_rank = min(typemax(Int), div(max_coefficient_visits, 3))
    dimensions = dimensions_for(scheme, isqrt(typemax(Int)), max_rank)
    if isnothing(dimensions)
        return _execution_failure(:scheme_dimensions, shape, scheme, max_coefficient_visits)
    end
    side, rank = dimensions
    side > 0 && rank > 0 || throw(ArgumentError("a scheme needs a positive side and rank"))
    # The promoted inputs and scheme result coexist. During recursion each
    # active level also retains two linear forms and one child product. Output
    # conversion uses a second output matrix after those forms are gone.
    entries = sum(top_level_entries)
    conversion_entries = entries + last(top_level_entries)
    visits = big(0)
    calls = big(1)
    layer_shape = shape
    while true
        child = _child_shape(layer_shape, side)
        active = _active_blocks(layer_shape, child)
        visits += calls * rank * sum(_matrix_entries(active))
        if visits > max_coefficient_visits
            return _execution_failure(
                :coefficient_visits, shape, scheme, max_coefficient_visits
            )
        end
        entries += sum(_matrix_entries(child))
        if max(entries, conversion_entries) > max_workspace_entries
            return _execution_failure(
                :workspace_entries, shape, scheme, max_workspace_entries
            )
        end
        _apply_child_layer(side, child) || return (; side, rank)
        layer_shape = child
        calls *= rank
    end
end

"""
    _check_classical_workspace(shape, scheme, max_workspace_entries)

Check the two factors and result of a conventional `(m, k, n)` product.

Throw `ExecutionInfeasible` on an array bound or workspace budget violation.
"""
function _check_classical_workspace(shape, scheme, max_workspace_entries)
    entries = _matrix_entries(shape)
    _has_addressable_matrices(entries) ||
        throw(_execution_failure(:matrix_size, shape, scheme))
    if sum(entries) > max_workspace_entries
        throw(_execution_failure(:workspace_entries, shape, scheme, max_workspace_entries))
    end
    return nothing
end

"""
    _check_zero_workspace(shape, scheme, max_workspace_entries)

Check the `m×n` output bounds for a product with a zero dimension in `shape`.

Throw `ExecutionInfeasible` when the output is unaddressable or exceeds the entry budget.
"""
function _check_zero_workspace(shape, scheme, max_workspace_entries)
    m, _, n = shape
    output_entries = big(m) * n
    if max(m, n) == typemax(Int) || !_has_addressable_matrices((output_entries,))
        throw(_execution_failure(:matrix_size, shape, scheme))
    end
    if output_entries > max_workspace_entries
        throw(_execution_failure(:workspace_entries, shape, scheme, max_workspace_entries))
    end
    return nothing
end
