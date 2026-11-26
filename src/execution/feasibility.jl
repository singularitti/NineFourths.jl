# Default Int budgets for recursive coefficient reads and live dense entries.
const DEFAULT_COEFFICIENT_VISITS = 10_000_000
const DEFAULT_WORKSPACE_ENTRIES = 10_000_000

"""
    ExecutionInfeasible

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

# Explain a scheme's index or visit limit for a numeric or symbolic side.
# The visits argument is the integer coefficient-visit budget.
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

# Package a Symbol reason, an (m, k, n) shape of Int dimensions, a scheme that
# supplies block_side, and the integer limit or nothing.
function _execution_failure(reason, shape, scheme, limit=nothing)
    m, k, n = shape
    square_side = m == k == n ? m : nothing
    side = any(iszero, shape) ? nothing : block_side(scheme)
    return ExecutionInfeasible(
        reason, square_side, shape, side, isnothing(limit) ? nothing : big(limit)
    )
end

# Return BigInt entry counts for the left input, right input, and output matrices.
_matrix_entries((m, k, n)) = (big(m) * k, big(k) * n, big(m) * n)

# The entries are a nonempty collection of integer counts, typically BigInt.
function _has_addressable_matrices(entries)
    bytes_per_entry = max(sizeof(Int), Base.elsize(Matrix{Rational{BigInt}}))
    return maximum(entries) <= div(typemax(Int), bytes_per_entry)
end

# The shape is the integer triple (m, k, n) of one layer and side is the integer
# number of blocks along each axis. Return the corresponding child dimensions.
_child_shape(shape, side) = map(dimension -> cld(dimension, side), shape)

# The shape and child are (m, k, n) triples for this layer and its child.
# Return the number of nonempty blocks along each dimension.
_active_blocks(shape, child) = map(cld, shape, child)

# Use another scheme layer when the integer side exceeds one and fits each
# of the three integer dimensions in child_shape.
_apply_child_layer(side, child_shape) = side > 1 && minimum(child_shape) >= side

# A previously specialized seed can shrink when moved into another field.
# Use its smallest possible rank before input normalization, then enforce
# the actual rank after selecting the Fourier orders in the common field.
# Both limits are integers. Return (side, rank) within the limits or nothing.
function _minimum_dimensions(scheme, max_side, max_rank)
    return execution_dimensions(scheme, max_side, max_rank)
end

# For a LoweredScheme, compare the block side and smallest possible rank
# after field specialization with the integer limits max_side and max_rank.
function _minimum_dimensions(scheme::LoweredScheme, max_side, max_rank)
    side = block_side(scheme)
    side <= max_side || return nothing
    polynomial = scheme.seed.polynomial
    rank_count(polynomial) == size(polynomial, 3) &&
        return execution_dimensions(scheme, max_side, max_rank)
    rank = _bounded_power(size(polynomial, 3), 6 * scheme.seed.copies, max_rank)
    return isnothing(rank) ? nothing : (Int(side), Int(rank))
end

# Plan an (m, k, n) product with positive Int dimensions and nonnegative
# integer budgets. The dimensions_for(scheme, max_side, max_rank) callback
# returns positive integer (side, rank) within the bounds or nothing.
# Return a named tuple (; side, rank) or an ExecutionInfeasible value.
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

# Enforce the integer entry budget for the two inputs and output of an (m, k, n)
# product. The scheme supplies block_side for diagnostics.
function _check_classical_workspace(shape, scheme, max_workspace_entries)
    entries = _matrix_entries(shape)
    _has_addressable_matrices(entries) ||
        throw(_execution_failure(:matrix_size, shape, scheme))
    if sum(entries) > max_workspace_entries
        throw(_execution_failure(:workspace_entries, shape, scheme, max_workspace_entries))
    end
    return nothing
end

# Enforce the integer entry budget for the m×n output when the (m, k, n)
# shape has a zero dimension. The scheme is passed along for diagnostics.
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
