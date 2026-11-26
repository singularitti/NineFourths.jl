const DEFAULT_COEFFICIENT_VISITS = 10_000_000
const DEFAULT_WORKSPACE_ENTRIES = 10_000_000

"""
    ExecutionInfeasible

The requested multiplication could not run a scheme layer. `reason` identifies
the failed check. `input_size` and `block_side` describe the input and the
scheme, and `limit` holds the applicable resource bound when there is one.
"""
struct ExecutionInfeasible{S} <: Exception
    reason::Symbol
    input_size::Int
    block_side::S
    limit::Union{BigInt,Nothing}
end

function Base.showerror(io::IO, error::ExecutionInfeasible)
    print(io, "cannot execute scheme for ", error.input_size, '×', error.input_size,
          " matrices with block side ", error.block_side, ". ")
    if error.reason === :empty_input
        print(io, "empty matrices have no multiplication layer")
    elseif error.reason === :matrix_size
        print(io, "the dense matrix dimensions exceed the machine's array bounds")
    elseif error.reason === :scheme_dimensions
        _show_dimension_failure(io, error.block_side, error.limit)
    elseif error.reason === :coefficient_visits
        print(io, "the recursive product requires more than ", error.limit, " coefficient visits")
    else
        print(io, "the product requires more than ", error.limit, " dense workspace entries")
    end
end

function _show_dimension_failure(io::IO, side::Integer, visits)
    max_side = isqrt(typemax(Int))
    if side > max_side
        print(io, "the block side exceeds the largest addressable side ", max_side)
    else
        max_rank = min(typemax(Int), div(visits, 3))
        print(io, "the scheme has more than ", max_rank,
              " addressable rank terms allowed by the coefficient-visit budget")
    end
end

function _show_dimension_failure(io::IO, side::WitnessSide, visits)
    scheme = side.scheme
    lower_log = 2 * scheme.program.copies * scheme.derivation.parameters.q
    max_side = isqrt(typemax(Int))
    if lower_log >= ndigits(max_side; base=2)
        print(io, "the construction requires a block side of at least 2^", lower_log,
              ", exceeding the largest addressable side ", max_side)
    else
        print(io, "the scheme exceeds the index bounds or the budget of ", visits, " coefficient visits")
    end
end

function _execution_failure(reason, n, scheme, limit=nothing)
    return ExecutionInfeasible(reason, n, block_side(scheme), isnothing(limit) ? nothing : big(limit))
end

function _has_addressable_matrices(n)
    bytes_per_entry = max(sizeof(Int), Base.elsize(Matrix{Rational{BigInt}}))
    return n <= isqrt(div(typemax(Int), bytes_per_entry))
end

_apply_child_layer(side, child_size) = side > 1 && child_size >= side

function _execution_plan(n, scheme, max_coefficient_visits, max_workspace_entries)
    iszero(n) && return _execution_failure(:empty_input, n, scheme)
    _has_addressable_matrices(n) || return _execution_failure(:matrix_size, n, scheme)

    # Each nonempty layer visits at least one coordinate in each of the three legs.
    max_rank = min(typemax(Int), div(max_coefficient_visits, 3))
    dimensions = execution_dimensions(scheme, isqrt(typemax(Int)), max_rank)
    if isnothing(dimensions)
        return _execution_failure(:scheme_dimensions, n, scheme, max_coefficient_visits)
    end
    side, rank = dimensions
    side > 0 && rank > 0 || throw(ArgumentError("a scheme needs a positive side and rank"))

    # The promoted inputs and scheme result coexist. During recursion each
    # active level also retains two linear forms and one child product. Output
    # conversion uses a fourth top-level matrix after those forms are gone.
    top_level_entries = big(n)^2
    conversion_entries = 4 * top_level_entries
    entries = 3 * top_level_entries
    visits = big(0)
    calls = big(1)
    layer_size = n
    while true
        child_size = cld(layer_size, side)
        active_side = cld(layer_size, child_size)
        visits += 3 * calls * rank * active_side^2
        if visits > max_coefficient_visits
            return _execution_failure(:coefficient_visits, n, scheme, max_coefficient_visits)
        end
        entries += 3 * big(child_size)^2
        if max(entries, conversion_entries) > max_workspace_entries
            return _execution_failure(:workspace_entries, n, scheme, max_workspace_entries)
        end
        _apply_child_layer(side, child_size) || return (; side, rank)
        layer_size = child_size
        calls *= rank
    end
end

function _check_classical_workspace(n, scheme, max_workspace_entries)
    _has_addressable_matrices(n) || throw(_execution_failure(:matrix_size, n, scheme))
    if 3 * big(n)^2 > max_workspace_entries
        throw(_execution_failure(:workspace_entries, n, scheme, max_workspace_entries))
    end
    return nothing
end
