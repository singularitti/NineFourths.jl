function _contains_rationals(matrix)
    T = eltype(matrix)
    T <: Integer && return false
    if typeintersect(T, Union{Integer,Rational}) === Union{}
        throw(ArgumentError("matrix entries must be integers or rationals"))
    end
    rational = T <: Rational
    for value in matrix
        if value isa Rational
            iszero(denominator(value)) && throw(DomainError(value, "matrix entries must be finite"))
            rational = true
        elseif !(value isa Integer)
            throw(ArgumentError("matrix entries must be integers or rationals"))
        end
    end
    return rational
end

function _execution_zeros(n)
    return fill!(Matrix{ExactScalar}(undef, n, n), zero(Rational{BigInt}))
end

function _classical_leaf(A, B)
    C = _execution_zeros(size(A, 1))
    for column in axes(B, 2), k in axes(A, 2)
        b = B[k, column]
        iszero(b) && continue
        for row in axes(A, 1)
            C[row, column] += A[row, k] * b
        end
    end
    return C
end

function _accumulate_forms!(left, right, A, B, scheme, term, side, active_side)
    child_size = size(left, 1)
    n = size(A, 1)
    for block_column in 1:active_side, block_row in 1:active_side
        coordinate = block_row + (block_column - 1) * side
        u = scheme_coefficient(scheme, term, 1, coordinate)
        v = scheme_coefficient(scheme, term, 2, coordinate)
        use_u = !iszero(u)
        use_v = !iszero(v)
        use_u || use_v || continue
        row_offset = (block_row - 1) * child_size
        column_offset = (block_column - 1) * child_size
        for column in 1:min(child_size, n - column_offset), row in 1:min(child_size, n - row_offset)
            i = row_offset + row
            j = column_offset + column
            if use_u
                left[row, column] += u * A[i, j]
            end
            if use_v
                right[row, column] += v * B[i, j]
            end
        end
    end
    return nothing
end

function _accumulate_product!(C, product, scheme, term, side, active_side)
    child_size = size(product, 1)
    n = size(C, 1)
    for block_column in 1:active_side, block_row in 1:active_side
        coordinate = block_row + (block_column - 1) * side
        w = scheme_coefficient(scheme, term, 3, coordinate)
        iszero(w) && continue
        row_offset = (block_row - 1) * child_size
        column_offset = (block_column - 1) * child_size
        for column in 1:min(child_size, n - column_offset), row in 1:min(child_size, n - row_offset)
            C[row_offset + row, column_offset + column] += w * product[row, column]
        end
    end
    return nothing
end

function _scheme_product(A, B, scheme, side, rank)
    n = size(A, 1)
    child_size = cld(n, side)
    active_side = cld(n, child_size)
    C = _execution_zeros(n)
    left = _execution_zeros(child_size)
    right = _execution_zeros(child_size)
    for term in 1:rank
        fill!(left, zero(Rational{BigInt}))
        fill!(right, zero(Rational{BigInt}))
        _accumulate_forms!(left, right, A, B, scheme, term, side, active_side)
        product = if _apply_child_layer(side, child_size)
            _scheme_product(left, right, scheme, side, rank)
        else
            _classical_leaf(left, right)
        end
        _accumulate_product!(C, product, scheme, term, side, active_side)
    end
    return C
end

"""
    multiply(A, B, scheme::BilinearScheme; fallback=:error,
             max_coefficient_visits=10_000_000, max_workspace_entries=10_000_000)

Multiply same-size square matrices of exact integers or finite rationals with
one-based indexing. The result is a dense `Matrix{BigInt}` for integer inputs
and a dense `Matrix{Rational{BigInt}}` if either input is rational.

The default requires at least one application of the bilinear rule. The
product uses implicit zero padding and applies further layers where a child
block can be split again. It uses conventional multiplication at the leaves.
If a layer is infeasible, including for empty inputs, `fallback=:classical`
allows an entirely conventional product. Input and arithmetic errors propagate.

The coefficient-visit limit bounds the sum of visits to the three legs across
all scheme layers. The workspace limit bounds dense scalar slots, including
promoted inputs and the result. These limits are checked before allocating
the multiplication workspace. The workspace limit also applies to fallback.
"""
function multiply(A::AbstractMatrix, B::AbstractMatrix, scheme::BilinearScheme;
                  fallback=:error, max_coefficient_visits::Integer=DEFAULT_COEFFICIENT_VISITS,
                  max_workspace_entries::Integer=DEFAULT_WORKSPACE_ENTRIES)
    fallback === :error || fallback === :classical ||
        throw(ArgumentError("fallback must be :error or :classical"))
    max_coefficient_visits >= 0 || throw(ArgumentError("max_coefficient_visits must be nonnegative"))
    max_workspace_entries >= 0 || throw(ArgumentError("max_workspace_entries must be nonnegative"))
    Base.require_one_based_indexing(A, B)
    size(A, 1) == size(A, 2) && size(A) == size(B) ||
        throw(DimensionMismatch("inputs must be square matrices of the same size"))
    n = size(A, 1)
    plan = _execution_plan(n, scheme, max_coefficient_visits, max_workspace_entries)
    use_classical = plan isa ExecutionInfeasible
    if use_classical
        fallback === :classical || throw(plan)
        _check_classical_workspace(n, scheme, max_workspace_entries)
    end

    rational_left = _contains_rationals(A)
    rational_right = _contains_rationals(B)
    T = rational_left || rational_right ? Rational{BigInt} : BigInt
    if use_classical
        return Matrix{T}(A) * Matrix{T}(B)
    end

    active_scheme = scheme isa PaperScheme ? lower_scheme(scheme) : scheme
    left = Matrix{Rational{BigInt}}(A)
    right = Matrix{Rational{BigInt}}(B)
    result = _scheme_product(left, right, active_scheme, plan.side, plan.rank)
    C = Matrix{T}(undef, n, n)
    for index in eachindex(C, result)
        C[index] = rational_result(result[index])
    end
    return C
end
