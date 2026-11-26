function _zero_matrix(::Type{T}, m, n, zero_value) where {T}
    C = Matrix{T}(undef, m, n)
    isempty(C) && return C
    isnothing(zero_value) && throw(ArgumentError("the output needs a zero in the input field"))
    return fill!(C, zero_value)
end

function _classical_product(A, B, zero_value, T, add=+, product=*)
    C = _zero_matrix(T, size(A, 1), size(B, 2), zero_value)
    for column in axes(B, 2), k in axes(A, 2)
        b = B[k, column]
        for row in axes(A, 1)
            C[row, column] = add(C[row, column], product(A[row, k], b))
        end
    end
    return C
end

function _accumulate_form!(form, source, scheme, domain, term, leg, side,
                           active_rows, active_columns)
    child_rows, child_columns = size(form)
    rows, columns = size(source)
    for block_column in 1:active_columns, block_row in 1:active_rows
        coordinate = block_row + (block_column - 1) * side
        coefficient = _field_coefficient(domain, scheme, term, leg, coordinate)
        _field_iszero(coefficient, domain.zero) && continue
        row_offset = (block_row - 1) * child_rows
        column_offset = (block_column - 1) * child_columns
        rows_in_block = min(child_rows, rows - row_offset)
        columns_in_block = min(child_columns, columns - column_offset)
        for column in 1:columns_in_block, row in 1:rows_in_block
            value = _field_apply(coefficient, source[row_offset + row, column_offset + column])
            form[row, column] = _field_add(form[row, column], value)
        end
    end
    return nothing
end

function _accumulate_product!(C, product, scheme, domain, term, side, active_rows, active_columns)
    child_rows, child_columns = size(product)
    rows, columns = size(C)
    for block_column in 1:active_columns, block_row in 1:active_rows
        coordinate = block_row + (block_column - 1) * side
        coefficient = _field_coefficient(domain, scheme, term, 3, coordinate)
        _field_iszero(coefficient, domain.zero) && continue
        row_offset = (block_row - 1) * child_rows
        column_offset = (block_column - 1) * child_columns
        rows_in_block = min(child_rows, rows - row_offset)
        columns_in_block = min(child_columns, columns - column_offset)
        for column in 1:columns_in_block, row in 1:rows_in_block
            i, j = row_offset + row, column_offset + column
            value = _field_apply(coefficient, product[row, column])
            C[i, j] = _field_add(C[i, j], value)
        end
    end
    return nothing
end

function _scheme_product(A, B, scheme, domain, zero_value, side, rank)
    m, k = size(A)
    n = size(B, 2)
    shape = (m, k, n)
    child = _child_shape(shape, side)
    child_m, child_k, child_n = child
    active_m, active_k, active_n = _active_blocks(shape, child)
    C = _zero_matrix(Any, m, n, zero_value)
    left = Matrix{Any}(undef, child_m, child_k)
    right = Matrix{Any}(undef, child_k, child_n)
    recurse = _apply_child_layer(side, child)
    for term in 1:rank
        fill!(left, zero_value)
        fill!(right, zero_value)
        _accumulate_form!(left, A, scheme, domain, term, 1, side, active_m, active_k)
        _accumulate_form!(right, B, scheme, domain, term, 2, side, active_k, active_n)
        product = if recurse
            _scheme_product(left, right, scheme, domain, zero_value, side, rank)
        else
            _classical_product(left, right, zero_value, Any, _field_add, _field_mul)
        end
        _accumulate_product!(C, product, scheme, domain, term, side, active_m, active_n)
    end
    return C
end

_wide_product(a, b) = big(a) * b

function _classical_fallback(inputs)
    product = inputs.legacy ? _wide_product : (*)
    return _classical_product(inputs.left, inputs.right, inputs.zero, inputs.eltype, +, product)
end

"""
    multiply(A, B, scheme::BilinearScheme; fallback=:error, field=nothing,
             max_coefficient_visits=10_000_000, max_workspace_entries=10_000_000)

Multiply an `m×k` matrix by a `k×n` matrix and return a dense Julia matrix.
With an inferred domain, Julia integer inputs produce `Matrix{BigInt}` and
Julia rational inputs produce `Matrix{Rational{BigInt}}`. Other inputs use
their common scalar field. Pass `field` to supply a parent, scalar type, or
representative element when needed.

For positive dimensions the default requires at least one bilinear scheme
layer. The product uses implicit zero padding along each axis and conventional
multiplication at the leaves. `fallback=:classical` permits a conventional
product when the requested scheme cannot execute in the input field or budgets.
A zero dimension determines an empty or zero result directly.

The visit budget bounds the coefficient visits across the recursive product.
The workspace budget bounds live dense matrix entries, including normalized
inputs and the result. The workspace budget also applies to classical fallback.
"""
function multiply(A::FieldMatrix, B::FieldMatrix, scheme::BilinearScheme;
                  fallback=:error, field=nothing,
                  max_coefficient_visits::Integer=DEFAULT_COEFFICIENT_VISITS,
                  max_workspace_entries::Integer=DEFAULT_WORKSPACE_ENTRIES)
    fallback === :error || fallback === :classical ||
        throw(ArgumentError("fallback must be :error or :classical"))
    max_coefficient_visits >= 0 || throw(ArgumentError("max_coefficient_visits must be nonnegative"))
    max_workspace_entries >= 0 || throw(ArgumentError("max_workspace_entries must be nonnegative"))
    m, k = size(A)
    right_rows, n = size(B)
    k == right_rows || throw(DimensionMismatch("input inner dimensions must match"))
    shape = (m, k, n)

    if any(iszero, shape)
        _check_zero_workspace(shape, scheme, max_workspace_entries)
        inputs = _field_inputs(A, B; field)
        return _zero_matrix(inputs.eltype, m, n, inputs.zero)
    end

    plan = _execution_plan(shape, scheme, max_coefficient_visits, max_workspace_entries;
                           dimensions_for=_minimum_dimensions)
    if plan isa ExecutionInfeasible
        fallback === :classical || throw(plan)
        _check_classical_workspace(shape, scheme, max_workspace_entries)
        inputs = _field_inputs(A, B; field)
        return _classical_fallback(inputs)
    end

    inputs = _field_inputs(A, B; field)
    try
        arithmetic = _scheme_arithmetic(scheme, inputs)
        adapted, domain = arithmetic.scheme, arithmetic.domain
        adapted_plan = adapted === scheme && !(scheme isa LoweredScheme) ? plan :
            _execution_plan(shape, adapted, max_coefficient_visits, max_workspace_entries)
        if adapted_plan isa ExecutionInfeasible
            fallback === :classical || throw(adapted_plan)
            return _classical_fallback(inputs)
        end

        result = _scheme_product(inputs.left, inputs.right, adapted, domain, inputs.zero,
                                 adapted_plan.side, adapted_plan.rank)
        C = Matrix{inputs.eltype}(undef, m, n)
        for index in eachindex(C, result)
            C[index] = _field_result(domain, result[index])
        end
        return C
    catch error
        fallback === :classical && error isa CoefficientIncompatible || rethrow()
        return _classical_fallback(inputs)
    end
end
