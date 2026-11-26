"""
    _zero_matrix(T::Type, m, n, zero_value)::Matrix{T}

Allocate an `m×n` matrix of element type `T` filled with `zero_value`.

Pass an additive identity convertible to `T`. Use `nothing` for an empty matrix.
"""
function _zero_matrix(::Type{T}, m, n, zero_value) where {T}
    C = Matrix{T}(undef, m, n)
    isempty(C) && return C
    isnothing(zero_value) &&
        throw(ArgumentError("the output needs a zero in the input field"))
    return fill!(C, zero_value)
end

"""
    _classical_product(A, B, zero_value, T, add=+, product=*)

Multiply two one-based matrices using conventional dot products.

Initialize each accumulation with `zero_value` and store the result in a `Matrix{T}`.
The binary `add` and `product` callbacks can operate on scalar or phase work values.
"""
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

"""
    _accumulate_form!(form, source, scheme, domain, term, leg, side,
                      active_rows, active_columns)

Add one scheme input form from `source` to the one-based child buffer `form`.

Select the left or right input form of `term` with `leg` equal to 1 or 2. The
square block grid has side `side`, and the active dimensions count the block
rows and columns containing source entries. Blocks beyond the source index
ranges contribute zero. The scalar `domain` comes from `_field_inputs`.
"""
function _accumulate_form!(
    form, source, scheme, domain, term, leg, side, active_rows, active_columns
)
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
            value = _field_apply(
                coefficient, source[row_offset + row, column_offset + column]
            )
            form[row, column] = _field_add(form[row, column], value)
        end
    end
    return nothing
end

"""
    _accumulate_product!(C, product, scheme, domain, term, side,
                         active_rows, active_columns)

Add `product` to the output `C` using the reconstruction weights for `term`.

Update the active block rows and columns of the grid of side `side`. The scalar
`domain` comes from `_field_inputs`. Trim each block to the output index ranges.
"""
function _accumulate_product!(
    C, product, scheme, domain, term, side, active_rows, active_columns
)
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

"""
    _scheme_product(A, B, scheme, domain, zero_value, side, rank)

Multiply two one-based matrices using one scheme layer and any admissible child layers.

The layer uses `rank` terms and a block grid of side `side`. It constructs child
input forms in the selected `domain` and uses conventional multiplication when
the child dimensions reach the recursion limit. The returned `Matrix{Any}` can
hold native scalars and formal phase work values pending output conversion.
"""
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

"""
    _wide_product(a, b)

Multiply built-in integer or rational scalars after widening the left factor.
"""
_wide_product(a, b) = big(a) * b

"""
    _classical_fallback(inputs)

Use conventional multiplication on the normalized factors from `_field_inputs`.

Widen scalar products for inferred built-in integers and rationals. Other fields
use their native addition and multiplication.
"""
function _classical_fallback(inputs)
    product = inputs.legacy ? _wide_product : (*)
    return _classical_product(
        inputs.left, inputs.right, inputs.zero, inputs.eltype, +, product
    )
end

"""
    multiply(A, B, scheme; <keyword arguments>)::Matrix

Multiply an `m×k` matrix by a `k×n` matrix using a bilinear scheme.

For positive dimensions the default requires at least one bilinear scheme
layer. The product uses implicit zero padding along each axis and conventional
multiplication at the leaves. A zero dimension determines an empty or zero
matrix directly.

With the default `field=nothing`, built-in Julia integer inputs produce
`Matrix{BigInt}`. Built-in rational inputs, including mixtures with built-in
integers, produce `Matrix{Rational{BigInt}}`. Other inputs use their common
scalar domain. All results are dense Julia matrices.

# Arguments

  - `fallback=:error` requires the scheme. Use `:classical` to permit a conventional
    product when the scheme exceeds its execution bounds or a coefficient cannot act
    in the selected domain.
  - `field=nothing` infers the scalar domain from the input. Supply a parent callable
    as `field(0)` and `field(1)`, a scalar type with identities, or a representative
    element to select it explicitly.
  - `max_coefficient_visits::Integer=10_000_000` bounds coefficient reads across the
    recursive product.
  - `max_workspace_entries::Integer=10_000_000` bounds live dense entries, including
    normalized inputs and the result. It also applies to a conventional product.

Both budgets must be nonnegative.

See also [`BilinearScheme`](@ref), [`multiplication_scheme`](@ref), and
[`verify_scheme`](@ref).

# Examples

```jldoctest
julia> using NineFourths

julia> scalar_rule = BilinearScheme([1;;], [1;;], [1;;]);

julia> C = multiply([1 2 3; 4 5 6], [1 0; 0 1; 1 1], scalar_rule);

julia> (eltype(C), C == [4 5; 10 11])
(BigInt, true)

julia> paper_rule = multiplication_scheme();

julia> C = multiply([2;;], [3;;], paper_rule; fallback=:classical, field=Float32);

julia> (eltype(C), only(C) == 6)
(Float32, true)
```

# Implementation

`A` and `B` can be Julia `AbstractMatrix` values, Nemo matrices, or other
containers with integer dimensions from `size(M)` and scalar entries from
`M[i, j]`. `axes(M)` supplies the index ranges and defaults to one-based
axes. Field inference uses `eltype(M)` and the entries.

A custom scheme supplies `NineFourths.execution_dimensions(scheme, max_side, max_rank)`, returning a positive `(side, rank)` pair within the limits or
`nothing`. `NineFourths.scheme_coefficient(scheme, term, leg, coordinate)`
supplies weights for one-based term and column-major block indices. Legs 1 and
2 address the input forms, and leg 3 addresses the output weights.
`NineFourths.block_side(scheme)` supplies the block side for diagnostics. The
Shpilka scheme can report a symbolic `WitnessSide`.
"""
function multiply(
    A,
    B,
    scheme;
    fallback=:error,
    field=nothing,
    max_coefficient_visits::Integer=DEFAULT_COEFFICIENT_VISITS,
    max_workspace_entries::Integer=DEFAULT_WORKSPACE_ENTRIES,
)
    fallback === :error ||
        fallback === :classical ||
        throw(ArgumentError("fallback must be :error or :classical"))
    max_coefficient_visits >= 0 ||
        throw(ArgumentError("max_coefficient_visits must be nonnegative"))
    max_workspace_entries >= 0 ||
        throw(ArgumentError("max_workspace_entries must be nonnegative"))
    shape = _multiplication_shape(A, B)
    m, _, n = shape
    if any(iszero, shape)
        _check_zero_workspace(shape, scheme, max_workspace_entries)
        inputs = _field_inputs(A, B, shape; field)
        return _zero_matrix(inputs.eltype, m, n, inputs.zero)
    end
    plan = _execution_plan(
        shape,
        scheme,
        max_coefficient_visits,
        max_workspace_entries;
        dimensions_for=_minimum_dimensions,
    )
    if plan isa ExecutionInfeasible
        fallback === :classical || throw(plan)
        _check_classical_workspace(shape, scheme, max_workspace_entries)
        inputs = _field_inputs(A, B, shape; field)
        return _classical_fallback(inputs)
    end
    inputs = _field_inputs(A, B, shape; field)
    try
        arithmetic = _scheme_arithmetic(scheme, inputs)
        adapted, domain = arithmetic.scheme, arithmetic.domain
        adapted_plan = if adapted === scheme && !(scheme isa LoweredScheme)
            plan
        else
            _execution_plan(shape, adapted, max_coefficient_visits, max_workspace_entries)
        end
        if adapted_plan isa ExecutionInfeasible
            fallback === :classical || throw(adapted_plan)
            return _classical_fallback(inputs)
        end
        result = _scheme_product(
            inputs.left,
            inputs.right,
            adapted,
            domain,
            inputs.zero,
            adapted_plan.side,
            adapted_plan.rank,
        )
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
