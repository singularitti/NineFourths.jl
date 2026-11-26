# Allocate a Matrix{T} of nonnegative integer dimensions m×n. zero_value is
# an additive identity convertible to T, or nothing for an empty result.
function _zero_matrix(::Type{T}, m, n, zero_value) where {T}
    C = Matrix{T}(undef, m, n)
    isempty(C) && return C
    isnothing(zero_value) &&
        throw(ArgumentError("the output needs a zero in the input field"))
    return fill!(C, zero_value)
end

# A and B are one-based m×k and k×n matrices. The result is a Matrix{T}
# initialized with the scalar zero_value. The add and product callbacks each
# take two entries and return a scalar or a FieldPhaseSum work value.
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

# Accumulate an input linear form from the one-based source matrix into a
# Matrix{Any} of child-block size. The domain is from _field_inputs. The term
# and leg select an input form (leg 1 or 2), side is the scheme's block-grid side,
# and the active dimensions count block rows and columns containing entries.
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

# Accumulate a child product Matrix{Any} into the parent output C::Matrix{Any}.
# The domain is from _field_inputs. The integer term selects an output weight,
# side is the block-grid side, and the active dimensions count output blocks.
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

# A and B are one-based matrices of field scalars or FieldPhaseSum work values.
# The domain is from _field_inputs and zero_value is its additive identity.
# The integers side and rank give the scheme's block-grid side and term count.
# Child input forms and the returned product use Matrix{Any} for work values.
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

# Multiply built-in integer or rational scalars after widening the left factor.
_wide_product(a, b) = big(a) * b

# Use the one-based matrices and scalar zero from _field_inputs. Its legacy
# flag selects widened integer or rational arithmetic for inferred exact inputs.
function _classical_fallback(inputs)
    product = inputs.legacy ? _wide_product : (*)
    return _classical_product(
        inputs.left, inputs.right, inputs.zero, inputs.eltype, +, product
    )
end

"""
    multiply(A, B, scheme; fallback=:error, field=nothing,
             max_coefficient_visits=10_000_000, max_workspace_entries=10_000_000)

Multiply an `m×k` matrix by a `k×n` matrix and return a dense Julia `Matrix`.
`A` and `B` can be Julia `AbstractMatrix` values, Nemo matrices, or other
containers that supply integer dimensions through `size(M)` and scalar entries
through `M[i, j]`. The size is typically a `Tuple{Int,Int}`. The index ranges
come from `axes(M)`, which defaults to one-based indices on each axis. The
executor uses `eltype(M)` and the entries to infer the input field.

The package's constructors return a `BilinearScheme`. A custom scheme can
implement `NineFourths.execution_dimensions(scheme, max_side, max_rank)`,
returning a positive integer pair `(side, rank)` within the limits or
`nothing`. `NineFourths.scheme_coefficient(scheme, term, leg, coordinate)`
supplies each scalar weight for one-based integer term and block coordinate
indices. Legs 1 and 2 denote the input forms and leg 3 denotes the output
weights. `NineFourths.block_side(scheme)` supplies the block side used in
diagnostics. Package schemes can represent that side as a symbolic `WitnessSide`.

With the default `field=nothing`, built-in Julia integer inputs produce
`Matrix{BigInt}` and their rational counterparts produce `Matrix{Rational{BigInt}}`.
Other inputs use their common scalar field. To supply the field explicitly,
pass a parent callable as `field(0)` and `field(1)`, a scalar type with
identities, or a representative element.

For positive dimensions the default requires at least one bilinear scheme
layer. The product uses implicit zero padding along each axis and conventional
multiplication at the leaves. The `fallback` keyword accepts either the default
`:error` or `:classical`, which permits a conventional product when the requested
scheme cannot execute in the input field or budgets. A zero dimension determines
an empty or zero result directly.

Both budgets are nonnegative integers. The visit budget bounds the coefficient
visits across the recursive product. The workspace budget bounds live dense
matrix entries, including normalized inputs and the result. The workspace budget
also applies to classical fallback.
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
