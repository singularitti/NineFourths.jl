"""
    CoefficientIncompatible(message)

A scheme coefficient cannot act in the requested scalar field.

The `message::String` describes the failed coefficient embedding or operation.
"""
struct CoefficientIncompatible <: Exception
    message::String
end

"""
    showerror(io::IO, error::CoefficientIncompatible)

Write the reason the coefficient cannot act in the selected field to `io`.
"""
Base.showerror(io::IO, error::CoefficientIncompatible) = print(io, error.message)

"""
    _BuiltinInteger

Built-in Julia integer types eligible for widened integer arithmetic.
"""
const _BuiltinInteger = Union{
    Bool,Int8,Int16,Int32,Int64,Int128,UInt8,UInt16,UInt32,UInt64,UInt128,BigInt
}

"""
    _BuiltinRational

Julia rational types whose numerators and denominators use built-in integers.
"""
const _BuiltinRational = Rational{T} where {T<:_BuiltinInteger}

"""
    _BuiltinExact

Union of the built-in integer and rational scalar types.
"""
const _BuiltinExact = Union{_BuiltinInteger,_BuiltinRational}

"""
    _NemoPrimeScalar

Union of Nemo's integer and rational scalar element types.
"""
const _NemoPrimeScalar = Union{Nemo.ZZRingElem,Nemo.QQFieldElem}

"""
    _FloatingScalar

Union of real and complex scalars with floating-point components.
"""
const _FloatingScalar = Union{AbstractFloat,Complex{<:AbstractFloat}}

"""
    _TypeBasedParent

AbstractAlgebra parents for Julia's type-based integer and rational domains.
"""
const _TypeBasedParent = Union{Nemo.AbstractAlgebra.Integers,Nemo.AbstractAlgebra.Rationals}

"""
    _field_integer(one_value, k::Integer)

Embed `k` by repeated doubling and addition of the target domain's `one_value`.
"""
function _field_integer(one_value, k::Integer)
    n = abs(BigInt(k))
    additive_identity = one_value - one_value
    value, multiple = additive_identity, one_value
    while !iszero(n)
        isodd(n) && (value += multiple)
        n >>= 1
        iszero(n) || (multiple += multiple)
    end
    return k < 0 ? additive_identity - value : value
end

"""
    _field_quotient(numerator, denominator)

Divide two embedded scalars in the same field by an invertible `denominator`.

Use native division for built-in rational, floating-point, and complex scalars.
For other scalars, try multiplication by the inverse before using division.
"""
function _field_quotient(numerator, denominator)
    if numerator isa Union{_BuiltinRational,AbstractFloat,Complex}
        return numerator / denominator
    end
    # A scalar subtype can inherit Julia's `/` even when that method would
    # leave its field. Prefer its native inverse to the inherited division.
    try
        return numerator * inv(denominator)
    catch error
        error isa MethodError || rethrow()
    end
    return numerator / denominator
end

"""
    _field_rational(one_value, value::Rational; coefficient=true)

Embed a finite rational using the target domain's scalar `one_value`.

Fractional scheme weights over `Nemo.ZZ` use `Nemo.QQ` work values. A failed
embedding raises `CoefficientIncompatible` for a scheme weight and `DomainError`
when `coefficient=false` identifies an input entry.
"""
function _field_rational(one_value, value::Rational; coefficient=true)
    den = denominator(value)
    if iszero(den)
        message = "matrix entries and coefficients must be finite"
        throw(coefficient ? CoefficientIncompatible(message) : DomainError(value, message))
    end
    one_value isa _FloatingScalar && return convert(typeof(one_value), value)
    if coefficient && den != 1 && one_value isa Nemo.ZZRingElem
        return Nemo.QQ(value)
    end
    num = _field_integer(one_value, numerator(value))
    den == 1 && return num
    one_value isa _BuiltinInteger && return BigInt(num) // BigInt(den)
    embedded_den = _field_integer(one_value, den)
    if embedded_den == one_value - one_value
        message = "rational denominator vanishes in the target field"
        throw(coefficient ? CoefficientIncompatible(message) : DomainError(value, message))
    end
    try
        return _field_quotient(num, embedded_den)
    catch error
        error isa Union{
            MethodError,
            InexactError,
            DomainError,
            DivideError,
            ArgumentError,
            Nemo.AbstractAlgebra.NotInvertibleError,
        } || rethrow()
        message = "rational denominator is not invertible in the target field"
        throw(coefficient ? CoefficientIncompatible(message) : DomainError(value, message))
    end
end

"""
    _field_unit_integer(one_value, n::Integer)

Test whether `n` remains nonzero when embedded using the field's `one_value`.
"""
function _field_unit_integer(one_value, n::Integer)
    return _field_integer(one_value, n) != one_value - one_value
end

"""
    _matrix_field(matrix)

Return the runtime scalar parent supplied by `matrix`, or `nothing` if absent.
"""
_matrix_field(matrix) = nothing

"""
    _matrix_field(matrix::Union{Nemo.MatElem,Nemo.MatRingElem})

Return the matrix's `Nemo.base_ring` unless it represents a type-based Julia parent.
"""
function _matrix_field(matrix::Union{Nemo.MatElem,Nemo.MatRingElem})
    domain = Nemo.base_ring(matrix)
    return domain isa _TypeBasedParent ? nothing : domain
end

"""
    _scalar_field(value)

Return the runtime scalar parent reported by `parent(value)`, if available.

Return `nothing` for native exact, floating-point, and complex scalars and
when `parent` supplies no runtime domain object.
"""
function _scalar_field(value)
    value isa Union{_BuiltinExact,AbstractFloat,Complex} && return nothing
    applicable(parent, value) || return nothing
    domain = parent(value)
    return domain === value || domain isa Union{Type,_TypeBasedParent} ? nothing : domain
end

"""
    _common_field(a, b)

Resolve compatible runtime parents `a` and `b`, with `nothing` indicating absence.

Identical parents stay unchanged. Nemo's integer and rational parents can
yield to the other parent. Other distinct parents raise `ArgumentError`.
"""
function _common_field(a, b)
    isnothing(a) && return b
    isnothing(b) && return a
    a === b && return a
    a === Nemo.ZZ && return b
    b === Nemo.ZZ && return a
    a === Nemo.QQ && return b
    b === Nemo.QQ && return a
    return throw(ArgumentError("matrix entries belong to different field parents"))
end

"""
    _is_nemo_prime_domain(domain)

Test whether `domain` is the runtime parent `Nemo.ZZ` or `Nemo.QQ`.
"""
_is_nemo_prime_domain(domain) = domain === Nemo.ZZ || domain === Nemo.QQ

"""
    _requested_field(source, target)

Validate an explicit `target` parent against the inferred `source` parent.

Accept the requested parent when the source is absent, identical to `target`,
or Nemo's integer or rational parent. Throw `ArgumentError` for a conflict.
"""
function _requested_field(source, target)
    if isnothing(source) || source === target || _is_nemo_prime_domain(source)
        return target
    end
    return throw(ArgumentError("matrix entries belong to a different parent than the requested field"),)
end

"""
    _prime_scalar(value::Nemo.ZZRingElem)::BigInt
    _prime_scalar(value::Nemo.QQFieldElem)::Rational{BigInt}

Convert a Nemo integer or rational scalar to its exact Julia equivalent.
"""
_prime_scalar(value::Nemo.ZZRingElem) = BigInt(value)
_prime_scalar(value::Nemo.QQFieldElem) = rational_result(value)

"""
    _field_metadata(A, B)

Collect the scalar metadata needed to infer a shared domain for `A` and `B`.

Return the runtime `domain`, the promoted `scalar_type`, a representative
`sample`, and Boolean flags for built-in exact, rational, and fractional entries.
An absent domain or sample is recorded as `nothing`. Inputs follow the matrix
interface of [`multiply`](@ref).
"""
function _field_metadata(A, B)
    domain = _common_field(_matrix_field(A), _matrix_field(B))
    scalar_type = Union{}
    sample = nothing
    rational_entries = false
    fractional_entries = false
    exact_entries = false
    for matrix in (A, B)
        declared = eltype(matrix)
        rational_entries |= declared <: _BuiltinRational && declared !== Union{}
        exact_entries |= declared <: _BuiltinExact && declared !== Union{}
        if any(iszero, size(matrix))
            if declared === Nemo.ZZRingElem
                domain = _common_field(domain, Nemo.ZZ)
            elseif declared === Nemo.QQFieldElem
                domain = _common_field(domain, Nemo.QQ)
            elseif isconcretetype(declared) && !(declared <: _BuiltinExact)
                scalar_type = promote_type(scalar_type, declared)
            end
            continue
        end
        rows, columns = axes(matrix)
        for j in columns, i in rows
            value = matrix[i, j]
            if value isa _BuiltinExact
                exact_entries = true
                if value isa _BuiltinRational
                    rational_entries = true
                    den = denominator(value)
                    iszero(den) &&
                        throw(DomainError(value, "matrix entries must be finite"))
                    fractional_entries |= den != 1
                end
            else
                domain = _common_field(domain, _scalar_field(value))
                if !(value isa _NemoPrimeScalar)
                    scalar_type = promote_type(scalar_type, typeof(value))
                    typeof(value) === scalar_type && (sample = value)
                end
            end
        end
    end
    return (;
        domain, scalar_type, sample, rational_entries, fractional_entries, exact_entries
    )
end

"""
    _optional_identity(operation, reference)

Obtain `zero` or `one` from a scalar, scalar type, or field parent when available.

Return `nothing` when the reference or identity method is unavailable.
"""
function _optional_identity(operation, reference)
    (isnothing(reference) || reference === Union{}) && return nothing
    try
        return operation(reference)
    catch error
        error isa MethodError || rethrow()
        return nothing
    end
end

"""
    _callable_field(reference)

Test whether `reference` accepts both `Int` literals `0` and `1` as arguments.
"""
_callable_field(reference) = applicable(reference, 0) && applicable(reference, 1)

"""
    _field_identities(reference, callable) -> (zero_value, one_value)

Find the additive and multiplicative identities of the selected scalar domain.

With `callable=true`, call `reference(0)` and `reference(1)`. Otherwise use
`zero` and `one` on the reference. When only `one` is available, obtain zero
by subtraction. An unavailable identity is reported as `nothing`.
"""
function _field_identities(reference, callable)
    if callable
        return reference(0), reference(1)
    end
    zero_value = _optional_identity(zero, reference)
    one_value = _optional_identity(one, reference)
    if isnothing(zero_value) && !isnothing(one_value)
        zero_value = one_value - one_value
    end
    return zero_value, one_value
end

"""
    _field_configuration(metadata, field)

Choose the execution domain from `_field_metadata` and an optional field reference.

Return a named tuple with `zero`, `one`, the output `eltype`, the runtime
`parent` and scalar `converter` when available, and a `legacy` flag for inferred
built-in exact scalars. The `field` reference may be a parent, scalar type, or
representative element.
"""
function _field_configuration(metadata, field)
    domain, scalar_type, sample = metadata.domain, metadata.scalar_type, metadata.sample
    if isnothing(field) && domain === Nemo.ZZ && metadata.fractional_entries
        domain = Nemo.QQ
    end
    legacy = false
    converter = nothing
    if !isnothing(field)
        if field isa Type
            reference = sample isa field ? sample : field
            converter = field
            callable = false
        elseif _callable_field(field)
            reference = converter = field
            callable = true
        else
            prototype_parent = _scalar_field(field)
            reference = isnothing(prototype_parent) ? field : prototype_parent
            converter = prototype_parent
            callable = _callable_field(prototype_parent)
        end
    elseif !isnothing(domain) && (!_is_nemo_prime_domain(domain) || scalar_type === Union{})
        reference = converter = domain
        callable = _callable_field(domain)
    elseif scalar_type === Union{} && metadata.exact_entries
        reference = metadata.rational_entries ? Rational{BigInt} : BigInt
        callable = false
        legacy = true
    else
        reference = typeof(sample) === scalar_type ? sample : scalar_type
        callable = false
        domain = nothing
    end
    zero_value, one_value = _field_identities(reference, callable)
    if field isa Type
        if isnothing(zero_value) && !isnothing(domain)
            parent_zero, parent_one = _field_identities(domain, _callable_field(domain))
            if parent_zero isa field
                zero_value, one_value = parent_zero, parent_one
                converter = domain
            end
        end
        domain = _requested_field(domain, _scalar_field(zero_value))
    elseif !isnothing(field) && _callable_field(field)
        parent_of_zero = _scalar_field(zero_value)
        domain = _requested_field(
            domain, isnothing(parent_of_zero) ? field : parent_of_zero
        )
    elseif !isnothing(field)
        domain = _requested_field(domain, _scalar_field(zero_value))
    end
    if !isnothing(zero_value)
        output_type = typeof(zero_value)
    elseif reference isa Type && reference !== Union{}
        output_type = reference
    elseif scalar_type !== Union{}
        output_type = scalar_type
    else
        output_type = Any
    end
    return (;
        zero=zero_value, one=one_value, eltype=output_type, parent=domain, legacy, converter
    )
end

"""
    _field_entry(options, value)

Convert an input entry to the scalar representation selected by `_field_configuration`.
"""
function _field_entry(options, value)
    T = options.eltype
    value isa T && return value
    value isa _NemoPrimeScalar && (value = _prime_scalar(value))
    if value isa _BuiltinExact
        if T <: Union{_BuiltinExact,AbstractFloat,Complex}
            return convert(T, value)
        end
        return if value isa _BuiltinInteger
            _field_integer(options.one, value)
        else
            _field_rational(options.one, value; coefficient=false)
        end
    end
    if !isnothing(options.converter) && applicable(options.converter, value)
        return options.converter(value)
    end
    return convert(T, value)
end

"""
    _field_embed_native(options, value)

Embed a scalar scheme weight using the domain selected by `_field_configuration`.

Throw `CoefficientIncompatible` if the coefficient cannot act in that domain.
"""
function _field_embed_native(options, value)
    value isa _NemoPrimeScalar && (value = _prime_scalar(value))
    if value isa _BuiltinInteger
        return _field_integer(options.one, value)
    elseif value isa _BuiltinRational
        return _field_rational(options.one, value)
    end
    domain = _scalar_field(value)
    if !isnothing(domain) && domain !== options.parent
        throw(CoefficientIncompatible("scheme coefficient belongs to a different field parent"),)
    end
    try
        return _field_entry(options, value)
    catch error
        error isa Union{MethodError,InexactError,DomainError,ArgumentError} || rethrow()
        throw(CoefficientIncompatible("scheme coefficient cannot embed in the input field"))
    end
end

"""
    _copy_field_matrix(convert_entry, matrix, T::Type)::Matrix{T}

Read a matrix-like input in axis order into a one-based matrix of element type `T`.

Apply the unary `convert_entry` callback to each scalar before storing it.
"""
function _copy_field_matrix(convert_entry, matrix, ::Type{T}) where {T}
    result = Matrix{T}(undef, size(matrix)...)
    rows, columns = axes(matrix)
    for (j, column) in enumerate(columns), (i, row) in enumerate(rows)
        try
            result[i, j] = convert_entry(matrix[row, column])
        catch error
            error isa Union{MethodError,InexactError,DivideError} || rethrow()
            throw(ArgumentError("matrix entry cannot embed in the input field"))
        end
    end
    return result
end

"""
    _legacy_matrix(matrix)

Normalize an integer or rational input to one-based axes and preserve its scalar type.

Reuse `matrix` when it is already a one-based `AbstractMatrix`.
"""
function _legacy_matrix(matrix)
    if matrix isa AbstractMatrix && !Base.has_offset_axes(matrix)
        return matrix
    end
    return _copy_field_matrix(identity, matrix, eltype(matrix))
end

"""
    _multiplication_shape(A, B) -> (m, k, n)

Validate the dimensions of the matrix-like factors of an `m×k` by `k×n` product.

Throw `DimensionMismatch` when the inner dimensions differ.
"""
function _multiplication_shape(A, B)
    m, k = _matrix_size(A)
    right_rows, n = _matrix_size(B)
    k == right_rows || throw(DimensionMismatch("input inner dimensions must match"))
    return (m, k, n)
end

"""
    _field_inputs(A, B, shape=_multiplication_shape(A, B); field=nothing)

Prepare the inputs and shared scalar configuration for matrix multiplication.

Return `_field_configuration`'s named tuple with one-based `left` and `right`
matrices when all dimensions in `shape` are positive. A zero dimension sets
both matrices to `nothing`. `A` and `B` follow the interface of [`multiply`](@ref).
"""
function _field_inputs(A, B, shape=_multiplication_shape(A, B); field=nothing)
    m, k, n = shape
    options = _field_configuration(_field_metadata(A, B), field)
    if (m > 0 && n > 0) && isnothing(options.zero)
        throw(ArgumentError("cannot determine the additive identity of the input field; supply field"),)
    end
    if iszero(m) || iszero(k) || iszero(n)
        return (; left=nothing, right=nothing, options...)
    end
    isnothing(options.one) &&
        throw(ArgumentError("cannot determine the multiplicative identity of the input field; supply field",),)
    if options.legacy
        return (; left=_legacy_matrix(A), right=_legacy_matrix(B), options...)
    end
    # Convert one scalar matrix entry using the selected field configuration.
    convert_entry(value) = _field_entry(options, value)
    T = options.eltype
    return (;
        left=_copy_field_matrix(convert_entry, A, T),
        right=_copy_field_matrix(convert_entry, B, T),
        options...,
    )
end
