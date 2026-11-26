"""An explicit rule has a coefficient that cannot act in the requested scalar field."""
struct CoefficientIncompatible <: Exception
    message::String
end
Base.showerror(io::IO, error::CoefficientIncompatible) = print(io, error.message)

const FieldMatrix = Union{AbstractMatrix,Nemo.MatElem,Nemo.MatRingElem}
const _BuiltinInteger = Union{
    Bool,Int8,Int16,Int32,Int64,Int128,UInt8,UInt16,UInt32,UInt64,UInt128,BigInt
}
const _BuiltinRational = Rational{T} where {T<:_BuiltinInteger}
const _BuiltinExact = Union{_BuiltinInteger,_BuiltinRational}
const _NemoPrimeScalar = Union{Nemo.ZZRingElem,Nemo.QQFieldElem}
const _FloatingScalar = Union{AbstractFloat,Complex{<:AbstractFloat}}
const _TypeBasedParent = Union{Nemo.AbstractAlgebra.Integers,Nemo.AbstractAlgebra.Rationals}

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
            MethodError,InexactError,DomainError,DivideError,ArgumentError,
            Nemo.AbstractAlgebra.NotInvertibleError
        } || rethrow()
        message = "rational denominator is not invertible in the target field"
        throw(coefficient ? CoefficientIncompatible(message) : DomainError(value, message))
    end
end

function _field_unit_integer(one_value, n::Integer)
    return _field_integer(one_value, n) != one_value - one_value
end

_matrix_field(::AbstractMatrix) = nothing
function _matrix_field(matrix::Union{Nemo.MatElem,Nemo.MatRingElem})
    domain = Nemo.base_ring(matrix)
    return domain isa _TypeBasedParent ? nothing : domain
end

function _scalar_field(value)
    value isa Union{_BuiltinExact,AbstractFloat,Complex} && return nothing
    applicable(parent, value) || return nothing
    domain = parent(value)
    return domain === value || domain isa Union{Type,_TypeBasedParent} ? nothing : domain
end

function _common_field(a, b)
    isnothing(a) && return b
    isnothing(b) && return a
    a === b && return a
    a === Nemo.ZZ && return b
    b === Nemo.ZZ && return a
    a === Nemo.QQ && return b
    b === Nemo.QQ && return a
    throw(ArgumentError("matrix entries belong to different field parents"))
end

_is_nemo_prime_domain(domain) = domain === Nemo.ZZ || domain === Nemo.QQ

function _requested_field(source, target)
    if isnothing(source) || source === target || _is_nemo_prime_domain(source)
        return target
    end
    throw(ArgumentError("matrix entries belong to a different parent than the requested field"))
end

_prime_scalar(value::Nemo.ZZRingElem) = BigInt(value)
_prime_scalar(value::Nemo.QQFieldElem) = rational_result(value)

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
        if isempty(matrix)
            if declared === Nemo.ZZRingElem
                domain = _common_field(domain, Nemo.ZZ)
            elseif declared === Nemo.QQFieldElem
                domain = _common_field(domain, Nemo.QQ)
            elseif isconcretetype(declared) && !(declared <: _BuiltinExact)
                scalar_type = promote_type(scalar_type, declared)
            end
            continue
        end
        for j in axes(matrix, 2), i in axes(matrix, 1)
            value = matrix[i, j]
            if value isa _BuiltinExact
                exact_entries = true
                if value isa _BuiltinRational
                    rational_entries = true
                    den = denominator(value)
                    iszero(den) && throw(DomainError(value, "matrix entries must be finite"))
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
    return (; domain, scalar_type, sample, rational_entries, fractional_entries, exact_entries)
end

function _optional_identity(operation, reference)
    (isnothing(reference) || reference === Union{}) && return nothing
    try
        return operation(reference)
    catch error
        error isa MethodError || rethrow()
        return nothing
    end
end

_callable_field(reference) = applicable(reference, 0) && applicable(reference, 1)

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
        domain = _requested_field(domain, isnothing(parent_of_zero) ? field : parent_of_zero)
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
    return (; zero=zero_value, one=one_value, eltype=output_type, parent=domain, legacy, converter)
end

function _field_entry(options, value)
    T = options.eltype
    value isa T && return value
    value isa _NemoPrimeScalar && (value = _prime_scalar(value))
    if value isa _BuiltinExact
        if T <: Union{_BuiltinExact,AbstractFloat,Complex}
            return convert(T, value)
        end
        return value isa _BuiltinInteger ? _field_integer(options.one, value) :
               _field_rational(options.one, value; coefficient=false)
    end
    if !isnothing(options.converter) && applicable(options.converter, value)
        return options.converter(value)
    end
    return convert(T, value)
end

function _field_embed_native(options, value)
    value isa _NemoPrimeScalar && (value = _prime_scalar(value))
    if value isa _BuiltinInteger
        return _field_integer(options.one, value)
    elseif value isa _BuiltinRational
        return _field_rational(options.one, value)
    end
    domain = _scalar_field(value)
    if !isnothing(domain) && domain !== options.parent
        throw(CoefficientIncompatible("scheme coefficient belongs to a different field parent"))
    end
    try
        return _field_entry(options, value)
    catch error
        error isa Union{MethodError,InexactError,DomainError,ArgumentError} || rethrow()
        throw(CoefficientIncompatible("scheme coefficient cannot embed in the input field"))
    end
end

function _copy_field_matrix(convert_entry, matrix, ::Type{T}) where {T}
    result = Matrix{T}(undef, size(matrix)...)
    for (j, column) in enumerate(axes(matrix, 2)), (i, row) in enumerate(axes(matrix, 1))
        try
            result[i, j] = convert_entry(matrix[row, column])
        catch error
            error isa Union{MethodError,InexactError,DivideError} || rethrow()
            throw(ArgumentError("matrix entry cannot embed in the input field"))
        end
    end
    return result
end

function _legacy_matrix(matrix)
    if matrix isa AbstractMatrix && !Base.has_offset_axes(matrix)
        return matrix
    end
    return _copy_field_matrix(identity, matrix, eltype(matrix))
end

# `field` may be an element prototype, a concrete scalar type with identities,
# or a parent callable as `field(0)` and `field(1)`.
function _field_inputs(A::FieldMatrix, B::FieldMatrix; field=nothing)
    m, k = size(A)
    inner, n = size(B)
    k == inner || throw(DimensionMismatch("matrix inner dimensions must agree"))
    options = _field_configuration(_field_metadata(A, B), field)
    if (m > 0 && n > 0) && isnothing(options.zero)
        throw(ArgumentError("cannot determine the additive identity of the input field; supply field"))
    end
    if iszero(m) || iszero(k) || iszero(n)
        return (; left=nothing, right=nothing, options...)
    end
    isnothing(options.one) &&
        throw(ArgumentError("cannot determine the multiplicative identity of the input field; supply field"))
    if options.legacy
        return (; left=_legacy_matrix(A), right=_legacy_matrix(B), options...)
    end
    convert_entry(value) = _field_entry(options, value)
    T = options.eltype
    return (; left=_copy_field_matrix(convert_entry, A, T),
            right=_copy_field_matrix(convert_entry, B, T), options...)
end
