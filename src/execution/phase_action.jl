# Cyclotomic work values keep their weights in the input field. The phase keys
# have the same half-turn normalization as PhaseSum. Distinct keys may still
# satisfy cyclotomic relations, so the sparse zero test is conservative.
const _FieldPhaseTerms = Dict{Rational{BigInt},Any}

struct FieldPhaseSum
    terms::_FieldPhaseTerms
    zero_value
end

_field_iszero(value, zero_value) = value == zero_value
_field_iszero(value::FieldPhaseSum, zero_value) = isempty(value.terms)

function _add_field_phase!(terms, phase, weight, zero_value)
    phase = mod(phase, 1)
    if phase >= 1 // 2
        phase -= 1 // 2
        weight = zero_value - weight
    end
    if haskey(terms, phase)
        weight = terms[phase] + weight
    end
    if _field_iszero(weight, zero_value)
        delete!(terms, phase)
    else
        terms[phase] = weight
    end
    return nothing
end

function _finish_field_phases(terms, zero_value)
    isempty(terms) && return zero_value
    length(terms) == 1 && haskey(terms, 0) && return terms[0]
    return FieldPhaseSum(terms, zero_value)
end

function _field_phase_coefficient(
    embed, coefficient::PhaseSum, zero_value=embed(big(0) // 1)
)
    terms = _FieldPhaseTerms()
    for (phase, weight) in coefficient.terms
        _add_field_phase!(terms, phase, embed(weight), zero_value)
    end
    return _finish_field_phases(terms, zero_value)
end

_field_add(left, right) = left + right

function _field_add(left::FieldPhaseSum, right)
    terms = copy(left.terms)
    _add_field_phase!(terms, big(0) // 1, right, left.zero_value)
    return _finish_field_phases(terms, left.zero_value)
end

_field_add(left, right::FieldPhaseSum) = _field_add(right, left)

function _field_add(left::FieldPhaseSum, right::FieldPhaseSum)
    terms = copy(left.terms)
    for (phase, weight) in right.terms
        _add_field_phase!(terms, phase, weight, left.zero_value)
    end
    return _finish_field_phases(terms, left.zero_value)
end

_field_mul(left, right) = left * right

function _field_mul(left::FieldPhaseSum, right)
    _field_iszero(right, left.zero_value) && return left.zero_value
    terms = _FieldPhaseTerms()
    for (phase, weight) in left.terms
        _add_field_phase!(terms, phase, weight * right, left.zero_value)
    end
    return _finish_field_phases(terms, left.zero_value)
end

_field_mul(left, right::FieldPhaseSum) = _field_mul(right, left)

function _field_mul(left::FieldPhaseSum, right::FieldPhaseSum)
    terms = _FieldPhaseTerms()
    for (phase, weight) in left.terms, (other_phase, other_weight) in right.terms
        _add_field_phase!(
            terms, phase + other_phase, weight * other_weight, left.zero_value
        )
    end
    return _finish_field_phases(terms, left.zero_value)
end

_field_apply(coefficient, value) = _field_mul(coefficient, value)

function _squarefree_prime_factors(order)
    primes = BigInt[]
    for (prime, power) in Nemo.factor(Nemo.ZZ(order))
        power == 1 || return nothing
        push!(primes, BigInt(prime))
    end
    return primes
end

# Project onto the constant power-basis coefficient in the prime-power
# cyclotomic rings and tensor those projections across coprime orders.
# The projections agree when extending a prime-power order. A primitive
# p^a-th root has constant coefficient zero for a > 1. For a = 1, the
# coefficient is −1 for exponent p−1. The Chinese remainder theorem gives
# that exponent exactly when n ≡ −(d/p) mod p for a phase n/d.
function _constant_phase_sign(phase, factors)
    order = denominator(phase)
    order == 1 && return 1
    primes = get!(() -> _squarefree_prime_factors(order), factors, order)
    isnothing(primes) && return 0
    exponent = numerator(phase)
    all(prime -> iszero(mod(exponent + div(order, prime), prime)), primes) || return 0
    return isodd(length(primes)) ? -1 : 1
end

_project_field_value(value) = value

function _project_field_value(value::FieldPhaseSum)
    factors = Dict{BigInt,Union{Nothing,Vector{BigInt}}}()
    result = value.zero_value
    for (phase, weight) in value.terms
        sign = _constant_phase_sign(phase, factors)
        iszero(sign) && continue
        result = sign == 1 ? result + weight : result - weight
    end
    return result
end

# On a Julia complex field the formal fourth root acts as the native i.
# If f is the integer-linear projection above, f(z) + i*f(-i*z) commutes
# with multiplication by i and fixes the Gaussian scalars.
function _project_complex_value(value::FieldPhaseSum)
    factors = Dict{BigInt,Union{Nothing,Vector{BigInt}}}()
    result = value.zero_value
    for (phase, weight) in value.terms
        real_sign = _constant_phase_sign(phase, factors)
        if !iszero(real_sign)
            result = real_sign > 0 ? result + weight : result - weight
        end
        imag_sign = _constant_phase_sign(mod(phase - 1 // 4, 1), factors)
        if !iszero(imag_sign)
            rotated = complex(-imag(weight), real(weight))
            result = imag_sign > 0 ? result + rotated : result - rotated
        end
    end
    return result
end
