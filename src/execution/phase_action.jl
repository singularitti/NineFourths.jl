# Cyclotomic work values keep their weights in the input field. The phase keys
# have the same half-turn normalization as PhaseSum. Distinct keys may still
# satisfy cyclotomic relations, so the sparse zero test is conservative.
const _FieldPhaseTerms = Dict{Rational{BigInt},Any}

# Store rational phase keys and scalar weights with their field's additive identity.
struct FieldPhaseSum
    terms::_FieldPhaseTerms
    zero_value
end

# Test a field scalar or FieldPhaseSum against the field's scalar zero.
_field_iszero(value, zero_value) = value == zero_value
_field_iszero(value::FieldPhaseSum, zero_value) = isempty(value.terms)

# Add a rational phase and its scalar weight to a _FieldPhaseTerms dictionary.
# The zero_value is the additive identity of the weight's field.
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

# Collapse _FieldPhaseTerms with only a constant term to a scalar. Use the
# supplied scalar zero for no terms and a FieldPhaseSum for other maps.
function _finish_field_phases(terms, zero_value)
    isempty(terms) && return zero_value
    length(terms) == 1 && haskey(terms, 0) && return terms[0]
    return FieldPhaseSum(terms, zero_value)
end

# coefficient.terms yields (phase, weight) pairs as in a PhaseSum. The embed
# callback maps each Rational{BigInt} weight to a scalar in the target field,
# whose additive identity is zero_value.
function _field_phase_coefficient(embed, coefficient, zero_value=embed(big(0) // 1))
    terms = _FieldPhaseTerms()
    for (phase, weight) in coefficient.terms
        _add_field_phase!(terms, phase, embed(weight), zero_value)
    end
    return _finish_field_phases(terms, zero_value)
end

# Add two work values, each a scalar or FieldPhaseSum over the same field.
_field_add(left, right) = left + right

# A scalar right operand contributes a weight at phase zero.
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

# Multiply two work values, each a scalar or FieldPhaseSum over the same field.
_field_mul(left, right) = left * right

# A scalar right operand multiplies each phase weight.
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

# Apply a work coefficient to a work value, both scalars or FieldPhaseSum objects.
_field_apply(coefficient, value) = _field_mul(coefficient, value)

# Factor a positive integer order. Return its BigInt prime divisors if the
# order is squarefree, or nothing if a prime factor occurs more than once.
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
# The phase is Rational{BigInt}. The factors cache maps BigInt orders to
# Vector{BigInt} prime factors or nothing. Return an Int sign in -1:1.
function _constant_phase_sign(phase, factors)
    order = denominator(phase)
    order == 1 && return 1
    primes = get!(() -> _squarefree_prime_factors(order), factors, order)
    isnothing(primes) && return 0
    exponent = numerator(phase)
    all(prime -> iszero(mod(exponent + div(order, prime), prime)), primes) || return 0
    return isodd(length(primes)) ? -1 : 1
end

# Return a scalar unchanged or project a FieldPhaseSum to a scalar of its field.
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
# value supplies rational phase keys, weights, and a zero_value as in a
# FieldPhaseSum over Complex scalars. The projection returns a Complex scalar.
function _project_complex_value(value)
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
