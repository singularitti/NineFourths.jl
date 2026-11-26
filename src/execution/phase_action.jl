"""
    _FieldPhaseTerms

Dictionary from normalized `Rational{BigInt}` phases to weights in the
working scalar domain. Phases use the half-turn convention of [`PhaseSum`](@ref).
"""
const _FieldPhaseTerms = Dict{Rational{BigInt},Any}

"""
    FieldPhaseSum(terms, zero_value)

Store a normalized phase dictionary and the additive identity of its working
scalar domain. This representation keeps arithmetic on the weights in that
domain while formal roots of unity supply the phases. Distinct phases can
still satisfy cyclotomic relations.
"""
struct FieldPhaseSum
    terms::_FieldPhaseTerms
    zero_value
end

_field_iszero(value, zero_value) = value == zero_value
_field_iszero(value::FieldPhaseSum, zero_value) = isempty(value.terms)

"""
    _field_iszero(value, zero_value)::Bool

Compare a scalar with its field's additive identity. For a [`FieldPhaseSum`](@ref),
test whether its dictionary is empty. A nonempty dictionary can still vanish
through cancellation between different phases.
"""
_field_iszero

"""
    _add_field_phase!(terms, phase, weight, zero_value)

Add a `weight` to a mutable [`_FieldPhaseTerms`](@ref) dictionary. Normalize
the rational phase to `[0, 1/2)` and adjust the weight's sign before adding.
Remove a term when its weight equals the field's `zero_value`. Return `nothing`.
"""
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

"""
    _finish_field_phases(terms, zero_value)

Finish a normalized phase sum. Return the supplied zero for an empty
dictionary, the scalar weight for a lone constant term, or a
[`FieldPhaseSum`](@ref) for other dictionaries.
"""
function _finish_field_phases(terms, zero_value)
    isempty(terms) && return zero_value
    length(terms) == 1 && haskey(terms, 0) && return terms[0]
    return FieldPhaseSum(terms, zero_value)
end

"""
    _field_phase_coefficient(embed, coefficient, zero_value=embed(big(0) // 1))

Embed a [`PhaseSum`](@ref) coefficient's `Rational{BigInt}` weights using
the callable `embed`. Keep the original phases and drop terms whose embedded
weights equal `zero_value`. The result is a working scalar or a
[`FieldPhaseSum`](@ref).
"""
function _field_phase_coefficient(embed, coefficient, zero_value=embed(big(0) // 1))
    terms = _FieldPhaseTerms()
    for (phase, weight) in coefficient.terms
        _add_field_phase!(terms, phase, embed(weight), zero_value)
    end
    return _finish_field_phases(terms, zero_value)
end

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

"""
    _field_add(left, right)

Add two working values in the same scalar domain. Scalars add directly.
When either operand is a [`FieldPhaseSum`](@ref), treat each scalar as a
constant term and combine weights at equal phases.
"""
_field_add

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

"""
    _field_mul(left, right)

Multiply two working values in the same scalar domain. Scalars multiply
directly, a scalar with a [`FieldPhaseSum`](@ref) scales each phase weight,
and two phase sums combine all phase pairs by addition of phases and
multiplication of weights.
"""
_field_mul

"""
    _field_apply(coefficient, value)

Apply a scalar or symbolic scheme coefficient to a working value using
[`_field_mul`](@ref). Both operands use the same working scalar domain.
"""
_field_apply(coefficient, value) = _field_mul(coefficient, value)

"""
    _squarefree_prime_factors(order)

Factor a positive integer `order` with Nemo. Return its prime divisors as a
`Vector{BigInt}` when it is squarefree, or `nothing` when a factor repeats.
The order one has an empty factor list.
"""
function _squarefree_prime_factors(order)
    primes = BigInt[]
    for (prime, power) in Nemo.factor(Nemo.ZZ(order))
        power == 1 || return nothing
        push!(primes, BigInt(prime))
    end
    return primes
end

"""
    _constant_phase_sign(phase, factors)::Int

Return the coefficient in `-1:1` obtained by projecting
`exp(2πim * phase)` onto the constant term. Tensor the power-basis
projections of the prime-power cyclotomic rings for the reduced denominator
of `phase`. The `factors` cache maps `BigInt` root orders to the results of
[`_squarefree_prime_factors`](@ref).

A primitive root of order `p^k` has constant coefficient zero for `k > 1`.
For `k = 1`, the coefficient is `-1` at exponent `p - 1`. For a phase `n/d`,
the Chinese remainder theorem gives that exponent precisely when
`n ≡ -(d ÷ p) mod p`.
"""
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

"""
    _project_field_value(value)

Return an ordinary working scalar unchanged. For a [`FieldPhaseSum`](@ref),
apply the integer-linear constant-term projection and return its scalar
value. This projection fixes scalar terms and selects a component from a
general symbolic sum.
"""
_project_field_value

"""
    _project_complex_value(value)

Project a [`FieldPhaseSum`](@ref) with Julia `Complex` weights into its
complex scalar domain. Here the formal fourth root acts as the native
imaginary unit. If `f` is the constant-term projection, `f(z) + im*f(-im*z)`
commutes with multiplication by `im` and fixes Gaussian scalars.
"""
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
