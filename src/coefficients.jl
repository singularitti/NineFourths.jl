# The Nemo field parent for exact algebraic scalars of type Nemo.QQBarFieldElem.
const ALGEBRAIC_NUMBERS = Nemo.algebraic_closure(Nemo.QQ)
const JuliaRational = Union{Integer,Rational}

# A key is a phase in whole turns and its value is the rational weight of
# exp(2πim * phase). Both are Rational{BigInt}. Normalized keys lie in [0, 1/2),
# with the sign absorbed into the weight.
struct PhaseSum
    terms::Dict{Rational{BigInt},Rational{BigInt}}
end

const ExactScalar = Union{Rational{BigInt},PhaseSum,Nemo.QQBarFieldElem}

# Normalize integers and rationals to Rational{BigInt}. Symbolic and QQBar
# coefficients retain their exact representations.
to_exact(value::Union{Integer,Nemo.ZZRingElem}) = BigInt(value) // 1
to_exact(value::Rational) = Rational{BigInt}(value)
to_exact(value::Union{PhaseSum,Nemo.QQBarFieldElem}) = value

# Extract a Rational{BigInt} from a rational coefficient. For an algebraic
# coefficient, require the value to be rational.
rational_result(value::Union{JuliaRational,Nemo.ZZRingElem}) = to_exact(value)

function rational_result(value::Nemo.QQFieldElem)
    return BigInt(numerator(value)) // BigInt(denominator(value))
end

to_exact(value::Nemo.QQFieldElem) = rational_result(value)

function rational_result(value::Nemo.QQBarFieldElem)
    Nemo.is_rational(value) || throw(DomainError(value, "expected a rational result"))
    return rational_result(Nemo.QQFieldElem(value))
end

# `terms` is a mutable phase-to-weight dictionary with the same key and value
# types as PhaseSum.terms. `phase` and `weight` are exact rationals, typically
# Rational{BigInt}. Normalize the phase before adding the signed weight.
function add_phase!(terms, phase, weight)
    phase = mod(phase, 1)
    if phase >= 1//2
        phase -= 1//2
        weight = -weight
    end
    coefficient = get(terms, phase, zero(Rational{BigInt})) + weight
    if iszero(coefficient)
        delete!(terms, phase)
    else
        terms[phase] = coefficient
    end
    return nothing
end

# `terms` holds normalized phases and weights as in PhaseSum.terms. Return a
# Rational{BigInt} when the only possible nonzero term has phase zero.
function finish_phases(terms)
    if length(terms) <= 1 && all(iszero, keys(terms))
        return get(terms, 0, zero(Rational{BigInt}))
    end
    return PhaseSum(terms)
end

# `phase` and `weight` are exact rationals, typically Rational{BigInt}, for the
# single term weight * exp(2πim * phase).
function phase_monomial(phase, weight)
    terms = Dict{Rational{BigInt},Rational{BigInt}}()
    add_phase!(terms, phase, weight)
    return finish_phases(terms)
end

"""
Return `exp(2πim * exponent / order)` for a positive `Integer` order and an
`Integer` exponent. A rational root is represented as a `Rational{BigInt}`.
Other roots are represented as a `PhaseSum`.
"""
function root_of_unity(order::Integer, exponent::Integer=1)
    order > 0 || throw(ArgumentError("root of unity order must be positive"))
    return phase_monomial(BigInt(exponent) // BigInt(order), to_exact(1))
end

# Yield `(phase, weight)` pairs with Rational{BigInt} components. A rational
# value contributes a single term with phase zero.
phase_terms(value::PhaseSum) = value.terms
phase_terms(value::JuliaRational) = ((zero(Rational{BigInt}), to_exact(value)),)

"""
Add the terms yielded by `phase_terms(right)` to a copy of `left.terms`.
The left operand is usually a `PhaseSum` with a mutable phase-to-weight
dictionary. The right operand is a `PhaseSum`, `Integer`, or `Rational`.
"""
function add_phases(left, right)
    terms = copy(left.terms)
    for (phase, weight) in phase_terms(right)
        add_phase!(terms, phase, weight)
    end
    return finish_phases(terms)
end

Base.:+(left::PhaseSum, right::Union{PhaseSum,JuliaRational}) = add_phases(left, right)
Base.:+(left::JuliaRational, right::PhaseSum) = right + left

function Base.:*(left::PhaseSum, right::PhaseSum)
    terms = Dict{Rational{BigInt},Rational{BigInt}}()
    for (phase, weight) in left.terms, (other_phase, other_weight) in right.terms
        add_phase!(terms, phase + other_phase, weight * other_weight)
    end
    return finish_phases(terms)
end

function Base.:*(left::PhaseSum, right::JuliaRational)
    iszero(right) && return zero(Rational{BigInt})
    factor = to_exact(right)
    return PhaseSum(Dict(phase => weight * factor for (phase, weight) in left.terms))
end

Base.:*(left::JuliaRational, right::PhaseSum) = right * left
Base.:/(left::PhaseSum, right::JuliaRational) = left * inv(to_exact(right))
Base.:-(value::PhaseSum) = value * -1
Base.:-(left::PhaseSum, right::Union{PhaseSum,JuliaRational}) = left + -to_exact(right)
Base.:-(left::JuliaRational, right::PhaseSum) = left + -right
Base.one(::PhaseSum) = one(Rational{BigInt})
Base.zero(::PhaseSum) = zero(Rational{BigInt})

function Base.:^(value::PhaseSum, exponent::Integer)
    if length(value.terms) == 1
        phase, weight = only(value.terms)
        return phase_monomial(phase * exponent, weight^exponent)
    end
    exponent >= 0 || throw(DomainError(exponent, "negative powers require a single phase"))
    return Base.power_by_squaring(value, exponent)
end

function Base.inv(value::PhaseSum)
    length(value.terms) == 1 ||
        throw(DomainError(value, "inverting requires a single phase"))
    phase, weight = only(value.terms)
    return phase_monomial(-phase, inv(weight))
end

# The normalized field trace of a primitive d-th root is μ(d)/φ(d),
# including when that root is embedded in a larger cyclotomic field.
# `phase` is a rational number of turns, typically Rational{BigInt}. `traces`
# caches each Rational{BigInt} trace by root order, a BigInt denominator.
function phase_trace(phase, traces)
    return get!(traces, denominator(phase)) do
        denominator_as_integer = Nemo.ZZ(denominator(phase))
        moebius = Nemo.moebius_mu(denominator_as_integer)
        iszero(moebius) && return zero(Rational{BigInt})
        return BigInt(moebius) // BigInt(Nemo.euler_phi(denominator_as_integer))
    end
end

"""
Return the normalized field trace of `|value|²` as a `Rational{BigInt}`.
`value` exposes phase and weight pairs through `terms`, as in a `PhaseSum`.
`traces` is a mutable cache such as a `Dict{BigInt,Rational{BigInt}}`.
"""
function phase_squared_norm(value, traces)
    return sum(value.terms; init=zero(Rational{BigInt})) do (phase, weight)
        sum(value.terms; init=zero(Rational{BigInt})) do (other_phase, other_weight)
            return weight * other_weight * phase_trace(phase - other_phase, traces)
        end
    end
end

# Seed the cache with trace one for the root of order one.
new_phase_traces() = Dict{BigInt,Rational{BigInt}}(1 => 1)

function Base.iszero(value::PhaseSum)
    # Distinct phases in [0, 1/2) have a non-rational ratio.
    length(value.terms) < 3 && return isempty(value.terms)
    return iszero(phase_squared_norm(value, new_phase_traces()))
end

Base.:(==)(left::PhaseSum, right::Union{PhaseSum,JuliaRational}) = iszero(left - right)
Base.:(==)(left::JuliaRational, right::PhaseSum) = right == left

# Use the rational trace mean as the candidate Rational{BigInt} result.
function rational_result(value::PhaseSum)
    if length(value.terms) == 1 && !haskey(value.terms, 0)
        throw(DomainError(value, "expected a rational result"))
    end
    traces = new_phase_traces()
    mean = sum(value.terms; init=zero(Rational{BigInt})) do (phase, weight)
        return weight * phase_trace(phase, traces)
    end
    # The normalized trace of |value - mean|² is nonnegative and vanishes
    # exactly when value equals the rational number mean.
    phase_squared_norm(value, traces) == mean^2 ||
        throw(DomainError(value, "expected a rational result"))
    return mean
end

# An explicitly supplied QQBar coefficient can be combined with the symbolic
# coefficients when FLINT can materialize their cyclotomic representation as a
# Nemo.QQBarFieldElem.
function as_qqbar(value::PhaseSum)
    return sum(value.terms; init=ALGEBRAIC_NUMBERS(0)) do (phase, weight)
        root = Nemo.root_of_unity(
            ALGEBRAIC_NUMBERS, Int(denominator(phase)), Int(numerator(phase))
        )
        return root * weight
    end
end

"""
Apply the binary callable `op`, such as `+` or `==`, to a `PhaseSum` `left`
and a `Nemo.QQBarFieldElem` `right`. If `right` is rational, `op` receives
`left` and a `Rational{BigInt}`. Otherwise, it receives two `Nemo.QQBarFieldElem`s.
"""
function with_qqbar(op, left, right)
    return if Nemo.is_rational(right)
        op(left, rational_result(right))
    else
        op(as_qqbar(left), right)
    end
end

Base.:+(left::PhaseSum, right::Nemo.QQBarFieldElem) = with_qqbar(+, left, right)
Base.:+(left::Nemo.QQBarFieldElem, right::PhaseSum) = right + left
Base.:-(left::PhaseSum, right::Nemo.QQBarFieldElem) = with_qqbar(-, left, right)
Base.:-(left::Nemo.QQBarFieldElem, right::PhaseSum) = -(right - left)
Base.:*(left::PhaseSum, right::Nemo.QQBarFieldElem) = with_qqbar(*, left, right)
Base.:*(left::Nemo.QQBarFieldElem, right::PhaseSum) = right * left
Base.:(==)(left::PhaseSum, right::Nemo.QQBarFieldElem) = with_qqbar(==, left, right)
Base.:(==)(left::Nemo.QQBarFieldElem, right::PhaseSum) = right == left
