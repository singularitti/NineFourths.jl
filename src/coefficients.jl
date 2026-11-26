"""
    ALGEBRAIC_NUMBERS

Nemo's parent for the algebraic closure of the rational field. Its elements
have type `Nemo.QQBarFieldElem`.
"""
const ALGEBRAIC_NUMBERS = Nemo.algebraic_closure(Nemo.QQ)

"""
    JuliaRational

Union of Julia's `Integer` and `Rational` types accepted as rational operands
of symbolic cyclotomic expressions.
"""
const JuliaRational = Union{Integer,Rational}

"""
    PhaseSum(terms)

Represent an exact cyclotomic expression as a sparse sum of terms
`weight * exp(2πim * phase)`. The dictionary `terms` maps `Rational{BigInt}`
phases, measured in turns, to nonzero weights of the same type. Phases lie in
`[0, 1/2)`, with each half turn absorbed into the sign of its weight.

Use [`root_of_unity`](@ref) or [`phase_monomial`](@ref) to construct normalized
terms from arbitrary rational phases. Distinct keys can still satisfy
cyclotomic relations. Equality tests the algebraic value of the sum.
"""
struct PhaseSum
    terms::Dict{Rational{BigInt},Rational{BigInt}}
end

"""
    ExactScalar

Union of `Rational{BigInt}`, [`PhaseSum`](@ref), and `Nemo.QQBarFieldElem`
used for exact construction coefficients.
"""
const ExactScalar = Union{Rational{BigInt},PhaseSum,Nemo.QQBarFieldElem}

to_exact(value::Union{Integer,Nemo.ZZRingElem}) = BigInt(value) // 1
to_exact(value::Rational) = Rational{BigInt}(value)
to_exact(value::Union{PhaseSum,Nemo.QQBarFieldElem}) = value

rational_result(value::Union{JuliaRational,Nemo.ZZRingElem}) = to_exact(value)

function rational_result(value::Nemo.QQFieldElem)
    return BigInt(numerator(value)) // BigInt(denominator(value))
end

to_exact(value::Nemo.QQFieldElem) = rational_result(value)

"""
    to_exact(value)::ExactScalar

Convert a Julia or Nemo integer or rational to `Rational{BigInt}`. Retain the
exact representation of a [`PhaseSum`](@ref) or `Nemo.QQBarFieldElem`.
"""
to_exact

function rational_result(value::Nemo.QQBarFieldElem)
    Nemo.is_rational(value) || throw(DomainError(value, "expected a rational result"))
    return rational_result(Nemo.QQFieldElem(value))
end

"""
    add_phase!(terms, phase, weight)

Add an exact rational `weight` at a rational `phase` in turns. Normalize the
phase to `[0, 1/2)` and adjust the weight's sign before updating the dictionary.
Remove an entry when its new weight is zero. The mutable `terms` dictionary
uses the key and value types of [`PhaseSum`](@ref). Return `nothing`.
"""
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

"""
    finish_phases(terms)

Wrap a normalized phase dictionary as a [`PhaseSum`](@ref). Return a
`Rational{BigInt}` directly if the dictionary is empty or has only a constant
term, whose phase is zero.
"""
function finish_phases(terms)
    if length(terms) <= 1 && all(iszero, keys(terms))
        return get(terms, 0, zero(Rational{BigInt}))
    end
    return PhaseSum(terms)
end

"""
    phase_monomial(phase, weight)

Represent the single term `weight * exp(2πim * phase)` for exact rational
`phase` and `weight`. A constant or zero term becomes a `Rational{BigInt}`.
Other terms become a normalized [`PhaseSum`](@ref).
"""
function phase_monomial(phase, weight)
    terms = Dict{Rational{BigInt},Rational{BigInt}}()
    add_phase!(terms, phase, weight)
    return finish_phases(terms)
end

"""
    root_of_unity(order::Integer, exponent::Integer=1)

Return `exp(2πim * exponent / order)` exactly. The order must be positive.
A rational root is represented as a `Rational{BigInt}`. Other roots use
[`PhaseSum`](@ref), which can represent orders larger than `typemax(Int)`.
"""
function root_of_unity(order::Integer, exponent::Integer=1)
    order > 0 || throw(ArgumentError("root of unity order must be positive"))
    return phase_monomial(BigInt(exponent) // BigInt(order), to_exact(1))
end

phase_terms(value::PhaseSum) = value.terms
phase_terms(value::JuliaRational) = ((zero(Rational{BigInt}), to_exact(value)),)

"""
    phase_terms(value)

Yield `(phase, weight)` pairs with `Rational{BigInt}` components. A Julia
integer or rational contributes one term of phase zero. A [`PhaseSum`](@ref)
exposes its retained terms through its dictionary.
"""
phase_terms

"""
    add_phases(left, right)

Add the terms yielded by [`phase_terms(right)`](@ref phase_terms) to a copy
of `left.terms`, combining weights at equal phases. The left operand exposes
a normalized dictionary like [`PhaseSum`](@ref). The right operand is a
`PhaseSum`, `Integer`, or `Rational`.
"""
function add_phases(left, right)
    terms = copy(left.terms)
    for (phase, weight) in phase_terms(right)
        add_phase!(terms, phase, weight)
    end
    return finish_phases(terms)
end

"""
    +(left::PhaseSum, right::Union{PhaseSum,JuliaRational,Nemo.QQBarFieldElem})
    +(left::Union{JuliaRational,Nemo.QQBarFieldElem}, right::PhaseSum)

Add exact values by combining normalized phase weights. Julia integers and
rationals enter as constant terms. With a `Nemo.QQBarFieldElem` operand, use
exact rational arithmetic if that operand is rational and Nemo algebraic
arithmetic otherwise. The latter may materialize the symbolic roots.
"""
Base.:+(left::PhaseSum, right::Union{PhaseSum,JuliaRational}) = add_phases(left, right)
Base.:+(left::JuliaRational, right::PhaseSum) = right + left

"""
    *(left::PhaseSum, right::Union{PhaseSum,JuliaRational,Nemo.QQBarFieldElem})
    *(left::Union{JuliaRational,Nemo.QQBarFieldElem}, right::PhaseSum)

Multiply exact values. Two symbolic sums convolve their phases and multiply
the paired weights. A rational multiplier scales the weights. A nonrational
Nemo algebraic multiplier materializes the symbolic roots in Nemo.
"""
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

"""
    /(left::PhaseSum, right::JuliaRational)

Divide the symbolic sum by multiplying its weights by the exact reciprocal
of `right`. Supply a nonzero divisor for a finite result.
"""
Base.:/(left::PhaseSum, right::JuliaRational) = left * inv(to_exact(right))

"""
    -(value::PhaseSum)
    -(left::PhaseSum, right::Union{PhaseSum,JuliaRational,Nemo.QQBarFieldElem})
    -(left::Union{JuliaRational,Nemo.QQBarFieldElem}, right::PhaseSum)

Negate all weights in a symbolic sum, or subtract the right operand from the
left. Rational operands act on the constant term. Nonrational Nemo operands
use concrete algebraic subtraction.
"""
Base.:-(value::PhaseSum) = value * -1
Base.:-(left::PhaseSum, right::Union{PhaseSum,JuliaRational}) = left + -to_exact(right)
Base.:-(left::JuliaRational, right::PhaseSum) = left + -right

"""
    one(::PhaseSum)::Rational{BigInt}

Return the exact rational multiplicative identity of a symbolic sum.
"""
Base.one(::PhaseSum) = one(Rational{BigInt})

"""
    zero(::PhaseSum)::Rational{BigInt}

Return the exact rational additive identity of a symbolic sum.
"""
Base.zero(::PhaseSum) = zero(Rational{BigInt})

"""
    ^(value::PhaseSum, exponent::Integer)

Raise a symbolic sum to an integer power. A single term raises its weight
and multiplies its phase by `exponent`. Multi-term sums use repeated
squaring for nonnegative exponents and throw `DomainError` for negative ones.
"""
function Base.:^(value::PhaseSum, exponent::Integer)
    if length(value.terms) == 1
        phase, weight = only(value.terms)
        return phase_monomial(phase * exponent, weight^exponent)
    end
    exponent >= 0 || throw(DomainError(exponent, "negative powers require a single phase"))
    return Base.power_by_squaring(value, exponent)
end

"""
    inv(value::PhaseSum)

Invert a single symbolic term by negating its phase and reciprocating its
weight. Throw `DomainError` unless the sum has exactly one stored term.
"""
function Base.inv(value::PhaseSum)
    length(value.terms) == 1 ||
        throw(DomainError(value, "inverting requires a single phase"))
    phase, weight = only(value.terms)
    return phase_monomial(-phase, inv(weight))
end

"""
    phase_trace(phase, traces)::Rational{BigInt}

Compute the normalized field trace of `exp(2πim * phase)`. For the reduced
denominator `d` of the rational phase, the trace is `μ(d) / φ(d)`, where `μ`
is the Möbius function and `φ` is Euler's totient. This value also applies
when the root belongs to a larger cyclotomic field. Cache traces in `traces`
by root order.
"""
function phase_trace(phase, traces)
    return get!(traces, denominator(phase)) do
        denominator_as_integer = Nemo.ZZ(denominator(phase))
        moebius = Nemo.moebius_mu(denominator_as_integer)
        iszero(moebius) && return zero(Rational{BigInt})
        return BigInt(moebius) // BigInt(Nemo.euler_phi(denominator_as_integer))
    end
end

"""
    phase_squared_norm(value, traces)::Rational{BigInt}

Return the normalized field trace of the squared absolute value of `value`.
`value` exposes phase and weight pairs through `terms`, as in a `PhaseSum`.
`traces` is a mutable order-to-trace cache as returned by [`new_phase_traces`](@ref).
"""
function phase_squared_norm(value, traces)
    return sum(value.terms; init=zero(Rational{BigInt})) do (phase, weight)
        sum(value.terms; init=zero(Rational{BigInt})) do (other_phase, other_weight)
            return weight * other_weight * phase_trace(phase - other_phase, traces)
        end
    end
end

"""
    new_phase_traces()::Dict{BigInt,Rational{BigInt}}

Make a trace cache seeded with the normalized trace of the root of order one.
"""
new_phase_traces() = Dict{BigInt,Rational{BigInt}}(1 => 1)

"""
    iszero(value::PhaseSum)::Bool

Test whether the symbolic sum is algebraically zero. For general sums, the
normalized trace of the squared absolute value detects cancellation between
distinct phases exactly.
"""
function Base.iszero(value::PhaseSum)
    # Distinct phases in [0, 1/2) have a non-rational ratio.
    length(value.terms) < 3 && return isempty(value.terms)
    return iszero(phase_squared_norm(value, new_phase_traces()))
end

"""
    ==(left::PhaseSum, right::Union{PhaseSum,JuliaRational,Nemo.QQBarFieldElem})
    ==(left::Union{JuliaRational,Nemo.QQBarFieldElem}, right::PhaseSum)

Compare the algebraic values exactly. With symbolic or rational operands,
test whether their difference vanishes, including cyclotomic cancellation.
A nonrational Nemo operand uses the concrete algebraic comparison.
"""
Base.:(==)(left::PhaseSum, right::Union{PhaseSum,JuliaRational}) = iszero(left - right)
Base.:(==)(left::JuliaRational, right::PhaseSum) = right == left

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

"""
    rational_result(value)::Rational{BigInt}

Extract the exact rational value of a Julia or Nemo integer or rational,
symbolic phase sum, or Nemo algebraic number. For a symbolic sum, use its
normalized trace as the candidate value and verify zero variance across
the field embeddings. Throw `DomainError` if the value is nonrational.
"""
rational_result

"""
    as_qqbar(value::PhaseSum)::Nemo.QQBarFieldElem

Materialize a symbolic sum in Nemo's algebraic closure, using the same
complex root for each rational phase. Each root order must fit in `Int`,
and the required cyclotomic representations must fit available resources.
"""
function as_qqbar(value::PhaseSum)
    return sum(value.terms; init=ALGEBRAIC_NUMBERS(0)) do (phase, weight)
        root = Nemo.root_of_unity(
            ALGEBRAIC_NUMBERS, Int(denominator(phase)), Int(numerator(phase))
        )
        return root * weight
    end
end

"""
    with_qqbar(op, left, right)

Apply the binary callable `op`, such as `+` or `==`, to a `PhaseSum` `left`
and a `Nemo.QQBarFieldElem` `right`. If `right` is rational, `op` receives
`left` and a `Rational{BigInt}`. Otherwise, it receives two `Nemo.QQBarFieldElem`s.
"""
with_qqbar(op, left, right) =
    if Nemo.is_rational(right)
        op(left, rational_result(right))
    else
        op(as_qqbar(left), right)
    end

Base.:+(left::PhaseSum, right::Nemo.QQBarFieldElem) = with_qqbar(+, left, right)
Base.:+(left::Nemo.QQBarFieldElem, right::PhaseSum) = right + left
Base.:-(left::PhaseSum, right::Nemo.QQBarFieldElem) = with_qqbar(-, left, right)
Base.:-(left::Nemo.QQBarFieldElem, right::PhaseSum) = -(right - left)
Base.:*(left::PhaseSum, right::Nemo.QQBarFieldElem) = with_qqbar(*, left, right)
Base.:*(left::Nemo.QQBarFieldElem, right::PhaseSum) = right * left
Base.:(==)(left::PhaseSum, right::Nemo.QQBarFieldElem) = with_qqbar(==, left, right)
Base.:(==)(left::Nemo.QQBarFieldElem, right::PhaseSum) = right == left
