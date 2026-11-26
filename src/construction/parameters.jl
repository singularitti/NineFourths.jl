"""
    _OPENAI_EXPONENT_BOUND::Rational{BigInt}

The exact reference exponent `9//4` that the construction approaches.
"""
const _OPENAI_EXPONENT_BOUND = big(9) // 4

"""
    ScaledPowerOfTwo(coefficient, exponent)

Represent the exact product `coefficient * 2^exponent` in factored form.

Both fields are stored as `BigInt`. This representation keeps large powers
from having to be expanded when only the construction parameters are needed.
"""
struct ScaledPowerOfTwo
    coefficient::BigInt
    exponent::BigInt
end

"""
    show(io::IO, value::ScaledPowerOfTwo)

Write `value` as a coefficient times a power of two without expanding it.
"""
function Base.show(io::IO, value::ScaledPowerOfTwo)
    return print(io, value.coefficient, " * 2^", value.exponent)
end

"""
    _scaled_power_of_two(coefficient::Integer, exponent::Integer)

Scale an integer coefficient by a power of two.

Return a shifted `BigInt` for ordinary shifts or a `ScaledPowerOfTwo` for
large exponents. Construction parameters use nonnegative exponents, for which
both representations give the exact product.
"""
function _scaled_power_of_two(coefficient::Integer, exponent::Integer)
    coefficient = BigInt(coefficient)
    # The cutoff controls storage only. The factored value is also exact.
    return if exponent <= 4096
        coefficient << Int(exponent)
    else
        ScaledPowerOfTwo(coefficient, BigInt(exponent))
    end
end

"""
    ShpilkaParameters(target)

Choose the exact parameters in Shpilka's proof of Theorem 1.2.

`target` must have a finite exact rational value above OpenAI's `9//4` bound.
The constructor accepts Julia integers and rationals and Nemo values supported
by `rational_result`, such as `Nemo.QQFieldElem`. A nonfinite rational target or
one at or below `9//4` raises `DomainError`.

`target` and `epsilon` are stored as `Rational{BigInt}`. `epsilon` is the gap
between the target and `9//4`, capped at one. `q = ceil(16 / epsilon^2)` and
`step_bound = q * (2q^2 + 7q)` are stored as `BigInt`. The latter bounds the
number of non-baseline derivation entries. `a = q * 2^q` is the final diagonal
coordinate and `length_bound = 4a` bounds all lengths in the derivation.
These two values are `BigInt` or, for large powers, `ScaledPowerOfTwo`.
"""
struct ShpilkaParameters
    target::Rational{BigInt}
    epsilon::Rational{BigInt}
    q::BigInt
    a::Union{BigInt,ScaledPowerOfTwo}
    step_bound::BigInt
    length_bound::Union{BigInt,ScaledPowerOfTwo}
    function ShpilkaParameters(target)
        exact_target = rational_result(target)
        isfinite(exact_target) ||
            throw(DomainError(target, "the target exponent must be finite"))
        exact_target > _OPENAI_EXPONENT_BOUND ||
            throw(DomainError(target, "the target exponent must be greater than 9/4"))
        epsilon = min(exact_target - _OPENAI_EXPONENT_BOUND, one(exact_target))
        q = ceil(BigInt, 16 / epsilon^2)
        a = _scaled_power_of_two(q, q)
        step_bound = q * (2q^2 + 7q)
        length_bound = _scaled_power_of_two(4q, q)
        return new(exact_target, epsilon, q, a, step_bound, length_bound)
    end
end
