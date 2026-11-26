# The reference exponent stored exactly as a Rational{BigInt}.
const _OPENAI_EXPONENT_BOUND = big(9) // 4

# Keep powers that would make a symbolic rule itself expensive in factored form.
struct ScaledPowerOfTwo
    coefficient::BigInt
    exponent::BigInt
end

function Base.show(io::IO, value::ScaledPowerOfTwo)
    return print(io, value.coefficient, " * 2^", value.exponent)
end

# Shift an integer coefficient by an integer exponent. The result is a BigInt
# for ordinary shifts or a ScaledPowerOfTwo with two BigInt fields for large powers.
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

Exact parameters in Shpilka's proof of Theorem 1.2. `target` must have a
finite exact rational value above OpenAI's `9//4` bound. Julia integers and
rationals and Nemo values supported by `rational_result`, such as
`Nemo.QQFieldElem`, are accepted. `target` and `epsilon` are stored as
`Rational{BigInt}`. `epsilon` is the gap between the target and `9//4`,
capped at one.

`q` is `ceil(16 / epsilon^2)`, and `step_bound` bounds the non-baseline
derivation entries. Both are `BigInt`. `a` is `q * 2^q`, and `length_bound`
bounds the coordinates. Both are `BigInt` or `ScaledPowerOfTwo` for large
powers stored in factored form.
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
