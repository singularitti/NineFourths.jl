const _OPENAI_EXPONENT_BOUND = big(9) // 4

# Keep powers that would make a symbolic rule itself expensive in factored form.
struct ScaledPowerOfTwo
    coefficient::BigInt
    exponent::BigInt
end

function Base.show(io::IO, value::ScaledPowerOfTwo)
    return print(io, value.coefficient, " * 2^", value.exponent)
end

function _scaled_power_of_two(coefficient::BigInt, exponent::BigInt)
    # The cutoff controls storage only. The factored value is also exact.
    return if exponent <= 4096
        coefficient << Int(exponent)
    else
        ScaledPowerOfTwo(coefficient, exponent)
    end
end

"""
    ShpilkaParameters(target)

Exact parameters in Shpilka's proof of Theorem 1.2. The target is a finite
integer or rational above OpenAI's `9//4` bound. `epsilon` is the gap between
the target and that bound, capped at one.
`q` is `ceil(16 / epsilon^2)`, `a` is `q * 2^q`,
`step_bound` bounds the non-baseline derivation entries, and `length_bound`
bounds their coordinates. The two bounds and the construction coordinates are
exact, with large powers of two stored in factored form.
"""
struct ShpilkaParameters
    target::Rational{BigInt}
    epsilon::Rational{BigInt}
    q::BigInt
    a::Union{BigInt,ScaledPowerOfTwo}
    step_bound::BigInt
    length_bound::Union{BigInt,ScaledPowerOfTwo}
    function ShpilkaParameters(target::Union{Integer,Rational})
        isfinite(target) || throw(DomainError(target, "the target exponent must be finite"))
        exact_target = Rational{BigInt}(target)
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
