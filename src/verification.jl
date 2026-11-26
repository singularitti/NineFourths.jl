"""The exact rank-based exponent bound `log_base(rank)` from a checked coefficient table."""
struct RankExponent
    base::Int
    rank::Int
end

function Base.show(io::IO, exponent::RankExponent)
    return print(io, "log_", exponent.base, "(", exponent.rank, ")")
end

"""
    VerificationReport

The result of `verify_scheme`. `identity` is `:exact_coefficients` after a
coefficient-by-coefficient check, `:symbolic_restriction` after a construction
certificate check, `:failed` for a failed check, or `:unchecked` if enumeration
exceeds its budget. `exponent` is a rank-based bound when the identity is
verified and the base matrix dimension is at least two. `target` is the
exponent requested when constructing a paper scheme. `valid` requires the
verified identity and, when present, the requested exponent bound.
"""
struct VerificationReport
    valid::Bool
    identity::Symbol
    exponent::Union{Nothing,RankExponent,Rational{BigInt}}
    target::Union{Nothing,Rational{BigInt}}
    diagnostics::Vector{String}
end

function _verification_failure(message; target=nothing)
    return VerificationReport(false, :failed, nothing, target, [message])
end

"""
    verify_scheme(scheme::BilinearScheme) -> VerificationReport
    verify_scheme(scheme::ExplicitScheme; field=nothing) -> VerificationReport

Verify the matrix multiplication identity and derive the exponent bound.
Explicit and lowered schemes are checked on every pair of matrix units in
exact arithmetic. For explicit tables, `field` supplies the common exact
field when it cannot be inferred from the coefficients.
For the paper form, the identity evidence is theorem-level verification of the
executable derivation and restriction recipe, with symbolic copy, degree, and
rank bounds from §6 of the paper. This certificate depends on the algebraic
primitives used by the compiler and the seed builder.
"""
verify_scheme(scheme::ExplicitScheme; field=nothing) =
    _verify_coefficient_tables(scheme.u, scheme.U, scheme.V, scheme.W; field)

_verification_rational_or_algebraic(value) = value isa Union{
    _BuiltinExact,PhaseSum,Nemo.QQBarFieldElem,Nemo.QQFieldElem,Nemo.ZZRingElem
}

function _unsupported_verification_scalar(value)
    value isa Union{AbstractFloat,AbstractArray,Nemo.MatElem,Nemo.MatRingElem} && return true
    value isa Complex && return !(value isa Complex{<:_BuiltinExact})
    return value isa Nemo.RingElem && !Nemo.is_exact_type(typeof(value))
end

_widen_verification_scalar(value) = to_exact(value)
_widen_verification_scalar(value::Nemo.ZZRingElem) = to_exact(BigInt(value))

function _native_verification_scalar(options, value)
    if value isa Union{PhaseSum,Nemo.QQBarFieldElem}
        if options.one isa Nemo.QQBarFieldElem
            return value isa PhaseSum ? as_qqbar(value) : value
        elseif options.one isa Complex
            algebraic = value isa PhaseSum ? as_qqbar(value) : value
            return complex(rational_result(real(algebraic)), rational_result(imag(algebraic)))
        end
        value = rational_result(value)
    end
    return _field_embed_native(options, value)
end

function _verification_coefficients(tables, field)
    if isnothing(field) && all(T -> all(_verification_rational_or_algebraic, T), tables)
        zero_value = zero(Rational{BigInt})
        return map(T -> map(_widen_verification_scalar, T), tables), zero_value, one(zero_value)
    end

    # Rational coefficients can embed in the field of the native entries.
    # Inspect each table before converting so a mixed parent is identified.
    domain, scalar_type, sample = nothing, Union{}, nothing
    fractional_entries = false
    for table in tables, value in table
        value isa _BuiltinRational && (fractional_entries |= denominator(value) != 1)
        _verification_rational_or_algebraic(value) && continue
        domain = _common_field(domain, _scalar_field(value))
        scalar_type = promote_type(scalar_type, typeof(value))
        typeof(value) === scalar_type && (sample = value)
    end
    metadata = (; domain, scalar_type, sample, fractional_entries,
                rational_entries=false, exact_entries=false)
    options = _field_configuration(metadata, field)
    if options.one isa Complex{<:_BuiltinExact} && !(options.one isa Complex{Rational{BigInt}})
        options = _field_configuration(metadata, Complex{Rational{BigInt}})
    end
    zero_value, one_value = options.zero, options.one
    if isnothing(zero_value) || isnothing(one_value) || zero_value == one_value ||
       _unsupported_verification_scalar(one_value) ||
       (one_value isa _BuiltinExact && !(one_value isa Union{BigInt,Rational{BigInt}}))
        throw(CoefficientIncompatible("The explicit maps require identities in a supported exact field."))
    end
    converted = map(T -> map(value -> _native_verification_scalar(options, value), T), tables)
    return converted, zero_value, one_value
end

function _verify_coefficient_tables(u, U, V, W; field=nothing)
    dimensions = size(U)
    entries, rank = dimensions
    if u < 1 || big(u)^2 != entries || rank < 1 ||
       size(V) != dimensions || size(W) != dimensions
        return _verification_failure(
            "Each explicit map must have one row per matrix entry and one column per rank term.",
        )
    end

    tables = (U, V, W)
    if any(T -> any(value -> value isa _BuiltinRational && !isfinite(value), T), tables)
        return _verification_failure("The explicit maps must have finite coefficients.")
    end
    if any(T -> any(_unsupported_verification_scalar, T), tables)
        return _verification_failure("The explicit maps require coefficients in a supported exact field.")
    end

    try
        coefficients, zero_value, one_value = _verification_coefficients(tables, field)
        return _check_matrix_unit_coefficients(u, coefficients, zero_value, one_value)
    catch err
        if err isa ArgumentError
            return _verification_failure("The explicit map coefficients do not share a compatible field parent.")
        elseif err isa CoefficientIncompatible
            return _verification_failure(err.message)
        elseif err isa Union{MethodError,InexactError,DomainError,DivideError,TypeError}
            return _verification_failure("The explicit map coefficients cannot be combined in a common exact field.")
        end
        rethrow()
    end
end

function _check_matrix_unit_coefficients(u, (U, V, W), zero_value, one_value)
    entries, rank = size(U)
    coordinates = CartesianIndices((Int(u), Int(u)))
    for x in 1:entries, y in 1:entries
        i, left_inner = Tuple(coordinates[x])
        right_inner, j = Tuple(coordinates[y])
        products = [(term, U[x, term] * V[y, term]) for term in 1:rank if
                    U[x, term] != zero_value && V[y, term] != zero_value]
        for z in 1:entries
            coefficient = zero_value
            for (term, factor) in products
                coefficient += W[z, term] * factor
            end
            expected = left_inner == right_inner && Tuple(coordinates[z]) == (i, j)
            coefficient == (expected ? one_value : zero_value) && continue
            coordinate = Tuple(coordinates[z])
            return _verification_failure(
                "The coefficient at output $coordinate for input matrix units " *
                "($i, $left_inner) and ($right_inner, $j) differs from matrix multiplication.",
            )
        end
    end

    exponent = u >= 2 ? RankExponent(Int(u), rank) : nothing
    return VerificationReport(true, :exact_coefficients, exponent, nothing, String[])
end

"""
    verify_scheme(scheme::LoweredScheme; max_terms=1_000_000) -> VerificationReport

Read the exact coefficient maps used by `multiply` and check the resulting
matrix multiplication tensor. `max_terms` bounds the number of table entries
and potential rank summands. Each coefficient can require additional work to
contract its restriction row with the seed. If the bound prevents enumeration,
the report has `identity == :unchecked`.
"""
function verify_scheme(scheme::LoweredScheme; max_terms::Integer=1_000_000)
    max_terms >= 0 || throw(DomainError(max_terms, "the verification budget must be nonnegative"))
    u, rank = block_side(scheme), rank_count(scheme.seed)
    if u < 1 || rank < 1
        return _verification_failure("The lowered scheme must have positive dimension and rank.")
    end
    entries = u^2
    work_bound = rank * (3entries + entries^3)
    if work_bound > max_terms || 3entries * rank > typemax(Int)
        return VerificationReport(
            false, :unchecked, nothing, nothing,
            ["Enumerating the lowered coefficient maps exceeds the verification budget."],
        )
    end
    tables = try
        ntuple(3) do leg
            [scheme_coefficient(scheme, term, leg, coordinate)
             for coordinate in 1:Int(entries), term in 1:Int(rank)]
        end
    catch err
        err isa BoundsError || rethrow()
        return _verification_failure("A lowered restriction references a source coefficient outside the seed.")
    end
    return _verify_coefficient_tables(u, tables...)
end

function _is_scaled_power(value::ScaledPowerOfTwo, coefficient, exponent)
    return value.coefficient == coefficient && value.exponent == exponent
end

function _is_scaled_power(value::BigInt, coefficient, exponent)
    value > 0 || return false
    ndigits(value; base=2) == exponent + ndigits(coefficient; base=2) || return false
    shift = Int(exponent)
    return trailing_zeros(value) >= shift && (value >> shift) == coefficient
end

function verify_scheme(scheme::PaperScheme)
    parameters = scheme.derivation.parameters
    target = parameters.target
    epsilon = parameters.epsilon
    q = parameters.q
    if target <= 9 // 4 || epsilon != min(target - 9 // 4, 1) ||
       q != ceil(BigInt, 16 / epsilon^2) || q < 16
        return _verification_failure("The parameter choice does not satisfy Theorem 1.2."; target)
    end

    # Lemma 6.5 uses q moves per doubling, with at most 2q+7 steps per
    # move. After q doublings the last coordinate is A, and the last
    # doubling's maximum intermediate length is less than 4A.
    step_bound = q^2 * (2q + 7)
    if parameters.step_bound != step_bound || !_is_scaled_power(parameters.a, q, q) ||
       !_is_scaled_power(parameters.length_bound, 4q, q)
        return _verification_failure("The derivation coordinates or step bound do not match Lemma 6.5."; target)
    end

    program = scheme.program
    if program.operations !== (materialize_derivation, compile_witness, seed_decomposition)
        return _verification_failure(
            "The executable construction must generate the derivation, compile its restriction, and use the balanced polynomial seed.";
            target,
        )
    end
    if LEG_PERMUTATIONS != ((1, 2, 3), (3, 1, 2), (2, 3, 1), (2, 1, 3), (3, 2, 1), (1, 3, 2))
        return _verification_failure("The seed legs do not match the six orientations used by its restriction."; target)
    end

    floor_log_q = ndigits(q; base=2) - 1
    ceil_log_q = ndigits(q - 1; base=2)
    log_length = q + 2 + ceil_log_q
    S = program.steps
    N = program.power
    c = program.overhead
    if S != step_bound || program.log_length != log_length || c != 34 ||
       N != 8c * S * log_length + 64S^2
        return _verification_failure("The step, length, or power budget does not match the construction."; target)
    end

    # Claim 6.6 bounds each stage degree by 6·9^N. After powering, each
    # of at most 2S stages uses at most 6N·9^N+2 ≤ 7N·9^N ≤ 63^N ≤ 2^(6N)
    # interpolation points. Each repeated restriction therefore needs 12SN
    # copies to interpolate and 6SN to supply the I_64 factors. Separately,
    # Lemma 6.7 bounds the rank of the powered catalyst by 2^(16SN²).
    application_copies = N^2 + 18S * N
    catalyst_copies = 16S * N^2
    m = program.copies
    if m != N * application_copies + catalyst_copies || m != N^3 + c * S * N^2
        return _verification_failure("The seed copy budget does not cover interpolation and catalyst preparation."; target)
    end

    # Lemma 6.7 gives √r ≥ B^N/(N+1)^(2S) and §6.1 gives n = r^(N²).
    # The flattening bound gives log2(B) ≤ 2 log2(L). Bound the loss in
    # log2(n)/(2m) relative to log2(B) with integer upper logs.
    ceil_log_power = ndigits(N; base=2)
    loss_numerator = 2log_length * (m - N^3) + 2S * N^2 * ceil_log_power
    if loss_numerator > m
        return _verification_failure("The verified matrix dimension does not attain the prescribed rate."; target)
    end

    # The q doublings give B ≥ (q/2)·2^(4q/3). With the bounded loss,
    # log2(n)/(2m) ≥ 4q/3 + log2(q) - 2. The seed uses Fourier order
    # 2A-1 or 2A depending on the characteristic. In both cases its
    # log2 rank is bounded by 6m log2(2A) = 6m (q + log2(q) + 1).
    exponent = 9 * (q + ceil_log_q + 1) // (4q + 3 * (floor_log_q - 2))
    if exponent > target
        return VerificationReport(false, :symbolic_restriction, exponent, target,
                                  ["The certified rank exponent exceeds the requested target."])
    end
    return VerificationReport(true, :symbolic_restriction, exponent, target, String[])
end
