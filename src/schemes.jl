"""A finite bilinear matrix multiplication algorithm with three indexed coefficient maps."""
abstract type BilinearScheme end

struct ExplicitScheme{A,B,C} <: BilinearScheme
    u::Int
    U::A
    V::B
    W::C
end

"""Construct a scheme from three column-major coefficient tables (block coordinates × terms)."""
function explicit_scheme(U::AbstractMatrix, V::AbstractMatrix, W::AbstractMatrix)
    Base.require_one_based_indexing(U, V, W)
    size(U) == size(V) == size(W) ||
        throw(DimensionMismatch("the three coefficient tables must have the same size"))
    rows, rank = size(U)
    u = isqrt(rows)
    u > 0 && u^2 == rows && rank > 0 || throw(DimensionMismatch("expected u² rows and at least one column"))
    return ExplicitScheme(u, U, V, W)
end

struct PaperProgram{Ops<:Tuple}
    steps::BigInt
    log_length::BigInt
    power::BigInt
    copies::BigInt
    overhead::Int
    operations::Ops
end

struct PaperScheme{P<:PaperProgram} <: BilinearScheme
    derivation::PaperDerivation
    program::P
end

"""
    multiplication_scheme(target_exponent = 5//2) -> BilinearScheme

Construct Shpilka's exact bilinear algorithm for the given rational upper bound
on the matrix multiplication exponent. The target must exceed `9//4`.
The finite substitution program retains tensor powers and derivation loops
without expanding their coefficient tables. It can be reused for many inputs.

`verify_scheme` audits the construction parameters and arithmetic exponent.
`multiply(A, B, scheme)` requests execution. `scheme[term, leg, coordinate]`
indexes a coefficient (legs 1 and 2 are the left and right input forms, leg 3
is the output weight). Paper coefficients print as unevaluated contractions.
"""
function multiplication_scheme(target_exponent::Union{Integer,Rational}=5//2)
    parameters = ConstructionParameters(target_exponent)
    derivation = PaperDerivation(parameters)
    S = parameters.step_bound
    log_length = parameters.q + 2 + ndigits(parameters.q - 1; base=2)
    overhead = 34
    N = 8 * overhead * S * log_length + 64 * S^2
    program = PaperProgram(S, log_length, N, _witness_copies(S, N), overhead,
                           (materialize_derivation, compile_witness, seed_decomposition))
    return PaperScheme(derivation, program)
end

# The side is r^(N²) from Lemma 6.7. Even its bit length can exceed all
# addressable memory. Keep the executable definition, not a floating estimate.
struct WitnessSide{S<:PaperScheme}
    scheme::S
end
block_side(s::PaperScheme) = WitnessSide(s)
block_side(s::ExplicitScheme) = s.u

function Base.show(io::IO, s::WitnessSide)
    print(io, "r^(N²) from Lemma 6.7 (q=", s.scheme.derivation.parameters.q,
          ", N=", s.scheme.program.power, ")")
end
function Base.show(io::IO, s::PaperScheme)
    print(io, "multiplication_scheme(", s.derivation.parameters.target, ")")
end
function Base.show(io::IO, ::MIME"text/plain", s::PaperScheme)
    show(io, s)
    print(io, "\n  Base block side ", block_side(s))
end

function execution_dimensions(s::ExplicitScheme, maxside, maxrank)
    rank = size(s.U, 2)
    return s.u <= maxside && rank <= maxrank ? (s.u, rank) : nothing
end

# Compare the *exact* count with a materialization limit using a binary
# exponentiation that never constructs the out-of-budget integer.
function _bounded_power(base::Integer, exponent::Integer, limit::Integer)
    limit >= 1 || return nothing
    answer, factor, n = big(1), big(base), big(exponent)
    while n > 0
        if isodd(n)
            factor > div(limit, answer) && return nothing
            answer *= factor
        end
        n >>= 1
        if n > 0
            factor > div(limit, factor) && return nothing
            factor *= factor
        end
    end
    return answer
end

function execution_dimensions(s::PaperScheme, maxside, maxrank)
    # The seed has (2a-1)^(6m) indexed products. Its matrix side also
    # satisfies log2(u) >= 2mq by Theorem 1.2's proof (q >= 16).
    p, m = s.derivation.parameters, s.program.copies
    min(maxside, maxrank) >= 1 || return nothing
    2 * m * p.q >= ndigits(maxside; base=2) && return nothing
    6 * m * p.q >= ndigits(maxrank; base=2) && return nothing
    a = _materialize_length(p.a)
    rank = _bounded_power(2a - 1, 6m, maxrank)
    isnothing(rank) && return nothing
    nodes = s.program.operations[1](s.derivation)
    u = witness_side(nodes, s.program.power)
    return u <= maxside ? (Int(u), Int(rank)) : nothing
end

_materialize_length(x::BigInt) = x
_materialize_length(x::ScaledPowerOfTwo) = x.coefficient * big(2)^x.exponent

function scheme_coefficient(s::ExplicitScheme, term::Integer, leg::Integer, coordinate::Integer)
    table = (s.U, s.V, s.W)[leg]
    return to_exact(table[coordinate, term])
end

struct LoweredScheme <: BilinearScheme
    seed::SeedDecomposition
    witness::CompiledWitness
    function LoweredScheme(seed::SeedDecomposition, witness::CompiledWitness)
        size(seed) == source_dims(witness.restriction) ||
            throw(DimensionMismatch("seed and witness differ"))
        target_dims(witness.restriction) == mm_dims(witness.side) ||
            throw(DimensionMismatch("witness has wrong target"))
        new(seed, witness)
    end
end
block_side(s::LoweredScheme) = s.witness.side
function execution_dimensions(s::LoweredScheme, maxside, maxrank)
    u, r = block_side(s), rank_count(s.seed)
    return u <= maxside && r <= maxrank ? (Int(u), Int(r)) : nothing
end

"""Contract one target row of an exact restriction with one rank-one seed term."""
function scheme_coefficient(s::LoweredScheme, term::Integer, leg::Integer, coordinate::Integer)
    1 <= term <= rank_count(s.seed) || throw(BoundsError(s, term))
    row = s.witness.restriction.legs[leg]
    total = big(0)//1
    for (source_index, weight) in row_entries(row, coordinate)
        total += weight * rank_coefficient(s.seed, term, leg, source_index)
    end
    return total
end

function lower_scheme(s::PaperScheme)
    build, compile, decompose = s.program.operations
    witness = compile(build(s.derivation), s.program.power; step_bound=s.program.steps)
    a = _materialize_length(s.derivation.parameters.a)
    return LoweredScheme(decompose(a, a, witness.copies), witness)
end

struct PaperCoefficient{S<:PaperScheme}
    scheme::S
    term::BigInt
    leg::Int
    coordinate::BigInt
end

function Base.show(io::IO, c::PaperCoefficient)
    print(io, "row ", c.coordinate, " of restriction leg ", c.leg,
          " applied to polynomial seed term ", c.term)
end

# For ordinary index queries the proven lower bounds settle membership
# immediately. Only an index with an exceptionally long representation
# requires evaluating the corresponding exact upper endpoint.
function _check_paper_index(s::PaperScheme, term, leg, coordinate)
    1 <= leg <= 3 || throw(BoundsError(1:3, leg))
    term >= 1 && coordinate >= 1 || throw(BoundsError(s, (term, leg, coordinate)))
    p, m = s.derivation.parameters, s.program.copies
    if ndigits(term; base=2) > 6 * m * p.q
        rank = _bounded_power(2 * _materialize_length(p.a) - 1, 6m, big(term) - 1)
        isnothing(rank) || throw(BoundsError(s, term))
    end
    if ndigits(coordinate; base=2) > 4 * m * p.q
        u = witness_side(s.program.operations[1](s.derivation), s.program.power)
        coordinate <= u^2 || throw(BoundsError(s, coordinate))
    end
end
function scheme_coefficient(s::PaperScheme, term::Integer, leg::Integer, coordinate::Integer)
    _check_paper_index(s, term, leg, coordinate)
    return PaperCoefficient(s, big(term), Int(leg), big(coordinate))
end
Base.getindex(s::BilinearScheme, term::Integer, leg::Integer, coordinate::Integer) =
    scheme_coefficient(s, term, leg, coordinate)

"""
    materialize(coefficient; max_leg_bits)

Evaluate a deferred coefficient by composing the paper's exact restriction
and contracting the requested row. The explicit budget limits the permitted
bit length of a source-leg dimension; full paper instances are enormous.
"""
function materialize(c::PaperCoefficient; max_leg_bits::Integer)
    s = c.scheme
    max_leg_bits >= 1 || throw(DomainError(max_leg_bits))
    p = s.derivation.parameters
    # Each of the three polynomial factors is at least 2^q. Check before
    # attempting to allocate either the seed dimensions or any proof nodes.
    lower = 6 * s.program.copies * p.q + 1
    lower <= max_leg_bits ||
        throw(ArgumentError("a source-leg dimension needs at least $lower bits, exceeding the requested budget of $max_leg_bits"))
    lower <= typemax(Int) ||
        throw(ArgumentError("a source-leg dimension needs at least $lower bits, beyond addressable bit lengths on this runtime"))
    # log2(seed_dim) = 2m log2(a²(2a-1)); use an upper bound without expanding a.
    upper = 2 * s.program.copies * (3 * (p.q + ndigits(p.q; base=2)) + 1) + 1
    upper <= max_leg_bits ||
        throw(ArgumentError("the source-leg dimension could exceed the requested budget (upper bound $upper bits)"))
    return scheme_coefficient(lower_scheme(s), c.term, c.leg, c.coordinate)
end
