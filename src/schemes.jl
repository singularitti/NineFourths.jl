"""
    BilinearScheme

Abstract type for finite bilinear matrix multiplication rules.

Index a rule as `scheme[term, leg, coordinate]` to access a weight of a
rank-one product. Legs 1 and 2 give the left and right linear forms. Leg 3
gives the output weights. A `ShpilkaScheme` returns a deferred coefficient.

See also [`multiplication_scheme`](@ref), [`verify_scheme`](@ref), [`multiply`](@ref).
"""
abstract type BilinearScheme end

"""
    ExplicitScheme(u, U, V, W)

Store a block side `u` and three coefficient tables with `u²` rows.

The type parameters retain the individual table types. Use [`BilinearScheme`](@ref)
to infer `u` and validate the table shapes and axes.
"""
struct ExplicitScheme{A,B,C} <: BilinearScheme
    u::Int
    U::A
    V::B
    W::C
end

"""
    _matrix_size(matrix) -> (rows, columns)

Read the dimensions of a Julia matrix, Nemo matrix, or custom matrix-like table.

Throw a `DimensionMismatch` if `size(matrix)` has a length other than two.
"""
function _matrix_size(matrix)
    dimensions = size(matrix)
    length(dimensions) == 2 ||
        throw(DimensionMismatch("expected a matrix, got size $dimensions"))
    return dimensions
end

"""
    explicit_scheme(U, V, W)::ExplicitScheme

Construct a rule from three one-based, scalar-indexable coefficient tables.

Require a shared shape `(u², rank)` with a positive integer block side `u`
and a positive product count `rank`. Read rows in column-major block order.
"""
function explicit_scheme(U, V, W)
    dimensions = _matrix_size(U)
    dimensions == size(V) == size(W) ||
        throw(DimensionMismatch("the three coefficient tables must have the same size"))
    Base.require_one_based_indexing(U, V, W)
    rows, rank = dimensions
    u = isqrt(rows)
    u > 0 && u^2 == rows && rank > 0 ||
        throw(DimensionMismatch("expected u² rows and at least one column"))
    return ExplicitScheme(u, U, V, W)
end

"""
    BilinearScheme(U, V, W)

Create a scheme for square matrix blocks from three coefficient tables.

For block side `u`, each table has `u²` rows ordered by column-major block
coordinate and one column per product. Supply the dimensions through
`size(table)`, one-based axes through `axes(table)`, and scalar coefficients
through `table[row, term]`. Julia `AbstractMatrix` values, Nemo matrices, and
custom tables can be mixed. Matching columns of `U` and `V` describe the left
and right linear forms. The column of `W` gives the output weights. Entries
can be integers, rationals, or elements of the input matrices' field.

See also [`verify_scheme`](@ref), [`multiply`](@ref).

# Examples

```jldoctest
julia> using NineFourths

julia> scheme = BilinearScheme([2;;], [3;;], [1//6;;]);

julia> scheme[1, 3, 1]
1//6

julia> multiply([4;;], [5;;], scheme) == [20;;]
true
```
"""
BilinearScheme(U, V, W) = explicit_scheme(U, V, W)

"""
    ShpilkaProgram(steps, log_length, power, copies, overhead, operations)

Store the finite construction and its integer bounds from §6 of Shpilka's exposition.

`steps` bounds the number of derivation steps, and `log_length` bounds the
base-two logarithm of their maximum length. `power` gives the witness tensor
power, `copies` counts the seed copies, and `overhead` is the coefficient of
the extra seed-copy term. The three operations materialize a derivation,
compile a witness, and decompose the polynomial seed in that order.
"""
struct ShpilkaProgram{Ops<:Tuple}
    steps::BigInt
    log_length::BigInt
    power::BigInt
    copies::BigInt
    overhead::Int
    operations::Ops
end

"""
    ShpilkaScheme(derivation, program)

Pair a `ShpilkaDerivation` with its finite executable `ShpilkaProgram`.

Use [`multiplication_scheme`](@ref) to choose the derivation and program for
a target exponent.
"""
struct ShpilkaScheme{P<:ShpilkaProgram} <: BilinearScheme
    derivation::ShpilkaDerivation
    program::P
end

"""
    multiplication_scheme(target_exponent=5//2)::BilinearScheme

Construct a reusable bilinear matrix multiplication rule for a target exponent.

Pass a finite integer or exact rational strictly greater than `9//4`, as
required by Theorem 1.2 of Shpilka's exposition. The rule stores the finite
substitution program, including tensor powers and derivation loops, in
symbolic form. The block side can exceed the runtime's indexing limits.

Use [`verify_scheme`](@ref) to check its construction and exponent bound,
and [`multiply`](@ref) to request a product. Indexing the rule returns a
deferred contraction for the requested coefficient.

# Examples

```jldoctest
julia> using NineFourths

julia> scheme = multiplication_scheme(5//2);

julia> scheme isa BilinearScheme
true

julia> report = verify_scheme(scheme);

julia> (report.identity, report.exponent <= 5//2)
(:symbolic_restriction, true)
```
"""
function multiplication_scheme(target_exponent=5//2)
    parameters = ShpilkaParameters(target_exponent)
    derivation = ShpilkaDerivation(parameters)
    S = parameters.step_bound
    log_length = parameters.q + 2 + ndigits(parameters.q - 1; base=2)
    overhead = 34
    N = 8 * overhead * S * log_length + 64 * S^2
    program = ShpilkaProgram(
        S,
        log_length,
        N,
        _witness_copies(S, N),
        overhead,
        (materialize_derivation, compile_witness, seed_decomposition),
    )
    return ShpilkaScheme(derivation, program)
end

"""
    WitnessSide(scheme)

Represent the integer block side `r^(N²)` in Lemma 6.7 by the `ShpilkaScheme`
that defines it.
"""
struct WitnessSide{S<:ShpilkaScheme}
    scheme::S
end

"""
    block_side(s::ShpilkaScheme)::WitnessSide

Return a symbolic description of the block side defined by the witness recipe.
"""
block_side(s::ShpilkaScheme) = WitnessSide(s)

"""
    block_side(s::ExplicitScheme)::Int

Return the stored matrix block side of an explicit coefficient table.
"""
block_side(s::ExplicitScheme) = s.u

"""
    Base.show(io::IO, s::WitnessSide)

Print the symbolic block side and the construction parameters `q` and `N`.
"""
function Base.show(io::IO, s::WitnessSide)
    return print(
        io,
        "r^(N²) from Lemma 6.7 (q=",
        s.scheme.derivation.parameters.q,
        ", N=",
        s.scheme.program.power,
        ")",
    )
end

"""
    Base.show(io::IO, s::ShpilkaScheme)

Print a `multiplication_scheme` call with the stored exact target exponent.
"""
function Base.show(io::IO, s::ShpilkaScheme)
    return print(io, "multiplication_scheme(", s.derivation.parameters.target, ")")
end

"""
    Base.show(io::IO, ::MIME"text/plain", s::ShpilkaScheme)

Print the construction call followed by the symbolic block side on a second line.
"""
function Base.show(io::IO, ::MIME"text/plain", s::ShpilkaScheme)
    show(io, s)
    return print(io, "\n  Base block side ", block_side(s))
end

"""
    execution_dimensions(s::ExplicitScheme, maxside, maxrank) -> (side, rank)

Return the stored block side and product count if both meet their integer
limits, or `nothing` otherwise.
"""
function execution_dimensions(s::ExplicitScheme, maxside, maxrank)
    _, rank = size(s.U)
    return s.u <= maxside && rank <= maxrank ? (s.u, rank) : nothing
end

"""
    _bounded_power(base::Integer, exponent::Integer, limit::Integer)

Compute the exact `BigInt` power of a positive base to a nonnegative exponent.

Return `nothing` as soon as the result would exceed `limit`.
"""
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

"""
    execution_dimensions(s::ShpilkaScheme, maxside, maxrank) -> (side, rank)

Test the executor's integer bounds on the block side and seed product count.

Use the proof's lower bounds to reject oversized rules before evaluating
their dimensions. Return the resulting pair of `Int` values if it fits, or
`nothing` if either limit is exceeded.
"""
function execution_dimensions(s::ShpilkaScheme, maxside, maxrank)
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

"""
    _materialize_length(x::Integer)::BigInt

Convert a stored integer length to the representation used by the compiler.
"""
_materialize_length(x::Integer) = big(x)

"""
    _materialize_length(x::ScaledPowerOfTwo)::BigInt

Expand a factored length into its full integer value.
"""
_materialize_length(x::ScaledPowerOfTwo) = x.coefficient * big(2)^x.exponent

"""
    scheme_coefficient(s::ExplicitScheme, term, leg, coordinate)

Read the scalar at row `coordinate` and column `term` of the selected table.

Legs 1, 2, and 3 select `U`, `V`, and `W`, respectively.
"""
function scheme_coefficient(s::ExplicitScheme, term, leg, coordinate)
    table = (s.U, s.V, s.W)[leg]
    return table[coordinate, term]
end

"""
    LoweredScheme

An executable rule with rank-one seed terms and a compiled restriction to
the matrix multiplication tensor.
"""
struct LoweredScheme <: BilinearScheme
    seed::SeedDecomposition
    witness::CompiledWitness
    @doc """
        LoweredScheme(seed::SeedDecomposition, witness::CompiledWitness)

    Combine a seed decomposition with a witness whose source dimensions
    match the seed and whose target dimensions match its matrix block side.
    """
    function LoweredScheme(seed::SeedDecomposition, witness::CompiledWitness)
        size(seed) == source_dims(witness.restriction) ||
            throw(DimensionMismatch("seed and witness differ"))
        target_dims(witness.restriction) == mm_dims(witness.side) ||
            throw(DimensionMismatch("witness has wrong target"))
        return new(seed, witness)
    end
end

"""
    block_side(s::LoweredScheme)::BigInt

Return the exact block side stored by the compiled witness.
"""
block_side(s::LoweredScheme) = s.witness.side

"""
    execution_dimensions(s::LoweredScheme, maxside, maxrank) -> (side, rank)

Return the compiled block side and seed product count as `Int` values if
both meet their integer limits, or `nothing` otherwise.
"""
function execution_dimensions(s::LoweredScheme, maxside, maxrank)
    u, r = block_side(s), rank_count(s.seed)
    return u <= maxside && r <= maxrank ? (Int(u), Int(r)) : nothing
end

"""
    scheme_coefficient(s::LoweredScheme, term, leg, coordinate)

Contract one target row of the compiled restriction with a rank-one seed term.

`term` and `coordinate` are one-based indices into the seed terms and target
rows, respectively. `leg` selects a restriction leg in `1:3`. The result is
an exact scalar such as a `Rational{BigInt}` or a `PhaseSum`.
"""
function scheme_coefficient(s::LoweredScheme, term, leg, coordinate)
    1 <= term <= rank_count(s.seed) || throw(BoundsError(s, term))
    row = s.witness.restriction.legs[leg]
    total = big(0)//1
    for (source_index, weight) in row_entries(row, coordinate)
        total += weight * rank_coefficient(s.seed, term, leg, source_index)
    end
    return total
end

"""
    lower_scheme(s; admissible_order=nothing)::LoweredScheme

Compile a Shpilka derivation into an executable restriction and seed decomposition.

An optional `admissible_order` predicate selects positive Fourier orders that
are invertible in the coefficient field.
"""
function lower_scheme(s; admissible_order=nothing)
    build, compile, decompose = s.program.operations
    witness = compile(
        build(s.derivation), s.program.power; step_bound=s.program.steps, admissible_order
    )
    a = _materialize_length(s.derivation.parameters.a)
    return LoweredScheme(decompose(a, a, witness.copies; admissible_order), witness)
end

"""
    ShpilkaCoefficient(scheme, term, leg, coordinate)

Represent a deferred coefficient of a `ShpilkaScheme`.

The term and row coordinate are one-based `BigInt` indices. The leg selects
the left input (1), right input (2), or output (3).
"""
struct ShpilkaCoefficient{S<:ShpilkaScheme}
    scheme::S
    term::BigInt
    leg::Int
    coordinate::BigInt
end

"""
    Base.show(io::IO, c::ShpilkaCoefficient)

Describe the deferred contraction by its restriction row, leg, and seed term.
"""
function Base.show(io::IO, c::ShpilkaCoefficient)
    return print(
        io,
        "row ",
        c.coordinate,
        " of restriction leg ",
        c.leg,
        " applied to polynomial seed term ",
        c.term,
    )
end

"""
    _check_shpilka_index(s, term, leg, coordinate)

Check the one-based seed term and row coordinates of a Shpilka coefficient.

Use symbolic lower bounds to accept ordinary indices and evaluate the exact
endpoint if a comparison requires it. Throw a `BoundsError` for an invalid
leg or index.
"""
function _check_shpilka_index(s, term, leg, coordinate)
    1 <= leg <= 3 || throw(BoundsError(1:3, leg))
    term >= 1 && coordinate >= 1 || throw(BoundsError(s, (term, leg, coordinate)))
    p, m = s.derivation.parameters, s.program.copies
    if ndigits(term; base=2) > 6 * m * p.q
        rank = _bounded_power(2 * _materialize_length(p.a) - 1, 6m, big(term) - 1)
        isnothing(rank) || throw(BoundsError(s, term))
    end
    if ndigits(coordinate; base=2) > 4 * m * p.q
        u = witness_side(s.program.operations[1](s.derivation), s.program.power)
        return coordinate <= u^2 || throw(BoundsError(s, coordinate))
    end
    return nothing
end

"""
    scheme_coefficient(s::ShpilkaScheme, term, leg, coordinate)::ShpilkaCoefficient

Check the indices and create a deferred coefficient for the requested seed
term and restriction row.
"""
function scheme_coefficient(s::ShpilkaScheme, term, leg, coordinate)
    _check_shpilka_index(s, term, leg, coordinate)
    return ShpilkaCoefficient(s, big(term), Int(leg), big(coordinate))
end

"""
    Base.getindex(s::BilinearScheme, term::Integer, leg::Integer, coordinate::Integer)

Access a scalar weight or a deferred coefficient at three one-based indices.

`term` selects a rank-one product. `leg` selects the left input, right input,
or output, and `coordinate` is a column-major block coordinate in that leg.
"""
function Base.getindex(s::BilinearScheme, term::Integer, leg::Integer, coordinate::Integer)
    return scheme_coefficient(s, term, leg, coordinate)
end

"""
    materialize(c::ShpilkaCoefficient; max_leg_bits::Integer)

Evaluate a deferred coefficient by composing the exact restriction and
contracting the requested row with a seed term.

`max_leg_bits` is a positive integer bound on the bit length of a source-leg
dimension. The construction must also fit the runtime's index limits.
"""
function materialize(c::ShpilkaCoefficient; max_leg_bits::Integer)
    s = c.scheme
    max_leg_bits >= 1 || throw(DomainError(max_leg_bits))
    p = s.derivation.parameters
    # Each of the three polynomial factors is at least 2^q. Check before
    # attempting to allocate either the seed dimensions or any proof nodes.
    lower = 6 * s.program.copies * p.q + 1
    lower <= max_leg_bits ||
        throw(ArgumentError("a source-leg dimension needs at least $lower bits, " *
                            "exceeding the requested budget of $max_leg_bits",),)
    lower <= typemax(Int) ||
        throw(ArgumentError("a source-leg dimension needs at least $lower bits, " *
                            "beyond addressable bit lengths on this runtime",),)
    # log2(seed_dim) = 2m log2(a²(2a-1)); use an upper bound without expanding a.
    upper = 2 * s.program.copies * (3 * (p.q + ndigits(p.q; base=2)) + 1) + 1
    upper <= max_leg_bits ||
        throw(ArgumentError("the source-leg dimension could exceed the requested budget " *
                            "(upper bound $upper bits)",),)
    return scheme_coefficient(lower_scheme(s), c.term, c.leg, c.coordinate)
end
