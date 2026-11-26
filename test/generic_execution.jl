# These scalars have only a value-level field interface. In particular, they
# lack zero(T), one(T), conversion to Julia numbers, and array multiplication.
# The constructor accepts any `Rational` and stores it as `Rational{BigInt}`.
struct TestValueRational
    value::Rational{BigInt}
    TestValueRational(value::Rational) = new(value)
end

# Build a `TestValueRational` from integer numerator and denominator values.
test_value_q(n::Integer, d::Integer=1) = TestValueRational(big(n) // big(d))
Base.zero(::TestValueRational) = test_value_q(0)
Base.one(::TestValueRational) = test_value_q(1)
Base.iszero(x::TestValueRational) = iszero(x.value)
Base.inv(x::TestValueRational) = TestValueRational(inv(x.value))
Base.:-(x::TestValueRational) = TestValueRational(-x.value)
Base.:+(x::TestValueRational, y::TestValueRational) = TestValueRational(x.value + y.value)
Base.:-(x::TestValueRational, y::TestValueRational) = TestValueRational(x.value - y.value)
Base.:*(x::TestValueRational, y::TestValueRational) = TestValueRational(x.value * y.value)
Base.:(==)(x::TestValueRational, y::TestValueRational) = x.value == y.value

# A callable prime field fixture. `modulus::Int` is prime.
struct TestPrimeParent
    modulus::Int
end

# A field element with an `Int` representative in `0:(field.modulus - 1)`.
struct TestValueResidue
    field::TestPrimeParent
    value::Int
end

# Coerce an integer to a `TestValueResidue` belonging to `F`.
(F::TestPrimeParent)(n::Integer) = TestValueResidue(F, Int(mod(n, F.modulus)))
Base.zero(F::TestPrimeParent) = F(0)
Base.one(F::TestPrimeParent) = F(1)
Base.zero(x::TestValueResidue) = zero(x.field)
Base.one(x::TestValueResidue) = one(x.field)
Base.iszero(x::TestValueResidue) = iszero(x.value)
Base.inv(x::TestValueResidue) = x.field(invmod(x.value, x.field.modulus))
Base.:-(x::TestValueResidue) = x.field(-x.value)

# `op` maps two `Int` representatives to an integer, as `+`, `-`, or `*` does.
# `x` and `y` are `TestValueResidue` elements of the same parent. Return a
# residue of that parent.
function test_residue_binary(op, x, y)
    x.field == y.field || throw(ArgumentError("incompatible residue parents"))
    return x.field(op(x.value, y.value))
end

Base.:+(x::TestValueResidue, y::TestValueResidue) = test_residue_binary(+, x, y)
Base.:-(x::TestValueResidue, y::TestValueResidue) = test_residue_binary(-, x, y)
Base.:*(x::TestValueResidue, y::TestValueResidue) = test_residue_binary(*, x, y)

function Base.:(==)(x::TestValueResidue, y::TestValueResidue)
    return x.field == y.field && x.value == y.value
end

# A modulo-five scalar whose `Integer` subtype tests field inference.
# Its constructor accepts an `Integer` and stores the reduced `Int` value.
struct TestIntegerResidue <: Integer
    value::Int
    TestIntegerResidue(value::Integer) = new(mod(value, 5))
end

TestIntegerResidue(x::TestIntegerResidue) = x
Base.zero(::TestIntegerResidue) = TestIntegerResidue(0)
Base.one(::TestIntegerResidue) = TestIntegerResidue(1)
Base.iszero(x::TestIntegerResidue) = iszero(x.value)
Base.inv(x::TestIntegerResidue) = TestIntegerResidue(invmod(x.value, 5))
Base.:-(x::TestIntegerResidue) = TestIntegerResidue(-x.value)

function Base.:+(x::TestIntegerResidue, y::TestIntegerResidue)
    return TestIntegerResidue(x.value + y.value)
end

function Base.:-(x::TestIntegerResidue, y::TestIntegerResidue)
    return TestIntegerResidue(x.value - y.value)
end

function Base.:*(x::TestIntegerResidue, y::TestIntegerResidue)
    return TestIntegerResidue(x.value * y.value)
end

Base.:(==)(x::TestIntegerResidue, y::TestIntegerResidue) = x.value == y.value

# A modulo-five scalar with an `Int` representative. Tests pass a callable
# that maps `Integer` inputs to this type to supply field identities.
struct TestCallableScalar
    value::Int
    TestCallableScalar(value::Integer) = new(mod(value, 5))
end

Base.inv(x::TestCallableScalar) = TestCallableScalar(invmod(x.value, 5))
Base.:-(x::TestCallableScalar) = TestCallableScalar(-x.value)

function Base.:+(x::TestCallableScalar, y::TestCallableScalar)
    return TestCallableScalar(x.value + y.value)
end

function Base.:-(x::TestCallableScalar, y::TestCallableScalar)
    return TestCallableScalar(x.value - y.value)
end

function Base.:*(x::TestCallableScalar, y::TestCallableScalar)
    return TestCallableScalar(x.value * y.value)
end

Base.:(==)(x::TestCallableScalar, y::TestCallableScalar) = x.value == y.value

# `A` and `B` are one-based matrix-like inputs of size `m×k` and `k×n` over
# the same field. `additive_identity` is a zero element of that field.
# Return the `m×n` Julia `Matrix` of scalar dot products.
function field_product_reference(A, B, additive_identity)
    m, k = size(A)
    n = last(size(B))
    # Integer output indices `(i, j)` select one scalar dot product.
    dot_entry(i, j) = foldl(+, (A[i, h] * B[h, j] for h in 1:k); init=additive_identity)
    return [dot_entry(i, j) for i in 1:m, j in 1:n]
end

# Return an `ExplicitScheme` with three 4×7 coefficient tables. The `Bool`
# `scaled` selects rational rescaling of the left and output weights.
function generic_strassen(; scaled=false)
    U = [1 0 1 0 1 -1 0; 0 1 0 0 0 1 0; 0 0 0 0 1 0 1; 1 1 0 1 0 0 -1]
    V = [1 1 0 -1 0 1 0; 0 0 0 1 0 0 1; 0 0 1 0 0 1 0; 1 0 -1 0 1 0 1]
    W = [1 0 0 1 -1 0 1; 0 1 0 1 0 0 0; 0 0 1 0 1 0 0; 1 -1 1 0 0 1 0]
    if scaled
        # Rescale each left form and the matching output weight by inverse
        # factors. This leaves Strassen's identity but requires division.
        weights = [1//2 2//3 -3//2 3//2 1//3 -1//2 2//1]
        return NineFourths.explicit_scheme(U .* weights, V, W ./ weights)
    end
    return NineFourths.explicit_scheme(U, V, W)
end

@testset "Compiled Shpilka baseline over finite fields" begin
    nodes = [NineFourths.DerivationNode(1, 2, 2 // 1, :baseline, ())]
    witness = NineFourths.compile_witness(nodes, 1)
    scheme = NineFourths.LoweredScheme(NineFourths.seed_decomposition(1, 2), witness)
    extension, generator = Nemo.finite_field(2, 2, :u)
    # Each case holds a Nemo field parent, an integer or extension generator
    # for the input entries, and the integer product dimensions `(m, k, n)`.
    cases = (
        (Nemo.GF(2), 0, (3, 5, 2)),
        (Nemo.GF(3), 0, (5, 2, 3)),
        (Nemo.Native.GF(5), 0, (2, 3, 5)),
        (extension, generator, (3, 5, 4)),
    )
    for (F, a, (m, k, n)) in cases
        A = [F(i - 2j) + F(a) * F(i * j + j) for i in 1:m, j in 1:k]
        B = [F(i + 3j) + F(a) * F(i + j + 1) for i in 1:k, j in 1:n]
        expected = field_product_reference(A, B, zero(F))
        native_A, native_B = Nemo.matrix(F, A), Nemo.matrix(F, B)
        for (left, right) in ((A, B), (native_A, native_B), (native_A, B))
            C = multiply(left, right, scheme)
            @test C == expected
            @test C isa Matrix{typeof(zero(F))}
            @test all(x -> parent(x) === F, C)
        end
    end

    # Characteristic two replaces two Fourier samples with three in each
    # orientation, enlarging the rank from 2^6 to 3^6.
    F2 = Nemo.GF(2)
    a = [one(F2);;]
    @test_throws NineFourths.ExecutionInfeasible multiply(
        a, a, scheme; max_coefficient_visits=500
    )
    @test multiply(a, a, scheme; max_coefficient_visits=500, fallback=:classical) == a

    padded_seed = NineFourths.seed_decomposition(1, 2; admissible_order=isodd)
    specialized = NineFourths.LoweredScheme(padded_seed, witness)
    for F in (Nemo.GF(3), Nemo.GF(5))
        a = [one(F);;]
        @test multiply(a, a, specialized; max_coefficient_visits=3 * 64) == a
    end
    @test_throws NineFourths.ExecutionInfeasible multiply(
        [one(F2);;], [one(F2);;], specialized; max_coefficient_visits=3 * 64
    )
end

@testset "Fourier separation with an admissible odd order" begin
    transition = NineFourths.midpoint_transition(1, 2, 1, 1, 2)
    t = NineFourths.root_of_unity(3)
    restriction = NineFourths.transition_restriction(transition, 2, t; admissible_order=3)
    for leg_map in restriction.legs
        entries = collect(NineFourths.row_entries(leg_map, 1))
        @test length(entries) == 3^6
        @test all(==(1 // 9) ∘ last, entries)
        @test all(entries) do (column, _)
            all(<(3), digits(mod(column - 1, 4^6); base=4, pad=6))
        end
        @test iszero(leg_map[1, first(first(entries)) + 3])
    end

    # The physical coordinates still use radix 4. The tensor contraction
    # keeps the selected type, cancels the other label, and retains its
    # positive-degree term when the matrix digits compensate for the label.
    changed_matrix_column = 1 + 2^6 * 81 * 4
    for (rows, expected) in
        (((1, 1, 1), 1), ((2, 1, 1), 0), ((2, 1, changed_matrix_column), t))
        entries = map(NineFourths.row_entries, restriction.legs, rows)
        actual = sum(zip(entries...); init=0 // big(1)) do terms
            source = scalar_midpoint_source_coefficient(map(first, terms))
            return iszero(source) ? 0 // big(1) : prod(map(last, terms))
        end
        @test actual == expected
    end

    single = NineFourths.midpoint_transition(2, 4, 1, 1, 1)
    no_extra_copy = NineFourths.transition_restriction(single, 2, t; admissible_order=1)
    for leg_map in no_extra_copy.legs
        column, coefficient = only(NineFourths.row_entries(leg_map, 1))
        @test mod(column - 1, 2^6) == 0
        @test coefficient == 1
        @test iszero(leg_map[1, column + 1])
    end

    first_stage = NineFourths.transition_restriction(single, 1, t; admissible_order=1)
    row = 64 * (sector_test_pack((1, 1, 5, 1, 4, 5), (8, 2, 10, 2, 8, 10)) - 1) + 1
    weight = inv(t)
    @test Dict(NineFourths.row_entries(first_stage.legs[2], row)) ==
        Dict(65 => -weight, (64 * 1600 * 4 + 1) => weight)

    # A degree-six stage cannot average seven evaluations in characteristic
    # seven. Eight evaluations still recover its constant coefficient.
    F7 = Nemo.GF(7)
    # `Integer -> Bool` predicate for orders invertible in the test field.
    admissible_order = order -> !iszero(F7(order))
    interpolated = NineFourths._interpolated_phase(single, 1, 1; admissible_order)
    @test interpolated.points == 8
    @test all(1:8) do point
        inverse_sample = inv(NineFourths.root_of_unity(8, point))
        interpolated.restriction.legs[2][row, 8 * (65 - 1) + point] == -inverse_sample
    end

    tripling = NineFourths.tripling_transition(1, 1, 1, 0, 0)
    normalized = NineFourths._interpolated_phase(tripling, 1, 1; admissible_order)
    @test normalized.points == 8
    @test all(point -> normalized.restriction.legs[1][1, point] == 1 // 8, 1:8)
    @test all(point -> normalized.restriction.legs[2][1, point] == 1, 1:8)
end

@testset "Rectangular Strassen over value-level fields" begin
    strassen = generic_strassen()
    scaled = generic_strassen(; scaled=true)
    for (m, k, n) in ((7, 3, 5), (3, 5, 9), (2, 9, 3))
        A = [test_value_q(2i - j, i + j) for i in 1:m, j in 1:k]
        B = [test_value_q(i - 2j, 2i + j) for i in 1:k, j in 1:n]
        reference = field_product_reference(A, B, test_value_q(0))
        original_A, original_B = copy(A), copy(B)
        for scheme in (strassen, scaled)
            C = multiply(A, B, scheme)
            @test C isa Matrix{TestValueRational}
            @test C == reference
        end
        @test A == original_A && B == original_B
    end

    F = TestPrimeParent(5)
    A = [F(i + 2j) for i in 1:5, j in 1:3]
    B = [F(2i - j) for i in 1:3, j in 1:7]
    expected = field_product_reference(A, B, zero(F))
    C = multiply(A, B, scaled)
    @test C == expected
    @test C isa Matrix{TestValueResidue}
    @test_throws NineFourths.ExecutionInfeasible multiply(
        A, B, scaled; max_coefficient_visits=0
    )
    C = multiply(A, B, scaled; fallback=:classical, max_coefficient_visits=0)
    @test C == expected
    @test C isa Matrix{TestValueResidue}
    @test_throws ArgumentError multiply(A, B, scaled; fallback=:automatic)
    @test_throws DimensionMismatch multiply(A, B[1:2, :], scaled; fallback=:classical)

    F2 = Nemo.GF(2)
    left = F2.([1 0 1; 0 1 1])
    right = F2.([1 1; 1 0; 0 1])
    @test_throws NineFourths.CoefficientIncompatible multiply(left, right, scaled)
    @test multiply(left, right, scaled; fallback=:classical) ==
        field_product_reference(left, right, zero(F2))
end

@testset "Runtime parents and compatible empty dimensions" begin
    scheme = generic_strassen()
    F = Nemo.GF(5)
    other = Nemo.GF(3)
    # `Matrix{Any}` makes field inference inspect the entries of the matrix.
    A = Any[F(1) F(2) F(0); F(4) F(3) F(1)]
    B = F.([1 1; 2 4; 3 0])
    C = multiply(A, B, scheme)
    @test C == field_product_reference(A, B, zero(F))
    @test C isa Matrix{typeof(zero(F))}
    @test multiply(TestMatrixLike(A), B, scheme) == C
    mixed = Any[F(1) 2 F(0); 4 F(3) 1//1]
    @test multiply(mixed, B, scheme) == C
    incompatible = copy(A)
    incompatible[end] = other(1)
    @test_throws Union{ArgumentError,DomainError} multiply(incompatible, B, scheme)
    @test_throws Union{ArgumentError,DomainError} multiply(
        A, other.([1 1; 2 1; 0 0]), scheme; fallback=:classical
    )
    @test_throws Union{ArgumentError,DomainError} multiply(A, B, scheme; field=other)

    a = Nemo.matrix(Nemo.QQ, [1//2 2//3 3//4; -1//3 1//4 0//1])
    b = Nemo.QQ.([2//3 0//1; 1//2 -1//3; 2//1 1//4])
    result = multiply(a, b, generic_strassen(; scaled=true))
    @test result isa Matrix{typeof(zero(Nemo.QQ))}
    @test result == field_product_reference(a, b, zero(Nemo.QQ))

    for (m, k, n) in ((0, 3, 5), (3, 5, 0), (3, 0, 5), (0, 0, 0))
        left = fill(0 // 1, m, k)
        right = fill(0 // 1, k, n)
        zero_product = multiply(left, right, scheme; max_coefficient_visits=0)
        @test size(zero_product) == (m, n)
        @test zero_product isa Matrix{Rational{BigInt}}
        @test all(iszero, zero_product)
    end

    FqElement = typeof(zero(F))
    left, right = Matrix{FqElement}(undef, 3, 0), Matrix{FqElement}(undef, 0, 5)
    @test_throws Union{ArgumentError,DomainError} multiply(left, right, scheme)
    for (left, right, keywords) in (
        (left, right, (; field=F)),
        (TestMatrixLike(left), right, (; field=F)),
        (Nemo.zero_matrix(F, 3, 0), Nemo.zero_matrix(F, 0, 5), (;)),
    )
        zero_product = multiply(left, right, scheme; keywords...)
        @test size(zero_product) == (3, 5)
        @test zero_product isa Matrix{FqElement}
        @test all(x -> iszero(x) && parent(x) === F, zero_product)
    end

    runtime = TestPrimeParent(7)
    left = Matrix{TestValueResidue}(undef, 2, 0)
    right = Matrix{TestValueResidue}(undef, 0, 4)
    @test_throws Union{ArgumentError,DomainError} multiply(left, right, scheme)
    @test multiply(left, right, scheme; field=runtime) == fill(zero(runtime), 2, 4)
    @test_throws DimensionMismatch multiply(
        left, fill(one(runtime), 1, 4), scheme; field=runtime, fallback=:classical
    )

    left = Matrix{TestValueRational}(undef, 2, 0)
    right = Matrix{TestValueRational}(undef, 0, 3)
    @test multiply(left, right, scheme; field=test_value_q(2, 3)) ==
        fill(test_value_q(0), 2, 3)
end

@testset "Custom scalar identity and widening rules" begin
    scheme = generic_strassen(; scaled=true)
    residue = TestIntegerResidue(Int16(7))
    @test TestIntegerResidue(residue) === residue
    # Each variant holds a scalar type and a named tuple of execution keywords.
    variants = (
        (TestIntegerResidue, (;)),
        (TestCallableScalar, (; field=n -> TestCallableScalar(n))),
    )
    @testset "$element" for (element, kwargs) in variants
        A = [element(i - 2j) for i in 1:3, j in 1:2]
        B = [element(2i + j) for i in 1:2, j in 1:5]
        expected = field_product_reference(A, B, element(0))
        C = multiply(A, B, scheme; kwargs...)
        @test C isa Matrix{element}
        @test C == expected
    end

    large = typemax(Int)
    A = [large -large large; -large large large]
    B = [large//2 1//3; -large//2 large//5; 3//4 large//7]
    inputs = NineFourths._field_inputs(A, B)
    @test inputs.left === A && inputs.right === B
    expected = Rational{BigInt}.(A) * Rational{BigInt}.(B)
    C = multiply(A, B, scheme; fallback=:classical, max_coefficient_visits=0)
    @test C isa Matrix{Rational{BigInt}}
    @test C == expected
    @test multiply(
        A, TestMatrixLike(B), scheme; fallback=:classical, max_coefficient_visits=0
    ) == expected
end

@testset "Native float and complex arithmetic" begin
    scheme = generic_strassen(; scaled=true)
    for T in (Float32, Float64, ComplexF32, ComplexF64)
        A = [T <: Complex ? T(i / 3, j / 7) : T(i / 3 + j / 7) for i in 1:5, j in 1:3]
        B = [T <: Complex ? T(i / 5, -j / 2) : T(i / 5 - j / 2) for i in 1:3, j in 1:7]
        C = multiply(A, B, scheme)
        @test C isa Matrix{T}
        @test C ≈ field_product_reference(A, B, zero(T))
    end

    # Applying a factor of 1/2 to the smallest Float32 rounds to zero.
    # Exact rational intermediates followed by one conversion would keep it.
    subnormal = nextfloat(0.0f0)
    scaled_product = NineFourths.explicit_scheme([1//2;;], [1;;], [2;;])
    C = multiply([subnormal;;], [1.0f0;;], scaled_product)
    @test C isa Matrix{Float32}
    @test iszero(only(C))

    # The ratio is finite although its numerator and denominator, taken
    # separately, exceed the Float32 range.
    x = big(2)^200 // (big(2)^200 + 1)
    reciprocal = BilinearScheme([x;;], [1;;], [inv(x);;])
    @test multiply(Float32[2;;], Float32[3;;], reciprocal) == Float32[6;;]

    zero_product = multiply(
        Matrix{Float32}(undef, 2, 0), Matrix{Float32}(undef, 0, 3), scheme; field=Float32
    )
    @test zero_product == zeros(Float32, 2, 3)
    @test zero_product isa Matrix{Float32}
end

@testset "Native algebraic number field and coefficient tables" begin
    _, x = Nemo.polynomial_ring(Nemo.QQ, :x)
    K, a = Nemo.number_field(x^2 - 2, :a)
    @test a^2 == K(2)
    bare = generic_strassen()
    # Scale each input form by a, then cancel a inside the same number field.
    native = BilinearScheme(
        map(w -> K(w) * a, bare.U), map(K, bare.V), map(w -> K(w) * inv(a), bare.W)
    )
    @test native[1, 1, 1] == a
    @test verify_scheme(native).identity == :exact_coefficients
    A = [K(i) + a * j for i in 1:5, j in 1:3]
    B = [a * i - K(j) for i in 1:3, j in 1:7]
    reference = field_product_reference(A, B, K(0))
    result = multiply(Nemo.matrix(K, A), B, native)
    @test result == reference
    @test all(value -> parent(value) === K, result)

    scalar = BilinearScheme([1;;], [1;;], [1;;])
    for left in ([Nemo.QQ(1//2);;], Nemo.matrix(Nemo.QQ, [1//2;;]))
        @test multiply(left, [a;;], scalar; field=K) == [a / 2;;]
        @test multiply(left, [a;;], scalar) == [a / 2;;]
    end
    F = Nemo.GF(5)
    native_weights = BilinearScheme(Nemo.matrix(F, [F(2);;]), [one(F);;], [F(3);;])
    @test verify_scheme(native_weights).valid
    wrong_weights = BilinearScheme([F(2);;], [one(F);;], [F(4);;])
    @test !verify_scheme(wrong_weights).valid
    @test_throws Union{ArgumentError,DomainError} multiply(
        [Nemo.QQ(1//5);;], [F(4);;], scalar; field=F, fallback=:classical
    )

    scaled = BilinearScheme([1//2;;], [2;;], [1;;])
    integer_product = multiply([Nemo.ZZ(7);;], [Nemo.ZZ(3);;], scaled)
    @test integer_product isa Matrix{Nemo.ZZRingElem}
    @test integer_product == [Nemo.ZZ(21);;]
    mixed_product = multiply([Nemo.ZZ(3);;], [1//2;;], scalar)
    @test mixed_product isa Matrix{Nemo.QQFieldElem}
    @test mixed_product == [Nemo.QQ(3//2);;]

    # Explicit schemes may mix symbolic roots with concrete algebraic numbers.
    symbolic = NineFourths.root_of_unity(4)
    concrete = Nemo.root_of_unity(NineFourths.ALGEBRAIC_NUMBERS, 4, -1)
    rotation = BilinearScheme([symbolic;;], [concrete;;], [1;;])
    @test multiply([3 4], [2; 5;;], rotation) == [26;;]
    gaussian = complex(big(1)//2, big(1)//3)
    for inverse_i in (concrete, complex(0//1, -1//1))
        rule = BilinearScheme([symbolic;;], [inverse_i;;], [1;;])
        @test verify_scheme(rule).valid
        @test multiply([gaussian;;], [gaussian;;], rule) == [gaussian^2;;]
    end
end
