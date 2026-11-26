@testset "Optional positional target and compact indexed scheme" begin
    default = multiplication_scheme()
    @test default isa BilinearScheme
    @test default isa NineFourths.ShpilkaScheme
    @test sprint(show, default) == "multiplication_scheme(5//2)"
    @test occursin("r^(N²)", sprint(show, MIME"text/plain"(), default))
    @test default.derivation.parameters.target == 5//2
    @test default.derivation.parameters.a == big(2)^264
    @test multiplication_scheme(23//10).derivation.parameters.q == 6400
    @test multiplication_scheme(Nemo.QQ(5//2)).derivation.parameters.target == 5//2
    @test multiplication_scheme(Nemo.ZZ(3)).derivation.parameters.target == 3
    @test_throws MethodError multiplication_scheme(2.5)
    @test_throws DomainError multiplication_scheme(9//4)
    @test_throws DomainError multiplication_scheme(2)
    @test_throws MethodError multiplication_scheme(; target_exponent=5//2)
    entry = default[1, 3, 1]
    @test entry isa NineFourths.ShpilkaCoefficient
    @test entry.leg == 3 && entry.coordinate == 1
    @test occursin("restriction leg 3", sprint(show, entry))
    @test_throws ArgumentError NineFourths.materialize(entry; max_leg_bits=1_000_000)
    @test_throws "beyond addressable bit lengths" NineFourths.materialize(
        entry; max_leg_bits=big(10)^100
    )
    @test_throws BoundsError default[0, 1, 1]
    @test_throws BoundsError default[1, 4, 1]
    @test_throws BoundsError default[1, 2, 0]
end

@testset "Executable polynomial seed to exact matrix multiplication" begin
    # Lemma 3.8, using the very same seed and witness contraction as §6.
    # This baseline has block side 4 and 64 products.
    nodes = [NineFourths.DerivationNode(1, 2, 2//1, :baseline, ())]
    witness = NineFourths.compile_witness(nodes, 1)
    scheme = NineFourths.LoweredScheme(NineFourths.seed_decomposition(1, 2), witness)
    report = verify_scheme(scheme)
    @test report.valid && report.identity === :exact_coefficients
    A = reshape(BigInt.(1:16), 4, 4)
    B = [big(i - 2j)//(i + j) for i in 1:4, j in 1:4]
    @test multiply(A, B, scheme) == A * B
end
