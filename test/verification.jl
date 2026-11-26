@testset "Explicit scheme verification" begin
    U = zeros(Int, 4, 8)
    V = zeros(Int, 4, 8)
    W = zeros(Int, 4, 8)
    for (term, (row, inner, column)) in enumerate(Iterators.product(1:2, 1:2, 1:2))
        U[row + 2 * (inner - 1), term] = 1
        V[inner + 2 * (column - 1), term] = 1
        W[row + 2 * (column - 1), term] = 1
    end

    report = NineFourths.verify_scheme(NineFourths.explicit_scheme(U, V, W))
    @test report.valid
    @test report.identity === :exact_coefficients
    @test report.exponent.base == 2
    @test report.exponent.rank == 8
    @test isnothing(report.target)
    @test isempty(report.diagnostics)

    table = TestMatrixLike(U, 1)
    indexed = BilinearScheme(table, Nemo.matrix(Nemo.ZZ, V), W)
    @test indexed.U === table
    @test indexed[1, 1, 1] == U[1, 1]
    @test verify_scheme(indexed).valid
    A = [1 2; 3 4]
    @test multiply(A, A, indexed) == A * A
    @test_throws ArgumentError BilinearScheme(TestMatrixLike(U), V, W)
    @test_throws DimensionMismatch BilinearScheme(vec(U), vec(V), vec(W))
    @test_throws DimensionMismatch BilinearScheme(U, reshape(V, 4, 8, 1), W)

    W[2, 1] = 1
    report = NineFourths.verify_scheme(NineFourths.explicit_scheme(U, V, W))
    @test !report.valid
    @test report.identity === :failed
    @test isnothing(report.exponent)
    @test occursin("input matrix units", only(report.diagnostics))

    exact = NineFourths.explicit_scheme([1 // 2 1 // 3], [3 3], [2 -2])
    @test NineFourths.verify_scheme(exact).valid

    root = NineFourths.root_of_unity(4)
    algebraic = NineFourths.explicit_scheme([root;;], [inv(root);;], [1;;])
    @test NineFourths.verify_scheme(algebraic).valid

    # Fixed-width arithmetic would wrap this coefficient to 1.
    wrapped = NineFourths.explicit_scheme([typemin(Int) 1], [2 1], [1 1])
    @test !NineFourths.verify_scheme(wrapped).valid
end

@testset "Lowered scheme verification limits and indices" begin
    seed = NineFourths.seed_decomposition(1, 2)
    nodes = [NineFourths.DerivationNode(1, 2, 2 // 1, :baseline, ())]
    witness = NineFourths.compile_witness(nodes, 1)
    scheme = NineFourths.LoweredScheme(seed, witness)
    report = NineFourths.verify_scheme(scheme; max_terms=0)
    @test !report.valid
    @test report.identity === :unchecked
    @test occursin("verification budget", only(report.diagnostics))
    @test_throws DomainError NineFourths.verify_scheme(scheme; max_terms=-1)

    x, y, z = witness.restriction.legs
    invalid = NineFourths.selection_map(z.in_dim, z.out_dim, _ -> z.in_dim + 1)
    change = NineFourths.TensorRestriction(x, y, invalid)
    bad_witness = NineFourths.CompiledWitness(witness.side, witness.copies, change)
    report = NineFourths.verify_scheme(NineFourths.LoweredScheme(seed, bad_witness))
    @test !report.valid
    @test report.identity === :failed
    @test occursin("outside the seed", only(report.diagnostics))

    zero_output = NineFourths.selection_map(z.in_dim, z.out_dim, _ -> 0)
    change = NineFourths.TensorRestriction(x, y, zero_output)
    bad_witness = NineFourths.CompiledWitness(witness.side, witness.copies, change)
    report = NineFourths.verify_scheme(NineFourths.LoweredScheme(seed, bad_witness))
    @test !report.valid
    @test report.identity === :failed
    @test occursin("input matrix units", only(report.diagnostics))
end

@testset "Shpilka scheme verification" begin
    scheme = NineFourths.multiplication_scheme()
    report = NineFourths.verify_scheme(scheme)
    @test report.valid
    @test report.identity === :symbolic_restriction
    @test report.target == 5 // 2
    @test 9 // 4 < report.exponent == 2385 // 1042 <= report.target
    @test isempty(report.diagnostics)

    target = 9 // 4 + 1 // big(10)^20
    report = NineFourths.verify_scheme(NineFourths.multiplication_scheme(target))
    @test report.valid
    @test report.exponent <= target

    program = scheme.program
    corrupted_program = NineFourths.ShpilkaProgram(
        program.steps,
        program.log_length,
        program.power,
        program.copies - 1,
        program.overhead,
        program.operations,
    )
    corrupted = NineFourths.ShpilkaScheme(scheme.derivation, corrupted_program)
    report = NineFourths.verify_scheme(corrupted)
    @test !report.valid
    @test report.identity === :failed
    @test occursin("copy budget", only(report.diagnostics))

    reordered_program = NineFourths.ShpilkaProgram(
        program.steps,
        program.log_length,
        program.power,
        program.copies,
        program.overhead,
        reverse(program.operations),
    )
    reordered = NineFourths.ShpilkaScheme(scheme.derivation, reordered_program)
    report = NineFourths.verify_scheme(reordered)
    @test !report.valid
    @test report.identity === :failed
    @test occursin("executable construction", only(report.diagnostics))

    altered_seed = (a, b, m) -> NineFourths.seed_decomposition(a, b, m - 1)
    altered_program = NineFourths.ShpilkaProgram(
        program.steps,
        program.log_length,
        program.power,
        program.copies,
        program.overhead,
        (program.operations[1], program.operations[2], altered_seed),
    )
    altered = NineFourths.ShpilkaScheme(scheme.derivation, altered_program)
    report = NineFourths.verify_scheme(altered)
    @test !report.valid
    @test report.identity === :failed
    @test occursin("balanced polynomial seed", only(report.diagnostics))
end
