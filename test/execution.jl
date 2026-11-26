struct TestScalarScheme end

NineFourths.block_side(::TestScalarScheme) = 1
NineFourths.scheme_coefficient(::TestScalarScheme, term, leg, coordinate) = 1
function NineFourths.execution_dimensions(::TestScalarScheme, max_side, max_rank)
    return min(max_side, max_rank) >= 1 ? (1, 1) : nothing
end

@testset "Exact matrix multiplication" begin
    # Strassen's seven products. Rows are the column-major block coordinates.
    U = [1 0 1 0 1 -1 0; 0 1 0 0 0 1 0; 0 0 0 0 1 0 1; 1 1 0 1 0 0 -1]
    V = [1 1 0 -1 0 1 0; 0 0 0 1 0 0 1; 0 0 1 0 0 1 0; 1 0 -1 0 1 0 1]
    W = [1 0 0 1 -1 0 1; 0 1 0 1 0 0 0; 0 0 1 0 1 0 0; 1 -1 1 0 0 1 0]
    strassen = NineFourths.explicit_scheme(U, V, W)

    @testset "Strict scheme layers" begin
        for n in (1, 2, 3, 4, 5)
            A = [2i - j for i in 1:n, j in 1:n]
            B = [(i - 2j)^2 for i in 1:n, j in 1:n]
            expected = BigInt.(A) * BigInt.(B)
            old_A, old_B = copy(A), copy(B)
            C = NineFourths.multiply(A, B, strassen)
            @test C == expected
            @test C isa Matrix{BigInt}
            @test (A, B) == (old_A, old_B)
        end

        large = typemax(Int)
        A = [large -large; 1 large]
        B = [large 3; -2 large]
        @test NineFourths.multiply(A, B, strassen) == BigInt.(A) * BigInt.(B)

        A = [1//3 2; -2 1//2]
        C = NineFourths.multiply(view(A, :, :), B, strassen)
        @test C isa Matrix{Rational{BigInt}}
        @test C == Rational{BigInt}.(A) * BigInt.(B)
        @test NineFourths.multiply(TestMatrixLike(A), B, strassen) == C
        @test NineFourths.multiply(TestMatrixLike(A), TestMatrixLike(B), strassen) == C

        single = NineFourths.explicit_scheme([2;;], [3;;], [1//6;;])
        @test NineFourths.multiply(A, B, single) == C
        @test multiply(A, B, TestScalarScheme()) == C
        @test_throws NineFourths.ExecutionInfeasible multiply(
            A, B, TestScalarScheme(); max_coefficient_visits=0
        )

        algebraic_U = Matrix{NineFourths.ExactScalar}(Rational{BigInt}.(U))
        algebraic_V = Matrix{NineFourths.ExactScalar}(Rational{BigInt}.(V))
        root = NineFourths.root_of_unity(4)
        inverse_root = NineFourths.root_of_unity(4, -1)
        for row in axes(U, 1)
            algebraic_U[row, 1] *= root
            algebraic_V[row, 1] *= inverse_root
        end
        algebraic = NineFourths.explicit_scheme(algebraic_U, algebraic_V, W)
        @test NineFourths.multiply(A, B, algebraic) == C
    end

    @testset "Feasibility and explicit fallback" begin
        A = [1 2 3; 4 5 6; 7 8 9]
        B = [9 8 7; 6 5 4; 3 2 1]
        expected = BigInt.(A) * BigInt.(B)
        error = try
            NineFourths.multiply(A, B, strassen; max_coefficient_visits=671)
        catch exception
            exception
        end
        @test error isa NineFourths.ExecutionInfeasible
        @test error.reason == :coefficient_visits
        @test error.input_size == 3
        @test error.block_side == 2
        @test NineFourths.multiply(A, B, strassen; max_coefficient_visits=672) == expected
        @test NineFourths.multiply(
            A, B, strassen; max_coefficient_visits=671, fallback=:classical
        ) == expected

        @test_throws NineFourths.ExecutionInfeasible NineFourths.multiply(
            A, B, strassen; max_workspace_entries=28
        )
        @test NineFourths.multiply(
            A, B, strassen; max_workspace_entries=28, fallback=:classical
        ) == expected

        shpilka = NineFourths.multiplication_scheme()
        @test_throws NineFourths.ExecutionInfeasible NineFourths.multiply(A, B, shpilka)
        @test_throws "exceeding the largest addressable side" NineFourths.multiply(
            A, B, shpilka
        )
        @test NineFourths.multiply(A, B, shpilka; fallback=:classical) == expected

        empty = Matrix{Rational{Int}}(undef, 0, 0)
        @test NineFourths.multiply(empty, empty, strassen) == empty
        C = NineFourths.multiply(empty, empty, strassen; fallback=:classical)
        @test size(C) == (0, 0)
        @test C isa Matrix{Rational{BigInt}}

        @test_throws DimensionMismatch NineFourths.multiply(
            A, B[1:2, 1:2], strassen; fallback=:classical
        )
        @test_throws DimensionMismatch NineFourths.multiply(
            A[:, 1:2], B[:, 1:2], strassen; fallback=:classical
        )
        for invalid in (1, [1, 2, 3], reshape(B, 3, 3, 1))
            @test_throws DimensionMismatch NineFourths.multiply(invalid, B, strassen)
            @test_throws DimensionMismatch NineFourths.multiply(
                A, invalid, strassen; fallback=:classical
            )
        end
        @test NineFourths.multiply(
            Float64.(A), B, strassen; fallback=:classical, max_coefficient_visits=0
        ) == Float64.(expected)
        @test_throws DomainError NineFourths.multiply(
            [1//0;;], [1;;], strassen; fallback=:classical, max_coefficient_visits=0
        )
        @test_throws ArgumentError NineFourths.multiply(A, B, strassen; fallback=:unknown)
    end
end
