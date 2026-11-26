@testset "Exact coefficients" begin
    @test NineFourths.to_exact(typemax(Int)) + 1 == big(typemax(Int)) + 1
    @test NineFourths.rational_result(2//3) isa Rational{BigInt}
    @test NineFourths.root_of_unity(1) == 1
    @test NineFourths.root_of_unity(12, -6) == -1
    @test NineFourths.root_of_unity(12, 2) == NineFourths.root_of_unity(18, 3)

    root = NineFourths.root_of_unity(12)
    other_root = NineFourths.root_of_unity(18)
    @test root * other_root == NineFourths.root_of_unity(36, 5)
    @test NineFourths.rational_result(root^3 + root^(-3) + big(2)//3) == 2//3
    @test_throws DomainError NineFourths.rational_result(root)
    @test_throws ArgumentError NineFourths.root_of_unity(0)

    large_order = big(2)^128
    large_root = NineFourths.root_of_unity(large_order)
    third_root = NineFourths.root_of_unity(3)
    @test large_root^(large_order ÷ 2) == -1
    @test NineFourths.rational_result(1 + third_root + third_root^2) == 0
    @test iszero(large_root + large_root * third_root + large_root * third_root^2)
    @test NineFourths.rational_result(
        1 + large_root + large_root * third_root + large_root * third_root^2
    ) == 1

    rational = big(2)//3
    algebraic = NineFourths.ALGEBRAIC_NUMBERS(big(1)//3)
    @test NineFourths.rational_result(algebraic + rational) == 1
    @test NineFourths.rational_result(algebraic * rational) == 2//9
    @test NineFourths.rational_result(algebraic * root * inv(root)) == 1//3
    @test algebraic * large_root == large_root / 3
end

@testset "Polynomial multiplication rank decomposition" begin
    decomposition = NineFourths.polynomial_decomposition(4, 3)
    @test size(decomposition) == (4, 3, 6)
    @test NineFourths.rank_count(decomposition) == 6
    for k in 1:6, j in 1:3, i in 1:4
        coefficient = sum(1:NineFourths.rank_count(decomposition)) do term
            NineFourths.rank_coefficient(decomposition, term, 1, i) *
            NineFourths.rank_coefficient(decomposition, term, 2, j) *
            NineFourths.rank_coefficient(decomposition, term, 3, k)
        end
        @test coefficient == (i + j - 1 == k)
    end
    @test_throws BoundsError NineFourths.rank_coefficient(decomposition, 1, 3, 7)

    large_length = big(2)^128
    large = NineFourths.polynomial_decomposition(1, large_length)
    @test NineFourths.rank_coefficient(large, 2, 3, 2) ==
        NineFourths.root_of_unity(large_length, -1) / large_length
end

# `a` and `b` are integer polynomial lengths. `coordinates` is a triple of
# one-based integer leg indices. Return the seed tensor coefficient `0` or `1`.
function seed_tensor_entry(a, b, coordinates)
    dimensions = (a, b, a + b - 1)
    remaining = coordinates .- 1
    for permutation in NineFourths.LEG_PERMUTATIONS
        digits = ntuple(leg -> divrem(remaining[leg], dimensions[permutation[leg]]), 3)
        original = ntuple(leg -> last(digits[findfirst(==(leg), permutation)]), 3)
        original[1] + original[2] == original[3] || return 0
        remaining = first.(digits)
    end
    return 1
end

@testset "Balanced seed rank decomposition" begin
    seed = NineFourths.seed_decomposition(1, 2)
    @test size(seed) == (16, 16, 16)
    @test NineFourths.rank_count(seed) == 2^6
    for coordinates in ((1, 1, 1), (16, 16, 16), (1, 2, 3), (3, 13, 9), (4, 7, 8))
        coefficient = sum(1:NineFourths.rank_count(seed)) do term
            prod(
                leg -> NineFourths.rank_coefficient(seed, term, leg, coordinates[leg]), 1:3
            )
        end
        @test coefficient == seed_tensor_entry(1, 2, coordinates)
    end

    power = NineFourths.seed_decomposition(1, 2, 2)
    @test size(power) == (16^2, 16^2, 16^2)
    @test NineFourths.rank_count(power) == 2^12
    first_term, second_term = 1, 64
    first_coordinate, second_coordinate = 1, 2
    term = first_term + 64 * (second_term - 1)
    coordinate = first_coordinate + 16 * (second_coordinate - 1)
    expected =
        NineFourths.rank_coefficient(seed, first_term, 1, first_coordinate) *
        NineFourths.rank_coefficient(seed, second_term, 1, second_coordinate)
    @test expected == -1//16
    @test NineFourths.rank_coefficient(power, term, 1, coordinate) == expected
end

@testset "Seed restrictions to matrix multiplication and the unit tensor" begin
    for (a, b) in ((2, 1), (2, 2))
        baseline = NineFourths.seed_baseline(a, b)
        @test NineFourths.source_dims(baseline) == NineFourths.seed_dims(a, b)
        @test NineFourths.target_dims(baseline) == (16, 16, 16)
        # One vector of selected source columns per leg, in target row order.
        selected = ntuple(3) do leg
            [first(only(NineFourths.row_entries(baseline.legs[leg], row))) for row in 1:16]
        end
        @test all(CartesianIndices((16, 16, 16))) do coordinate
            x, y, z = Tuple(coordinate)
            k, i = divrem(x - 1, 4)
            j, second_k = divrem(y - 1, 4)
            column, row = divrem(z - 1, 4)
            source = (selected[1][x], selected[2][y], selected[3][z])
            seed_tensor_entry(a, b, source) == (k == second_k && i == row && j == column)
        end

        unit = NineFourths.seed_unit(a, b)
        @test NineFourths.target_dims(unit) == (2, 2, 2)
        for k in 1:2, j in 1:2, i in 1:2
            source = ntuple(
                leg -> first(only(NineFourths.row_entries(unit.legs[leg], (i, j, k)[leg]))),
                3,
            )
            @test seed_tensor_entry(a, b, source) == (i == j == k)
        end
    end
    @test_throws ArgumentError NineFourths.seed_unit(1, 1)
end
