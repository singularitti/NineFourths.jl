# A callable fixture backed by a table `values::T`. The tests use a coefficient
# matrix, a tuple of row supports, and a tuple of selected source columns.
struct TestMapLookup{T}
    values::T
end

# Accept one-based `BigInt` indices. Two indices return a coefficient. One
# index returns an iterable of `(column, coefficient)` pairs or an integer
# source column, with zero marking an empty selection.
(lookup::TestMapLookup)(indices::BigInt...) = lookup.values[indices...]

@testset "Callable leg map callbacks" begin
    NF = NineFourths
    entry = TestMapLookup([0 -3; 4 0])
    support = TestMapLookup((((2, -3),), ((1, 4),)))
    dense = NF.LegMap(2, 2, entry)
    sparse = NF.LegMap(2, 2, entry, support)
    @test dense[1, 2] == -3
    @test only(NF.row_entries(dense, 1)) == (2, -3)
    @test only(NF.row_entries(sparse, 2)) == (1, 4)

    selected = NF.selection_map(3, 2, TestMapLookup((3, 0)))
    selected_restriction = NF.TensorRestriction(selected, selected, selected)
    reindex = NF.selection_map(2, 2, Int)
    selection_composite = NF.compose_restrictions(
        selected_restriction, NF.TensorRestriction(reindex, reindex, reindex)
    ).legs[1]
    @test selection_composite[1, 3] == 1
    @test only(NF.row_entries(selection_composite, 1)) == (3, 1)
    @test selection_composite[2, 3] == 0
    @test isempty(NF.row_entries(selection_composite, 2))

    weighted_composite = NF.compose_restrictions(
        selected_restriction, NF.TensorRestriction(sparse, sparse, sparse)
    ).legs[1]
    @test weighted_composite[2, 3] == 4
    @test only(NF.row_entries(weighted_composite, 2)) == (3, 4)
end

@testset "Directed linear maps and matrix tensor coordinates" begin
    NF = NineFourths
    a = NF.selection_map(7, 3, row -> (7, 2, 5)[row])
    b = NF.LegMap(3, 2, (row, col) -> [2 0 -3; 0 4 1][row, col])
    composed = NF.compose_restrictions(
        NF.TensorRestriction(a, a, a), NF.TensorRestriction(b, b, b)
    )
    map = composed.legs[1]
    @test [map[i, j] for i in 1:2, j in 1:7] == [0 0 0 0 -3 0 2; 0 4 0 0 1 0 0]
    for i in 1:2
        @test sum(j * v for (j, v) in NF.row_entries(map, i)) ==
            sum(j * map[i, j] for j in 1:7)
    end

    packed = NF.mm_product((2, 3))
    unpacked = NF.mm_split(6, (2, 3))
    original = NF.compose_restrictions(packed, unpacked)
    @test all(original.legs[1][i, j] == (i == j) for i in 1:36, j in 1:36)
    # (i₁,k₁)=(2,1), (i₂,k₂)=(1,3) → (i,k)=(2,5) in M₆.
    @test packed.legs[1][2 + 6 * 4, 2 + 4 * 6] == 1
    @test NF.mm_split(7, (2, 3)).legs[1][2 + 4 * 6, 2 + 7 * 4] == 1
    @test_throws DimensionMismatch NF.mm_split(5, (2, 3))

    classical = NF.unit_to_mm(3)
    # (i,k,j)=(2,3,1) contributes to X₂₃ Y₃₁ Z₂₁.
    term = 2 + 3 * 2
    @test all(classical.legs[leg][row, term] == 1 for (leg, row) in enumerate((8, 3, 2)))
    @test all(
        (term, 1) in NF.row_entries(classical.legs[leg], row) for
        (leg, row) in enumerate((8, 3, 2))
    )
    # Each factor supplies an integer triple of tensor leg dimensions.
    dimensions = ((2, 3, 4), (3, 4, 2), (4, 2, 3))
    reordered = NF.permute_factors(
        Iterators.Stateful(dimensions), Iterators.Stateful((3, 1, 2))
    )
    @test NF.target_dims(reordered) == (24, 24, 24)
    @test reordered.legs[1][3 + 4 * (1 + 2 * 2), 2 + 2 * (2 + 3 * 2)] == 1
    @test only(NF.row_entries(reordered.legs[1], 1)) == (1, 1)
    @test_throws ArgumentError NF.permute_factors(dimensions, (1, 1, 3))
end
