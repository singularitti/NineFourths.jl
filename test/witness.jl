@testset "Catalytic witness compilation" begin
    function node(a, b, value, kind, parents=())
        return NineFourths.DerivationNode(big(a), big(b), big(value) // 1, kind, parents)
    end

    baseline = [node(1, 2, 2, :baseline)]
    witness = NineFourths.compile_witness(baseline, 1)
    @test witness.side == 4
    @test witness.copies == 1
    @test NineFourths.source_dims(witness.restriction) == NineFourths.seed_dims(1, 2)
    @test NineFourths.target_dims(witness.restriction) == NineFourths.mm_dims(4)
    @test witness.recipe.nodes == baseline
    @test witness.recipe.nodes !== baseline

    midpoint = [
        node(1, 1, 1, :baseline), node(1, 3, 3, :baseline), node(1, 2, 2, :midpoint, (1, 2))
    ]
    plan = NineFourths._witness_events(midpoint, 2)
    event = only(plan.events)
    @test event.counts == (0, 2, 0)
    @test event.child_side == 81
    @test event.side == 5
    @test NineFourths.witness_side(midpoint, 2) == 625

    witness = NineFourths.compile_witness(midpoint, 2; step_bound=3)
    @test witness.side == 625
    @test witness.copies == 416
    @test NineFourths.source_dims(witness.restriction) ==
        map(dimension -> dimension^witness.copies, NineFourths.seed_dims(1, 2))
    @test NineFourths.target_dims(witness.restriction) == NineFourths.mm_dims(625)

    chain = [
        node(1, 2, 2, :baseline),
        node(1, 6, 6, :tripling, (1,)),
        node(6, 1, 6, :symmetry, (2,)),
        node(7, 1, 6, :restriction, (3,)),
    ]
    plan = NineFourths._witness_events(chain, 2)
    tripling = last(plan.events)
    @test tripling.counts == (1, 1, 0)
    @test tripling.multiplicity == 2
    @test tripling.side == 64
    @test NineFourths.compile_witness(chain, 2).side == 64^4

    fallback = [
        node(1, 1, 1, :baseline),
        node(1, 3, 1, :restriction, (1,)),
        node(1, 2, 1, :midpoint, (1, 2)),
        node(1, 6, 3, :tripling, (3,)),
    ]
    @test NineFourths.compile_witness(fallback, 1).side == 1

    transition = NineFourths.tripling_transition(1, 1, 1, 1, 0)
    phase1 = NineFourths._interpolated_phase(transition, 1, 2)
    phase2 = NineFourths._interpolated_phase(transition, 2, 2)
    @test phase1.points == 25
    @test phase2.points == 13
    @test_throws ArgumentError NineFourths.compile_witness(midpoint, 0)
    @test_throws ArgumentError NineFourths.compile_witness(midpoint, 2; step_bound=0)
end

@testset "Witness substitution coefficients" begin
    index(dims, coordinates) = LinearIndices(dims)[CartesianIndex(coordinates)]
    seed_coordinates = (1, 2, 2, 1, 2, 1)
    source = index((2, 4, 3, 3, 4, 2), seed_coordinates)
    target = index((1, 2, 2, 2, 2, 1), seed_coordinates)
    truncate = NineFourths._seed_restrict(2, 3, 1, 2).legs[1]
    @test truncate[target, source] == 1
    @test truncate[target, source - 1] == 0

    source_digits = (2, 3, 1, 3, 4, 2)
    swapped_digits = (3, 4, 2, 2, 3, 1)
    source = index((2, 4, 3, 3, 4, 2), source_digits)
    target = index((3, 4, 2, 2, 4, 3), swapped_digits)
    swap = NineFourths._seed_symmetry(2, 3).legs[1]
    @test swap[target, source] == 1
    @test swap[target, source - 1] == 0

    factors = [(2, 3, 4), (3, 2, 5)]
    group = NineFourths._replica_order(factors, 2).legs[1]
    ungroup = NineFourths._replica_order(factors, 2; inverse=true).legs[1]
    source = index((2, 2, 3, 3), (2, 1, 3, 2))
    target = index((2, 3, 2, 3), (2, 3, 1, 2))
    @test group[target, source] == 1
    @test ungroup[source, target] == 1
    @test source != target
    @test group[source, source] == 0

    matrix = NineFourths._matrix_power(2, 2).legs[1]
    split = NineFourths._matrix_power(2, 2; inverse=true).legs[1]
    @test matrix[14, 12] == 1
    @test split[12, 14] == 1
    @test matrix[12, 12] == 0

    # The first copy uses the midpoint kernel coordinate on one orientation.
    # The second copy uses only complement coordinates.
    transition = NineFourths.midpoint_transition(1, 2, 1, 1, 1)
    phase = NineFourths._interpolated_phase(transition, 1, 2)
    old = 1 + 64 * (index((1, 2, 2, 2, 2, 1), (1, 1, 2, 1, 1, 1)) - 1)
    first = 1 + 64 * (index((1, 4, 4, 4, 4, 1), (1, 2, 1, 2, 2, 1)) - 1)
    second = 1 + 64 * (index((1, 4, 4, 4, 4, 1), (1, 2, 2, 2, 2, 1)) - 1)
    row = first + (second - 1) * (64 * 4^4)
    for point in (1, 2, 3)
        column = point + phase.points * (old - 1)
        sign = isodd(point) ? 1 : -1
        @test phase.restriction.legs[1][row, column] ==
            -sign * binomial(phase.points, point) // point
    end

    # Interpolation gives the constant term across all powers up through D.
    transition = NineFourths.tripling_transition(1, 1, 1, 1, 0)
    phase = NineFourths._interpolated_phase(transition, 1, 2)
    weights = [phase.restriction.legs[1][1, point] for point in 1:phase.points]
    @test sum(weights) == 1
    @test all(
        iszero(sum(weights[point] * point^degree for point in 1:phase.points)) for
        degree in 1:(phase.points - 1)
    )
end

# In Q(1,2), the two nonscalar legs of each orientation carry the same
# binary index. Grouping these digits by the scalar leg gives the two
# matrix indices on each source leg, even across powered copies of Q.
function midpoint_test_source_pairs(
    witness, leg, row; embed=identity, zero_weight=big(0) // 1
)
    orientations = ((1, 2, 3), (3, 1, 2), (2, 3, 1), (2, 1, 3), (3, 2, 1), (1, 3, 2))
    active = filter(orientation -> orientation[leg] != 1, orientations)
    shared_legs = ((2, 3), (3, 1), (2, 1))[leg]
    positions = map(
        shared -> findall(orientation -> orientation[shared] == 1, active), shared_legs
    )
    function axis_index(source, digits)
        index, place = big(0), big(1)
        for _ in 1:witness.copies
            for digit in digits
                isodd(source >> (digit - 1)) && (index += place)
                place <<= 1
            end
            source >>= 4
        end
        return index
    end
    weights = Dict{Tuple{BigInt,BigInt},typeof(zero_weight)}()
    for (column, weight) in NineFourths.row_entries(witness.restriction.legs[leg], row)
        coordinates = map(digits -> axis_index(column - 1, digits), positions)
        weights[coordinates] = get(weights, coordinates, zero_weight) + embed(weight)
    end
    return weights
end

function test_midpoint_tensor_identity(witness; embed=identity, zero_weight=big(0) // 1)
    Weight = typeof(zero_weight)
    rows = ntuple(3) do leg
        return [
            midpoint_test_source_pairs(witness, leg, row; embed, zero_weight) for row in 1:4
        ]
    end
    right_buckets = map(rows[2]) do right
        by_inner = Dict{BigInt,Vector{Tuple{BigInt,Weight}}}()
        for ((inner, column), weight) in right
            push!(get!(() -> Tuple{BigInt,Weight}[], by_inner, inner), (column, weight))
        end
        return by_inner
    end
    matrix_units = CartesianIndices((2, 2))
    for y in 1:4, x in 1:4
        by_inner = right_buckets[y]
        product = Dict{Tuple{BigInt,BigInt},Weight}()
        for ((row, inner), weight) in rows[1][x]
            haskey(by_inner, inner) || continue
            for (column, right_weight) in by_inner[inner]
                coordinate = (row, column)
                product[coordinate] =
                    get(product, coordinate, zero_weight) + weight * right_weight
            end
        end
        i, left_inner = Tuple(matrix_units[x])
        right_inner, j = Tuple(matrix_units[y])
        for z in 1:4
            coefficient = sum(rows[3][z]; init=zero_weight) do (coordinate, weight)
                return get(product, coordinate, zero_weight) * weight
            end
            expected = left_inner == right_inner && Tuple(matrix_units[z]) == (i, j)
            @test coefficient == embed(Int(expected))
        end
    end
    return nothing
end

@testset "Compiled midpoint tensor identity" begin
    nodes = [
        NineFourths.DerivationNode(1, 1, 1 // 1, :baseline, ()),
        NineFourths.DerivationNode(1, 3, 3 // 1, :baseline, ()),
        NineFourths.DerivationNode(1, 2, 2 // 1, :midpoint, (1, 2)),
    ]
    # This step prepares and returns M₄ and crops the long child's M₉
    # to M₂ ⊗ M₄ before discarding the returned catalyst.
    witness = NineFourths.compile_witness(nodes, 1)
    @test witness.side == 2
    test_midpoint_tensor_identity(witness)
end
