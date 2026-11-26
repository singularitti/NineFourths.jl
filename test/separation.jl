function sector_test_expand!(coefficients, maps, indices)
    maps[1](indices[1]) do x, x_coefficient
        maps[2](indices[2]) do y, y_coefficient
            maps[3](indices[3]) do z, z_coefficient
                term = (x, y, z)
                coefficient = x_coefficient * y_coefficient * z_coefficient
                return coefficients[term] =
                    get(coefficients, term, big(0) // 1) + coefficient
            end
        end
    end
    return coefficients
end

function sector_test_polynomial!(coefficients, a, b, sector)
    for i in 1:a, j in 1:b
        coefficients[(i, (sector, j), (sector, i + j - 1))] = big(1) // 1
    end
    return coefficients
end

@testset "Midpoint and three-sector substitutions" begin
    for t in (2 // 1, -3 // 2)
        a, b, s = 3, 5, 2
        observed = Dict()
        for copy in 1:2
            maps = ntuple(3) do leg
                (emit, index) ->
                    NineFourths.midpoint_column(emit, a, b, s, leg, copy, index, t)
            end
            for i in 1:a, j in 1:b
                sector_test_expand!(observed, maps, (i, j, i + j - 1))
            end
        end
        filter!(term -> !iszero(last(term)), observed)
        expected = Dict()
        sector_test_polynomial!(expected, a, b - s, 1)
        sector_test_polynomial!(expected, a, b + s, 2)
        for i in 1:a, j in (b - s + 1):b
            output = i + j - 1
            if output <= a + b - 1 - s
                expected[(i, (2, j + s), (1, output))] = t
            end
        end
        @test observed == expected

        a, b = 3, 2
        observed = Dict()
        maps = ntuple(3) do leg
            (emit, index) -> NineFourths.tripling_column(emit, a, b, leg, index, t)
        end
        for i in 1:a, j in 1:(3b + a - 1)
            sector_test_expand!(observed, maps, (i, j, i + j - 1))
        end
        expected = Dict()
        sector_test_polynomial!(expected, a, b, 1)
        sector_test_polynomial!(expected, a, b, 3)
        for i in 1:a, k in 1:b
            expected[(i, (2, a - i + k), (2, k))] = big(1) // 1
        end
        for i in 1:a, j in 1:(a + b - 1)
            output = b + i + j - 1
            if output < a + b
                expected[(i, (2, j), (1, output))] = t
            elseif output >= 2b + a
                expected[(i, (2, j), (3, output - (2b + a - 1)))] = t
            end
        end
        @test observed == expected
    end
end

@testset "Fixed types and exact Fourier separation" begin
    counts = Any[Int16(2), UInt8(1), big(1)]
    sector_type = NineFourths.SectorType(Iterators.Stateful(counts))
    @test sector_type.counts isa NTuple{3,BigInt}
    @test sector_type.counts == (2, 1, 1)
    @test_throws MethodError NineFourths.SectorType([2.0, 1.0])
    @test_throws DomainError NineFourths.SectorType((1, -1, 1))
    empty_type = NineFourths.SectorType(())
    @test NineFourths.type_rank(empty_type, ()) == 1
    @test isempty(NineFourths.type_word(empty_type, 1))
    words = [
        (1, 1, 2, 3),
        (1, 1, 3, 2),
        (1, 2, 1, 3),
        (1, 2, 3, 1),
        (1, 3, 1, 2),
        (1, 3, 2, 1),
        (2, 1, 1, 3),
        (2, 1, 3, 1),
        (2, 3, 1, 1),
        (3, 1, 1, 2),
        (3, 1, 2, 1),
        (3, 2, 1, 1),
    ]
    @test sector_type.multiplicity == length(words)
    @test all(
        NineFourths.type_rank(sector_type, word) == rank for
        (rank, word) in enumerate(words)
    )
    @test NineFourths.type_rank(sector_type, Iterators.filter(>(0), (1, 0, 2, 1, 3))) == 3
    @test all(
        Tuple(NineFourths.type_word(sector_type, rank)) == word for
        (rank, word) in enumerate(words)
    )
    @test isnothing(NineFourths.type_rank(sector_type, (1, 1, 1, 2)))
    @test isnothing(NineFourths.type_rank(sector_type, (1, 1, 2)))
    @test isnothing(NineFourths.type_rank(sector_type, (1, 1, 2, 3, 1)))

    sector_type = NineFourths.SectorType((1, 1))
    t = -3 // 2
    rootpower = exponent -> NineFourths.root_of_unity(4, exponent)
    @test NineFourths.evaluation_parameter(Nemo.QQ(t)) == t
    for coordinates in ((101,), (101, 202, 303))
        @test_throws DimensionMismatch NineFourths.separation_column(
            tuple, sector_type, 1, 0, coordinates, t
        )
    end
    for (i, word) in enumerate(((1, 2), (2, 1), (2, 2)))
        x_indices = (101, 202)
        y_indices = ((word[1], 11), (word[2], 22))
        z_indices = ((word[1], 33), (word[2], 44))
        observed = Dict()
        for ρ in 0:3
            maps = ntuple(3) do leg
                (emit, index) -> NineFourths.separation_column(
                    emit, sector_type, leg, ρ, Iterators.Stateful(index), t, rootpower
                )
            end
            sector_test_expand!(observed, maps, (x_indices, y_indices, z_indices))
        end
        filter!(term -> !iszero(last(term)), observed)
        expected = Dict()
        if i <= 2
            y = i == 1 ? (11, 22) : (22, 11)
            z = i == 1 ? (33, 44) : (44, 33)
            for j in 1:2, k in 1:2, l in 1:2
                j + k == i + l || continue
                x = j == 1 ? x_indices : reverse(x_indices)
                expected[((j, 1, x), (i, k, y), (i, l, z))] = t^((j - i)^2)
            end
        end
        @test Dict(
            key => NineFourths.rational_result(value) for (key, value) in observed
        ) == expected
    end
end

function sector_test_pack(indices, radices)
    coordinate = big(0)
    stride = big(1)
    for (index, radix) in zip(indices, radices)
        coordinate += (index - 1) * stride
        stride *= radix
    end
    return coordinate + 1
end

@testset "Balanced finite stages" begin
    a, b, s = 2, 4, 1
    transition = NineFourths.midpoint_transition(a, b, s, 1, 1)
    t = 3 // 2
    first_stage = NineFourths.transition_restriction(transition, 1, t)
    second_stage = NineFourths.transition_restriction(transition, 2, t)
    dimensions = NineFourths.seed_dims(a, b)
    @test NineFourths.source_dims(first_stage) ==
        map(dimension -> 64 * 16 * dimension, dimensions)
    @test NineFourths.target_dims(first_stage) == NineFourths.source_dims(second_stage)
    @test NineFourths.target_dims(second_stage) == NineFourths.seed_dims(a, b - s)
    @test NineFourths.transition_degree(transition, 1) == 6
    @test NineFourths.transition_degree(transition, 2) == 0
    @test_throws DomainError NineFourths.transition_restriction(transition, 1, 0)
    @test_throws DomainError NineFourths.transition_restriction(transition, 2, 1 // 0)
    legs = ((1, 3, 2, 2, 3, 1), (2, 1, 3, 1, 2, 3), (3, 2, 1, 3, 1, 2))
    dot_copy_two = ((2, 5), (3, 6), (2, 6))
    lengths = (a, b, a + b - 1)
    for leg in 1:3
        radices = map(local_leg -> local_leg == 1 ? a : 2 * lengths[local_leg], legs[leg])
        coordinates = ntuple(6) do orientation
            local_leg = legs[leg][orientation]
            local_leg == 1 && return 1
            return orientation in dot_copy_two[leg] ? 1 : lengths[local_leg] - s + 1
        end
        column = 64 * (sector_test_pack(coordinates, radices) - 1) + 1
        row = 64 * dimensions[leg] * 9 + 1 # Zero-based matrix digits 1 and 2.
        expected = prod(
            legs[leg][orientation] == 2 ? inv(t) : t for orientation in dot_copy_two[leg]
        )
        leg_map = first_stage.legs[leg]
        @test leg_map[column, row] == expected
        @test iszero(leg_map[column, row + 1])
        entries = Dict(NineFourths.row_entries(leg_map, column))
        @test entries[row] == expected
        @test all(leg_map[column, index] == weight for (index, weight) in entries)
    end

    b = 3
    tripling = NineFourths.tripling_transition(a, b, 0, 1, 0)
    first_stage = NineFourths.transition_restriction(tripling, 1, t)
    second_stage = NineFourths.transition_restriction(tripling, 2, t)
    @test NineFourths.source_dims(first_stage) ==
        map(dimension -> 64 * dimension, NineFourths.seed_dims(a, 3b + a - 1))
    @test NineFourths.target_dims(first_stage) == NineFourths.source_dims(second_stage)
    @test NineFourths.target_dims(second_stage) == NineFourths.seed_dims(a, b)
    swapped_orientations = (6, 4, 5, 2, 3, 1)
    input_lengths = (a, 3b + a - 1, 3b + 2a - 2)
    output_lengths = (a, b, a + b - 1)
    output_indices = (1, 2, 1, 2, 1, 2)
    for leg in 1:3
        coordinates = ntuple(6) do orientation
            local_leg = legs[leg][orientation]
            index = output_indices[swapped_orientations[orientation]]
            if local_leg == 1
                return a + 1 - index
            end
            return (local_leg == 2 ? b : b + a - 1) + index
        end
        input_radices = map(local_leg -> input_lengths[local_leg], legs[leg])
        output_radices = map(local_leg -> output_lengths[local_leg], legs[leg])
        column = sector_test_pack(output_indices, output_radices)
        row = 64 * (sector_test_pack(coordinates, input_radices) - 1) + 64
        leg_map = second_stage.legs[leg]
        rows, columns = size(leg_map)
        @test rows < columns
        @test leg_map[column, row] == 1 // 4
        wrong_column = column == 1 ? 2 : column - 1
        @test iszero(leg_map[wrong_column, row])
    end

    transitions = (
        NineFourths.midpoint_transition(2, 5, 2, 1, 2),
        NineFourths.tripling_transition(2, 2, 0, 1, 1),
    )
    for transition in transitions
        @test transition.sector_type.multiplicity == 2
        @test NineFourths.transition_degree(transition, 1) == 12
        @test NineFourths.transition_degree(transition, 2) == 6
    end

    transition = transitions[1]
    mixed = NineFourths.transition_restriction(transition, 2, t)
    ranks = (2, 1, 2, 1, 1, 2)
    copies = (1, 2, 3, 4, 1, 2)
    input_unit = sector_test_pack(copies, fill(4, 6))
    output_unit = sector_test_pack(ranks, fill(2, 6))
    canonical = ((1, 2, 1, 2, 1, 2), (2, 1, 2, 1, 2, 1))
    short = (2, 3, 4)
    long = (2, 7, 8)
    mixed_lengths = (2, 10, 12)
    for leg in 1:3
        input_radices = map(local_leg -> mixed_lengths[local_leg], legs[leg])
        output_radices = map(
            lengths -> map(local_leg -> lengths[local_leg], legs[leg]), (short, long)
        )
        input_coordinates = ntuple(12) do position
            copy, axis = divrem(position - 1, 6)
            orientation = axis + 1
            local_leg = legs[leg][orientation]
            sector = ranks[orientation] == 1 ? copy + 1 : 2 - copy
            index = canonical[sector][orientation]
            return local_leg == 1 || sector == 1 ? index : short[local_leg] + index
        end
        row =
            input_unit +
            4^6 *
            (sector_test_pack(input_coordinates, (input_radices..., input_radices...)) - 1)
        new_q = sector_test_pack(
            (canonical[1]..., canonical[2]...), (output_radices[1]..., output_radices[2]...)
        )
        column =
            output_unit +
            2^6 * (new_q - 1 + 9 * prod(first(output_radices)) * prod(last(output_radices)))
        phase, weight = 0, 0
        for orientation in 1:6
            i, ρ = ranks[orientation] - 1, copies[orientation] - 1
            k = Int(orientation in dot_copy_two[leg])
            local_leg = legs[leg][orientation]
            if local_leg == 1
                phase += ρ * i
                weight += i^2
            elseif local_leg == 2
                phase += ρ * (k - i)
                weight += 2i * k - i^2
            else
                phase -= ρ * k
                weight -= 2i * k
            end
        end
        @test mixed.legs[leg][column, row] ==
            NineFourths.root_of_unity(4, phase) * (t^weight / 16)
        orientation = findfirst(!=(1), legs[leg])
        wrong_column = column + (3 - 2ranks[orientation]) * 2^(orientation - 1)
        @test iszero(mixed.legs[leg][wrong_column, row])
    end
end

# For a=1, the two midpoint sectors act by scalar multiplication. The
# intermediate tensor has coefficient one exactly when the Fourier copies
# match and each orientation matches its local second and third indices.
function scalar_midpoint_source_coefficient(columns)
    units = 4^6
    digits = map(column -> divrem(column - 1, units), columns)
    digits[1][2] == digits[2][2] == digits[3][2] || return 0
    polynomial = map(first, digits)
    orientations = ((1, 2, 3), (3, 1, 2), (2, 3, 1), (2, 1, 3), (3, 2, 1), (1, 3, 2))
    for _ in 1:2, orientation in orientations
        digits = ntuple(leg -> divrem(polynomial[leg], orientation[leg] == 1 ? 1 : 4), 3)
        polynomial = map(first, digits)
        y = findfirst(==(2), orientation)
        z = findfirst(==(3), orientation)
        digits[y][2] == digits[z][2] || return 0
    end
    return 1
end

@testset "Balanced separation of a fixed type" begin
    transition = NineFourths.midpoint_transition(1, 2, 1, 1, 2)
    t = -3 // 2
    restriction = NineFourths.transition_restriction(transition, 2, t)
    long_seed_dimension = 81
    changed_matrix_column = 1 + 2^6 * long_seed_dimension * 4
    for (target_rows, expected) in
        (((1, 1, 1), 1), ((2, 1, 1), 0), ((2, 1, changed_matrix_column), t))
        entries = map(NineFourths.row_entries, restriction.legs, target_rows)
        actual = sum(zip(entries...); init=big(0) // 1) do terms
            source = scalar_midpoint_source_coefficient(map(first, terms))
            source == 0 && return big(0) // 1
            return prod(map(last, terms))
        end
        @test NineFourths.rational_result(actual) == expected
    end
end
