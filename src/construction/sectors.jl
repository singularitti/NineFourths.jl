# Claim 6.6, with all six orientations in the order used by the balanced seed.

struct SectorTransition{K}
    a::BigInt
    b::BigInt
    shift::BigInt
    sector_type::SectorType{K}
end

function midpoint_transition(a::Integer, b::Integer, s::Integer, j::Integer, N::Integer)
    a >= 1 && 1 <= s < b && N >= 1 && 0 <= j <= N ||
        throw(ArgumentError("invalid midpoint dimensions or sector counts"))
    return SectorTransition(big(a), big(b), big(s), SectorType((j, big(N) - j)))
end

function tripling_transition(a::Integer, b::Integer, j0::Integer, j1::Integer,
                             j2::Integer)
    a >= 1 && b >= 1 && big(j0) + j1 + j2 >= 1 ||
        throw(ArgumentError("invalid tripling dimensions or sector counts"))
    return SectorTransition(big(a), big(b), big(0), SectorType((j0, j1, j2)))
end

_is_midpoint(::SectorTransition{K}) where {K} = K == 2
_sector_copies(transition::SectorTransition) = sum(transition.sector_type.counts)

function transition_degree(transition::SectorTransition, stage::Integer)
    M = transition.sector_type.multiplicity
    stage == 1 && return 6 * _sector_copies(transition)
    stage == 2 && return 6 * (M - 1)^2
    throw(ArgumentError("Claim 6.6 has stages 1 and 2"))
end

function _sector_input_lengths(transition)
    a, b = transition.a, transition.b
    _is_midpoint(transition) || (b = 3b + a - 1)
    return (a, b, a + b - 1)
end

function _sector_block_lengths(transition, local_leg)
    a, b, s = transition.a, transition.b, transition.shift
    if _is_midpoint(transition)
        length = local_leg == 2 ? b : a + b - 1
        return (length - s, length + s)
    end
    return local_leg == 2 ? (b, b + a - 1, b) : (b + a - 1, b, b + a - 1)
end

function _sector_input_radices(transition, leg)
    lengths = _sector_input_lengths(transition)
    return ntuple(i -> lengths[LEG_PERMUTATIONS[i][leg]], 6)
end

function _sector_middle_radices(transition, leg)
    radices = _sector_input_radices(transition, leg)
    _is_midpoint(transition) || return radices
    return ntuple(6) do orientation
        LEG_PERMUTATIONS[orientation][leg] == 1 && return radices[orientation]
        return 2 * radices[orientation]
    end
end

function _sector_output_radices(transition, leg, sector)
    a, b, s = transition.a, transition.b, transition.shift
    if _is_midpoint(transition)
        b = sector == 1 ? b - s : b + s
    end
    lengths = (a, b, a + b - 1)
    return ntuple(i -> lengths[LEG_PERMUTATIONS[i][leg]], 6)
end

function _sector_coordinate(transition, local_leg, digit)
    local_leg == 1 && return digit
    for (sector, length) in enumerate(_sector_block_lengths(transition, local_leg))
        digit <= length && return (sector, digit)
        digit -= length
    end
    throw(BoundsError())
end

# B_X uses the column index, B_Y the row index, and B_Z the
# contraction index. Their two copies form the two digits of each index.
const _SECTOR_DOT_LEGS = ((2, 3), (3, 1), (2, 1))

function _sector_dot_axis(leg, orientation)
    shared = findfirst(==(1), LEG_PERMUTATIONS[orientation])
    first_leg, second_leg = _SECTOR_DOT_LEGS[leg]
    shared == first_leg && return 1
    shared == second_leg && return 2
    return 0
end

function _sector_first_value(transition, local_leg, dot_copy, source, target, t)
    value = Ref(zero(t))
    record = function (coordinate, coefficient)
        coordinate == target && (value[] = coefficient)
        return nothing
    end
    a, b = transition.a, transition.b
    if _is_midpoint(transition)
        midpoint_column(record, a, b, transition.shift, local_leg, dot_copy, source, t)
    else
        tripling_column(record, a, b, local_leg, source, t)
    end
    return value[]
end

function _sector_first_sources(transition, local_leg, target, digit)
    if !_is_midpoint(transition) || local_leg == 1
        return ((1, digit),)
    end
    b, s = transition.b, transition.shift
    sector, index = target
    if local_leg == 2
        if sector == 1
            return ((1, index + s), (2, index))
        end
        return index <= b ? ((1, index),) : ((2, index - s),)
    end
    sector == 1 && return ((2, index),)
    index <= s && return ((1, index),)
    index >= transition.a + b && return ((2, index - s),)
    return ((1, index), (2, index - s))
end

function _sector_first_leg(transition, leg, t)
    count = _sector_copies(transition)
    units = (2 * transition.sector_type.multiplicity)^6
    source_radices = _sector_input_radices(transition, leg)
    middle_radices = _sector_middle_radices(transition, leg)
    source_q = prod(source_radices)^count
    dot_size = _is_midpoint(transition) ? big(4)^count : big(1)
    source_dim = units * source_q * dot_size^2
    target_dim = units * prod(middle_radices)^count
    coefficient = function (target_row, source_column)
        old, unit = divrem(source_column - 1, units)
        new, new_unit = divrem(target_row - 1, units)
        unit == new_unit || return zero(t)
        matrix, old = divrem(old, source_q)
        matrix2, matrix1 = divrem(matrix, dot_size)
        matrix_digits = [matrix1, matrix2]
        value = one(t)
        for _ in 1:count, orientation in 1:6
            old, source = divrem(old, source_radices[orientation])
            new, target = divrem(new, middle_radices[orientation])
            local_leg = LEG_PERMUTATIONS[orientation][leg]
            axis = _sector_dot_axis(leg, orientation)
            dot_copy = 1
            if _is_midpoint(transition) && axis != 0
                matrix_digits[axis], digit = divrem(matrix_digits[axis], 2)
                dot_copy += digit
            end
            target = _sector_coordinate(transition, local_leg, target + 1)
            value *= _sector_first_value(transition, local_leg, dot_copy, source + 1,
                                         target, t)
            iszero(value) && return value
        end
        return value
    end
    function entries(target_row)
        new, unit = divrem(target_row - 1, units)
        source_column = unit + 1
        value = one(t)
        source_stride = units
        matrix_strides = [units * source_q, units * source_q * dot_size]
        alternatives = NTuple{2,Tuple{BigInt,Rational{BigInt}}}[]
        for _ in 1:count, orientation in 1:6
            new, digit = divrem(new, middle_radices[orientation])
            local_leg = LEG_PERMUTATIONS[orientation][leg]
            axis = _sector_dot_axis(leg, orientation)
            dot_stride = big(0)
            if _is_midpoint(transition) && axis != 0
                dot_stride = matrix_strides[axis]
                matrix_strides[axis] *= 2
            end
            target = _sector_coordinate(transition, local_leg, digit + 1)
            sources = _sector_first_sources(transition, local_leg, target, digit + 1)
            options = map(sources) do (dot_copy, index)
                offset = (dot_copy - 1) * dot_stride + (index - 1) * source_stride
                weight = _sector_first_value(transition, local_leg, dot_copy, index,
                                             target, t)
                return (offset, weight)
            end
            if length(options) == 1
                offset, weight = only(options)
                source_column += offset
                value *= weight
            else
                push!(alternatives, options)
            end
            source_stride *= source_radices[orientation]
        end
        function contribution(bits)
            column, weight = source_column, value
            for options in alternatives
                bits, choice = divrem(bits, 2)
                offset, factor = options[Int(choice) + 1]
                column += offset
                weight *= factor
            end
            return (column, weight)
        end
        return (contribution(bits) for bits in 0:(big(2)^length(alternatives) - 1))
    end
    return LegMap(source_dim, target_dim, coefficient, entries)
end

function _sector_source_coordinates!(input_coordinates, transition, local_leg,
                                     orientation, word, output_coordinates, offsets)
    positions = copy(offsets)
    block_offsets = if local_leg == 1
        nothing
    else
        cumsum((big(0), _sector_block_lengths(transition, local_leg)...))
    end
    middle_orientation = orientation
    if !_is_midpoint(transition)
        swapped = map(index -> index == 1 ? 1 : 5 - index,
                      LEG_PERMUTATIONS[orientation])
        middle_orientation = findfirst(==(swapped), LEG_PERMUTATIONS)
    end
    for (copy, sector) in enumerate(word)
        positions[sector] += 1
        output_orientation = orientation
        if !_is_midpoint(transition) && sector == 2
            output_orientation = middle_orientation
        end
        index = output_coordinates[output_orientation, positions[sector]]
        if local_leg != 1
            index += block_offsets[sector]
        elseif !_is_midpoint(transition) && sector == 2
            index = transition.a + 1 - index
        end
        input_coordinates[orientation, copy] = index
    end
    return nothing
end

function _sector_second_leg(transition, leg, t)
    count = _sector_copies(transition)
    sector_type = transition.sector_type
    M = sector_type.multiplicity
    input_units = (2M)^6
    output_units = M^6
    middle_radices = _sector_middle_radices(transition, leg)
    output_radices = ntuple(length(sector_type.counts)) do sector
        _sector_output_radices(transition, leg, sector)
    end
    output_q = prod(prod(radices)^n for (radices, n) in zip(output_radices,
                                                          sector_type.counts))
    source_dim = input_units * prod(middle_radices)^count
    target_dim = output_units * output_q * M^4
    function row_parameters(target_row)
        new, word_unit = divrem(target_row - 1, output_units)
        matrix, new = divrem(new, output_q)
        matrix2, matrix1 = divrem(matrix, M^2)
        matrix_digits = [matrix1, matrix2]
        input_coordinates = Matrix{BigInt}(undef, 6, Int(count))
        output_coordinates = similar(input_coordinates)
        copy = 0
        for (radices, n) in zip(output_radices, sector_type.counts), _ in 1:n
            copy += 1
            for orientation in 1:6
                new, digit = divrem(new, radices[orientation])
                output_coordinates[orientation, copy] = digit + 1
            end
        end
        offsets = cumsum([0; Int.(collect(sector_type.counts))])
        phases = Vector{BigInt}(undef, 6)
        weight = big(0)
        for orientation in 1:6
            word_unit, i = divrem(word_unit, M)
            word = type_word(sector_type, i + 1)
            local_leg = LEG_PERMUTATIONS[orientation][leg]
            _sector_source_coordinates!(input_coordinates, transition, local_leg,
                                        orientation, word, output_coordinates, offsets)
            axis = _sector_dot_axis(leg, orientation)
            k = big(0)
            if axis != 0
                matrix_digits[axis], k = divrem(matrix_digits[axis], M)
            end
            local_phase, local_weight = separation_character(local_leg, i, k, 1)
            phases[orientation] = local_phase
            weight += local_weight
        end
        input_q = big(0)
        for copy in Int(count):-1:1, orientation in 6:-1:1
            input_q = input_q * middle_radices[orientation] +
                input_coordinates[orientation, copy] - 1
        end
        return (input_q, phases, weight)
    end
    function phase_coefficient(copy_unit, phases, scale)
        phase = big(0)
        for orientation in 1:6
            copy_unit, ρ = divrem(copy_unit, 2M)
            phase += ρ * phases[orientation]
        end
        return iszero(mod(phase, 2M)) ? scale : root_of_unity(2M, phase) * scale
    end
    function coefficient(target_row, source_column)
        old, copy_unit = divrem(source_column - 1, input_units)
        input_q, phases, weight = row_parameters(target_row)
        old == input_q || return zero(t)
        # Each global leg is the local third leg in exactly two orientations.
        scale = t^weight / (2M)^2
        return phase_coefficient(copy_unit, phases, scale)
    end
    function entries(target_row)
        input_q, phases, weight = row_parameters(target_row)
        scale = t^weight / (2M)^2
        return ((input_q * input_units + copy + 1, phase_coefficient(copy, phases, scale))
                for copy in 0:(input_units - 1))
    end
    return LegMap(source_dim, target_dim, coefficient, entries)
end

"""
    transition_restriction(transition, stage, t)

Return the variable substitutions at a nonzero rational parameter for one
stage of Claim 6.6. Input factors are the unit tensor, the balanced seed
copies, then the matrix tensor if needed. Output factors are the returned
unit tensor, the child seed copies, then the matrix tensor. The shorter
child copies come first for midpoint transitions. The intermediate space
holds the same unit factor and the six oriented sector tensors per copy.
"""
function transition_restriction(transition::SectorTransition, stage::Integer, t)
    t = evaluation_parameter(t)
    make_leg = if stage == 1
        _sector_first_leg
    elseif stage == 2
        _sector_second_leg
    else
        throw(ArgumentError("Claim 6.6 has stages 1 and 2"))
    end
    legs = ntuple(leg -> make_leg(transition, leg, t), 3)
    return TensorRestriction(legs...)
end
