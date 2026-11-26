# Claim 6.6, with all six orientations in the order used by the balanced seed.

# B_X uses the column index, B_Y the row index, and B_Z the
# contraction index. Their two copies form the two digits of each index.
# This NTuple{3,NTuple{2,Int}} gives the ordered legs of the two indices.
const _SECTOR_DOT_LEGS = ((2, 3), (3, 1), (2, 1))

# K is the number of sectors, two for a midpoint or three for a tripling.
struct SectorTransition{K}
    a::BigInt
    b::BigInt
    shift::BigInt
    sector_type::SectorType{K}
end

# Positive integer lengths a and b, shift 1 ≤ s < b, and j of N copies in
# the shorter sector define a SectorTransition{2}.
function midpoint_transition(a::Integer, b::Integer, s::Integer, j::Integer, N::Integer)
    a >= 1 && 1 <= s < b && N >= 1 && 0 <= j <= N ||
        throw(ArgumentError("invalid midpoint dimensions or sector counts"))
    return SectorTransition(big(a), big(b), big(s), SectorType((j, big(N) - j)))
end

# Positive integer lengths a and b and three nonnegative integer counts
# j0, j1 and j2, whose sum is positive, define a SectorTransition{3}.
function tripling_transition(a::Integer, b::Integer, j0::Integer, j1::Integer, j2::Integer)
    a >= 1 && b >= 1 && big(j0) + j1 + j2 >= 1 ||
        throw(ArgumentError("invalid tripling dimensions or sector counts"))
    return SectorTransition(big(a), big(b), big(0), SectorType((j0, j1, j2)))
end

# A SectorTransition with two sectors is a midpoint transition.
_is_midpoint(::SectorTransition{K}) where {K} = K == 2

# Return the BigInt copy count from transition.sector_type.counts.
_sector_copies(transition) = sum(transition.sector_type.counts)

# The degree bound for integer stage 1 or 2 of a SectorTransition is a BigInt.
function transition_degree(transition::SectorTransition, stage::Integer)
    M = transition.sector_type.multiplicity
    stage == 1 && return 6 * _sector_copies(transition)
    stage == 2 && return 6 * (M - 1)^2
    return throw(ArgumentError("Claim 6.6 has stages 1 and 2"))
end

# Return a SectorTransition's three polynomial lengths as an NTuple{3,BigInt}.
function _sector_input_lengths(transition)
    a, b = transition.a, transition.b
    _is_midpoint(transition) || (b = 3b + a - 1)
    return (a, b, a + b - 1)
end

# For local_leg 2 or 3 of a SectorTransition{K}, return the block lengths as
# an NTuple{K,BigInt} in sector order.
function _sector_block_lengths(transition, local_leg)
    a, b, s = transition.a, transition.b, transition.shift
    if _is_midpoint(transition)
        length = local_leg == 2 ? b : a + b - 1
        return (length - s, length + s)
    end
    return local_leg == 2 ? (b, b + a - 1, b) : (b + a - 1, b, b + a - 1)
end

# For a SectorTransition and integer leg in 1:3, return the NTuple{6,BigInt}
# of input radices in orientation order.
function _sector_input_radices(transition, leg)
    lengths = _sector_input_lengths(transition)
    return ntuple(i -> lengths[LEG_PERMUTATIONS[i][leg]], 6)
end

# For a SectorTransition and integer leg in 1:3, return the NTuple{6,BigInt}
# of intermediate radices in orientation order.
function _sector_middle_radices(transition, leg)
    radices = _sector_input_radices(transition, leg)
    _is_midpoint(transition) || return radices
    return ntuple(6) do orientation
        LEG_PERMUTATIONS[orientation][leg] == 1 && return radices[orientation]
        return 2 * radices[orientation]
    end
end

# For a SectorTransition, integer leg and one-based integer sector, return
# an NTuple{6,BigInt} of output radices ordered by orientation.
function _sector_output_radices(transition, leg, sector)
    a, b, s = transition.a, transition.b, transition.shift
    if _is_midpoint(transition)
        b = sector == 1 ? b - s : b + s
    end
    lengths = (a, b, a + b - 1)
    return ntuple(i -> lengths[LEG_PERMUTATIONS[i][leg]], 6)
end

# Decode a SectorTransition's one-based integer digit in local_leg 1:3.
# The coordinate is an integer on leg 1 or an integer pair (sector, index).
function _sector_coordinate(transition, local_leg, digit)
    local_leg == 1 && return digit
    for (sector, length) in enumerate(_sector_block_lengths(transition, local_leg))
        digit <= length && return (sector, digit)
        digit -= length
    end
    return throw(BoundsError())
end

# leg and orientation are integers in 1:3 and 1:6. Return the shared dot
# factor axis as Int 1 or 2, or 0 if neither factor shares it.
function _sector_dot_axis(leg, orientation)
    shared = findfirst(==(1), LEG_PERMUTATIONS[orientation])
    first_leg, second_leg = _SECTOR_DOT_LEGS[leg]
    shared == first_leg && return 1
    shared == second_leg && return 2
    return 0
end

# Use a SectorTransition, integer local leg, dot copy and source index, and
# a target from _sector_coordinate. For a Rational{BigInt} or PhaseSum
# monomial t, return a coefficient of either type, or exact zero.
function _sector_first_value(transition, local_leg, dot_copy, source, target, t)
    value = Ref{ExactScalar}(zero(t))
    # Receive an integer or (sector, index) coordinate and a Rational{BigInt}
    # or PhaseSum coefficient. Record the match and return nothing.
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

# Use a SectorTransition, integer local leg and digit, and a target from
# _sector_coordinate. Return one or two integer pairs (dot_copy, source_index).
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

# Construct the stage-one LegMap for a SectorTransition and integer leg in 1:3.
# t is a normalized Rational{BigInt} or PhaseSum monomial.
function _sector_first_leg(transition, leg, t)
    count = _sector_copies(transition)
    units = (2 * transition.sector_type.multiplicity)^6
    source_radices = _sector_input_radices(transition, leg)
    middle_radices = _sector_middle_radices(transition, leg)
    source_q = prod(source_radices)^count
    dot_size = _is_midpoint(transition) ? big(4)^count : big(1)
    source_dim = units * source_q * dot_size^2
    target_dim = units * prod(middle_radices)^count
    # A BigInt target row and source column select a Rational{BigInt} or PhaseSum.
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
            value *= _sector_first_value(
                transition, local_leg, dot_copy, source + 1, target, t
            )
            iszero(value) && return value
        end
        return value
    end
    # For a BigInt target row, yield (BigInt source column, coefficient) pairs
    # with Rational{BigInt} or PhaseSum coefficients.
    function entries(target_row)
        new, unit = divrem(target_row - 1, units)
        source_column = unit + 1
        value = one(t)
        source_stride = units
        matrix_strides = [units * source_q, units * source_q * dot_size]
        alternatives = NTuple{2,Tuple{BigInt,ExactScalar}}[]
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
            # Map an integer source pair to a BigInt offset and exact weight.
            options = map(sources) do (dot_copy, index)
                offset = (dot_copy - 1) * dot_stride + (index - 1) * source_stride
                weight = _sector_first_value(
                    transition, local_leg, dot_copy, index, target, t
                )
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
        # A zero-based BigInt choice mask selects a source column and weight.
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
        return (contribution(bits) for bits in 0:(big(2) ^ length(alternatives) - 1))
    end
    return LegMap(source_dim, target_dim, coefficient, entries)
end

# The two Matrix{BigInt} coordinate tables index orientations by row and
# tensor copies by column. Fill the row for the integer orientation using
# the SectorTransition, integer local leg, Vector{Int} of sector indices
# and Vector{Int} of cumulative counts starting at zero.
function _sector_source_coordinates!(
    input_coordinates, transition, local_leg, orientation, word, output_coordinates, offsets
)
    positions = copy(offsets)
    block_offsets = if local_leg == 1
        nothing
    else
        cumsum((big(0), _sector_block_lengths(transition, local_leg)...))
    end
    middle_orientation = orientation
    if !_is_midpoint(transition)
        swapped = map(index -> index == 1 ? 1 : 5 - index, LEG_PERMUTATIONS[orientation])
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

# Construct the stage-two LegMap for a SectorTransition and integer leg in 1:3.
# t is a normalized Rational{BigInt} or PhaseSum monomial, and L is the BigInt
# Fourier order chosen by _admissible_separation_order.
function _sector_second_leg(transition, leg, t, L)
    count = _sector_copies(transition)
    sector_type = transition.sector_type
    M = sector_type.multiplicity
    physical_order = 2M
    input_units = physical_order^6
    copy_strides = ntuple(i -> physical_order^(i - 1), 6)
    # Iterate over one NTuple{6,BigInt} of zero-based Fourier digits at a time.
    active_digits = Iterators.product(ntuple(_ -> 0:(L - 1), 6)...)
    output_units = M^6
    middle_radices = _sector_middle_radices(transition, leg)
    output_radices = ntuple(length(sector_type.counts)) do sector
        return _sector_output_radices(transition, leg, sector)
    end
    output_q = prod(
        prod(radices)^n for (radices, n) in zip(output_radices, sector_type.counts)
    )
    source_dim = input_units * prod(middle_radices)^count
    target_dim = output_units * output_q * M^4
    # A BigInt target row gives a zero-based BigInt packed input index, six
    # phase multipliers in a Vector{BigInt}, and a BigInt Laurent exponent.
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
            _sector_source_coordinates!(
                input_coordinates,
                transition,
                local_leg,
                orientation,
                word,
                output_coordinates,
                offsets,
            )
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
            input_q =
                input_q * middle_radices[orientation] +
                input_coordinates[orientation, copy] - 1
        end
        return (input_q, phases, weight)
    end
    # Combine NTuple{6,BigInt} digits, Vector{BigInt} multipliers and a
    # Rational{BigInt} or PhaseSum scale into an exact scalar weight.
    function phase_coefficient(digits, phases, scale)
        phase = sum(digits[i] * phases[i] for i in 1:6)
        return iszero(mod(phase, L)) ? scale : root_of_unity(L, phase) * scale
    end
    # A BigInt target row and source column select a Rational{BigInt} or PhaseSum.
    function coefficient(target_row, source_column)
        old, copy_unit = divrem(source_column - 1, input_units)
        digits = ntuple(i -> div(copy_unit, copy_strides[i]) % physical_order, 6)
        any(>=(L), digits) && return zero(t)
        input_q, phases, weight = row_parameters(target_row)
        old == input_q || return zero(t)
        # Each global leg is the local third leg in exactly two orientations.
        scale = t^weight / L^2
        return phase_coefficient(digits, phases, scale)
    end
    # For a BigInt target row, yield (BigInt source column, coefficient) pairs
    # with Rational{BigInt} or PhaseSum coefficients.
    function entries(target_row)
        input_q, phases, weight = row_parameters(target_row)
        scale = t^weight / L^2
        base_column = input_q * input_units + 1
        return (
            (
                base_column + sum(digits[i] * copy_strides[i] for i in 1:6),
                phase_coefficient(digits, phases, scale),
            ) for digits in active_digits
        )
    end
    return LegMap(source_dim, target_dim, coefficient, entries)
end

"""
    transition_restriction(transition, stage, t; admissible_order=nothing)

Return a `TensorRestriction` for integer `stage` 1 or 2 of Claim 6.6.
`transition` is a `SectorTransition{2}` or `SectorTransition{3}`. `t` is a
nonzero exact rational or an invertible `PhaseSum` monomial, as accepted by
`evaluation_parameter`. Input factors are the unit tensor, the balanced seed
copies, then the matrix tensor if needed. Output factors are the returned
unit tensor, the child seed copies, then the matrix tensor. The shorter
child copies come first for midpoint transitions. The intermediate space
holds the same unit factor and the six oriented sector tensors per copy.
For `M = transition.sector_type.multiplicity`, `admissible_order` is `nothing`
to use `2M` or an integer equal to `2M` or `2M-1`. The second stage keeps
the physical unit coordinates in radix `2M`. For the smaller order, the
extra digit is discarded in each orientation as in §7.
"""
function transition_restriction(
    transition::SectorTransition, stage::Integer, t; admissible_order=nothing
)
    t = evaluation_parameter(t)
    L = _admissible_separation_order(transition.sector_type.multiplicity, admissible_order)
    legs = if stage == 1
        ntuple(leg -> _sector_first_leg(transition, leg, t), 3)
    elseif stage == 2
        ntuple(leg -> _sector_second_leg(transition, leg, t, L), 3)
    else
        throw(ArgumentError("Claim 6.6 has stages 1 and 2"))
    end
    return TensorRestriction(legs...)
end
