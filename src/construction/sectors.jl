# Claim 6.6, with all six orientations in the order used by the balanced seed.

"""
    _SECTOR_DOT_LEGS

Map each balanced leg's two matrix axes to the legs shared by their dot factors.

`B_X` uses the column index, `B_Y` the row index, and `B_Z` the contraction
index. The axes on legs 1, 2 and 3 are ordered as (row, contraction),
(contraction, column) and (row, column), respectively. Each axis combines
the digits from two orientations.
"""
const _SECTOR_DOT_LEGS = ((2, 3), (3, 1), (2, 1))

"""
    SectorTransition{K}
    SectorTransition(a::BigInt, b::BigInt, shift::BigInt, sector_type::SectorType{K})
    SectorTransition{K}(a, b, shift, sector_type)

Store the lengths, shift and fixed type class for the two stages of Claim 6.6.

`K` is two for a midpoint and three for a tripling. In a midpoint,
`b` is the source second-input length. In a tripling, `b` is the child
second-input length and `shift` is zero. Use `midpoint_transition` or
`tripling_transition` to validate the lengths and sector counts.
"""
struct SectorTransition{K}
    a::BigInt
    b::BigInt
    shift::BigInt
    sector_type::SectorType{K}
end

"""
    midpoint_transition(a::Integer, b::Integer, s::Integer, j::Integer, N::Integer)

Build a midpoint transition from `C(a,b)` to sectors of lengths `b-s` and `b+s`.

Require `a ≥ 1`, `1 ≤ s < b`, and `N ≥ 1`. Assign `j` copies to the
shorter sector and `N-j` to the longer sector.
"""
function midpoint_transition(a::Integer, b::Integer, s::Integer, j::Integer, N::Integer)
    a >= 1 && 1 <= s < b && N >= 1 && 0 <= j <= N ||
        throw(ArgumentError("invalid midpoint dimensions or sector counts"))
    return SectorTransition(big(a), big(b), big(s), SectorType((j, big(N) - j)))
end

"""
    tripling_transition(a::Integer, b::Integer, j0::Integer, j1::Integer, j2::Integer)

Build a three-sector transition from `C(a,3b+a-1)` to sectors based on `C(a,b)`.

Require positive lengths and nonnegative counts with a positive sum.
Assign `j0`, `j1` and `j2` copies to the left, middle and right sectors
in that order.
"""
function tripling_transition(a::Integer, b::Integer, j0::Integer, j1::Integer, j2::Integer)
    a >= 1 && b >= 1 && big(j0) + j1 + j2 >= 1 ||
        throw(ArgumentError("invalid tripling dimensions or sector counts"))
    return SectorTransition(big(a), big(b), big(0), SectorType((j0, j1, j2)))
end

"""
    _is_midpoint(::SectorTransition{K}) where {K}

Return whether the transition has the two midpoint sectors.
"""
_is_midpoint(::SectorTransition{K}) where {K} = K == 2

"""
    _sector_copies(transition)::BigInt

Return the total number of tensor copies in the transition's fixed type class.
"""
_sector_copies(transition) = sum(transition.sector_type.counts)

"""
    transition_degree(transition::SectorTransition, stage::Integer)::BigInt

Bound the degree of one stage of the balanced degeneration.

For `N` copies and a type class of size `M`, stage 1 has bound `6N`
and stage 2 has bound `6(M-1)^2`.
"""
function transition_degree(transition::SectorTransition, stage::Integer)
    M = transition.sector_type.multiplicity
    stage == 1 && return 6 * _sector_copies(transition)
    stage == 2 && return 6 * (M - 1)^2
    return throw(ArgumentError("Claim 6.6 has stages 1 and 2"))
end

"""
    _sector_input_lengths(transition)::NTuple{3,BigInt}

Return the source polynomial lengths in the original leg order.

The first two lengths describe the inputs to polynomial multiplication.
The third length describes the output.
"""
function _sector_input_lengths(transition)
    a, b = transition.a, transition.b
    _is_midpoint(transition) || (b = 3b + a - 1)
    return (a, b, a + b - 1)
end

"""
    _sector_block_lengths(transition, local_leg)

Return the lengths of the disjoint blocks on local leg 2 or 3 in sector order.

In a tripling, the middle block exchanges the second-input and output
lengths. The shared first leg has a single set of coordinates.
"""
function _sector_block_lengths(transition, local_leg)
    a, b, s = transition.a, transition.b, transition.shift
    if _is_midpoint(transition)
        length = local_leg == 2 ? b : a + b - 1
        return (length - s, length + s)
    end
    return local_leg == 2 ? (b, b + a - 1, b) : (b + a - 1, b, b + a - 1)
end

"""
    _sector_input_radices(transition, leg)::NTuple{6,BigInt}

Return the six source seed radices on one balanced leg.

The tuple follows `LEG_PERMUTATIONS`. Its first radix varies fastest
when packing an individual seed copy.
"""
function _sector_input_radices(transition, leg)
    lengths = _sector_input_lengths(transition)
    return ntuple(i -> lengths[LEG_PERMUTATIONS[i][leg]], 6)
end

"""
    _sector_middle_radices(transition, leg)::NTuple{6,BigInt}

Return the six intermediate radices on one balanced leg.

A midpoint doubles the radix of each orientation in which `leg`
is a nonshared local leg. A tripling partitions its source coordinates.
"""
function _sector_middle_radices(transition, leg)
    radices = _sector_input_radices(transition, leg)
    _is_midpoint(transition) || return radices
    return ntuple(6) do orientation
        LEG_PERMUTATIONS[orientation][leg] == 1 && return radices[orientation]
        return 2 * radices[orientation]
    end
end

"""
    _sector_output_radices(transition, leg, sector)::NTuple{6,BigInt}

Return the six child seed radices for a one-based sector and a balanced leg.

The radices follow `LEG_PERMUTATIONS` after restoring the middle tripling
sector to the balanced seed's orientation order.
"""
function _sector_output_radices(transition, leg, sector)
    a, b, s = transition.a, transition.b, transition.shift
    if _is_midpoint(transition)
        b = sector == 1 ? b - s : b + s
    end
    lengths = (a, b, a + b - 1)
    return ntuple(i -> lengths[LEG_PERMUTATIONS[i][leg]], 6)
end

"""
    _sector_coordinate(transition, local_leg, digit)

Decode a one-based intermediate digit in the original polynomial leg order.

Return the integer digit on the shared first leg or a one-based pair
`(sector, index)` on legs 2 and 3.
"""
function _sector_coordinate(transition, local_leg, digit)
    local_leg == 1 && return digit
    for (sector, length) in enumerate(_sector_block_lengths(transition, local_leg))
        digit <= length && return (sector, digit)
        digit -= length
    end
    return throw(BoundsError())
end

"""
    _sector_dot_axis(leg, orientation)::Int

Find the matrix axis whose digits include the specified orientation's dot factor.

`leg` is in `1:3` and `orientation` is in `1:6`. Return 1 or 2 in the
order of `_SECTOR_DOT_LEGS`. Return zero when the orientation shares the
given leg.
"""
function _sector_dot_axis(leg, orientation)
    shared = findfirst(==(1), LEG_PERMUTATIONS[orientation])
    first_leg, second_leg = _SECTOR_DOT_LEGS[leg]
    shared == first_leg && return 1
    shared == second_leg && return 2
    return 0
end

"""
    _sector_first_value(transition, local_leg, dot_copy, source, target, t)

Find the coefficient of an intermediate variable in the image of a source variable.

`dot_copy` and `source` are one-based. Use a target coordinate from
`_sector_coordinate` and a parameter from `evaluation_parameter`. A missing
target has coefficient zero.
"""
function _sector_first_value(transition, local_leg, dot_copy, source, target, t)
    value = Ref{ExactScalar}(zero(t))
    # Record the exact coefficient when the emitted coordinate matches target.
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

"""
    _sector_first_sources(transition, local_leg, target, digit)

List the local source variables contributing to a stage-one target variable.

`digit` is the one-based packed form of `target`. Return one or two
one-based pairs `(dot_copy, source_index)`. A tripling or a shared local
leg uses `dot_copy == 1`.
"""
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

"""
    _sector_first_leg(transition, leg, t)::LegMap

Build the source-to-intermediate substitution for one balanced leg.

Keep the unit digit first. For a midpoint, unpack the source matrix index
into local dot-copy digits. Combine the local substitutions at the
normalized Laurent parameter `t`.
"""
function _sector_first_leg(transition, leg, t)
    count = _sector_copies(transition)
    units = (2 * transition.sector_type.multiplicity)^6
    source_radices = _sector_input_radices(transition, leg)
    middle_radices = _sector_middle_radices(transition, leg)
    source_q = prod(source_radices)^count
    dot_size = _is_midpoint(transition) ? big(4)^count : big(1)
    source_dim = units * source_q * dot_size^2
    target_dim = units * prod(middle_radices)^count
    # Read a one-based target row and source column and multiply their local weights.
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
    # Yield one-based (source column, exact weight) pairs for the target row.
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
        # Unpack a zero-based mask into one source choice per branching orientation.
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

"""
    _sector_source_coordinates!(
        input_coordinates, transition, local_leg, orientation, word,
        output_coordinates, offsets
    )::Nothing

Reconstruct one orientation's intermediate coordinates from its child seed coordinates.

Both coordinate tables index orientations by row and tensor copies by
column. `word` gives the intermediate copy order. `offsets` starts at zero
and gives the cumulative counts used to index the child copies in sector
order. The middle tripling sector exchanges its last two legs and reverses
the indices of its first leg.
"""
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

"""
    _sector_second_leg(transition, leg, t, L)::LegMap

Build the intermediate-to-separated substitution for one balanced leg.

`t` is a normalized Laurent parameter and `L` is the chosen Fourier order.
Each target row fixes one set of intermediate polynomial coordinates.
Its source support ranges over the active Fourier digits, packed in radix
`2M` for type class size `M`.
"""
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
    output_q = prod(prod(radices)^n for
                    (radices, n) in zip(output_radices, sector_type.counts))
    source_dim = input_units * prod(middle_radices)^count
    target_dim = output_units * output_q * M^4
    # Decode a one-based target row into a zero-based packed polynomial index,
    # six orientation-specific phase multipliers, and the Laurent exponent.
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
    # Multiply the normalized Laurent scale by the root-of-unity phase
    # selected by the six zero-based active digits.
    function phase_coefficient(digits, phases, scale)
        phase = sum(digits[i] * phases[i] for i in 1:6)
        return iszero(mod(phase, L)) ? scale : root_of_unity(L, phase) * scale
    end
    # Read the entry at a one-based target row and source column, masking
    # inactive digits and polynomial coordinates outside the row's support.
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
    # Yield one-based (source column, exact weight) pairs for the active
    # Fourier copies contributing to the target row.
    function entries(target_row)
        input_q, phases, weight = row_parameters(target_row)
        scale = t^weight / L^2
        base_column = input_q * input_units + 1
        return ((
            base_column + sum(digits[i] * copy_strides[i] for i in 1:6),
            phase_coefficient(digits, phases, scale),
        ) for digits in active_digits)
    end
    return LegMap(source_dim, target_dim, coefficient, entries)
end

"""
    transition_restriction(
        transition::SectorTransition, stage::Integer, t; admissible_order=nothing
    )::TensorRestriction

Build the exact restriction at parameter `t` for one stage of Claim 6.6.

Stage 1 maps source factors ordered as the unit tensor, balanced seed
copies, and the matrix tensor when needed for a midpoint. Its intermediate
target contains the unit tensor and six oriented sector tensors per copy.
Stage 2 maps these intermediate coordinates to the returned unit tensor,
child seed copies, and matrix tensor. Shorter child copies come first
for a midpoint. Each leg map has one-based target rows and source
columns. The first factor varies fastest.

`t` is a nonzero exact rational or an invertible `PhaseSum` monomial, as
accepted by `evaluation_parameter`.
For `M = transition.sector_type.multiplicity`, `admissible_order` is `nothing`
to use `2M` or an integer equal to `2M` or `2M-1`. Choose an order invertible
in the target field. The second stage keeps the physical unit coordinates in
radix `2M`. For the smaller order, the extra digit is discarded in each
orientation as in §7.
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
