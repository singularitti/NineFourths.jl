# A column callback expands the image of one source variable under substitution.
# Polynomial and sector indices are one-based. Fourier exponents are zero-based.

"""
    evaluation_parameter(t)::Rational{BigInt}

Normalize a finite, nonzero rational parameter for a Laurent substitution.

Use `rational_result` to convert the exact input before checking that its
negative powers are defined.
"""
function evaluation_parameter(t)
    parameter = rational_result(t)
    isfinite(parameter) && !iszero(parameter) ||
        throw(DomainError(t, "Laurent substitutions require a finite nonzero parameter"))
    return parameter
end

"""
    evaluation_parameter(t::PhaseSum)::PhaseSum

Validate a single phase monomial as a Laurent evaluation parameter.

Its rational weight must be finite and nonzero. Return the supplied
monomial.
"""
function evaluation_parameter(t::PhaseSum)
    length(t.terms) == 1 ||
        throw(DomainError(t, "Laurent substitutions require an invertible phase monomial"))
    evaluation_parameter(only(values(t.terms)))
    return t
end

"""
    midpoint_column(emit, a, b, s, leg, copy, index, t)::Nothing

Substitute a source variable of `C(a,b) ⊗ B_X(2)` as in Lemma 5.6.

Call `emit(coordinate, coefficient)` for each term in its image. The lengths
`a`, `b` and shift `s` are integers with `a ≥ 1` and `1 ≤ s < b`. `leg`,
`copy` and `index` are one-based integers. `t` is a nonzero exact rational
or an invertible `PhaseSum` monomial, as accepted by `evaluation_parameter`.

The callback receives a `Rational{BigInt}` or `PhaseSum` coefficient. The
coordinate is an integer on leg 1 and a pair of integers `(sector, index)`
on legs 2 and 3. Sector 1 is the `b-s` kernel and sector 2 is the `b+s`
complement.
"""
function midpoint_column(emit, a, b, s, leg, copy, index, t)
    t = evaluation_parameter(t)
    if leg == 1
        emit(index, one(t))
    elseif leg == 2
        if copy == 1
            emit((2, index), one(t))
            index > s && emit((1, index - s), -inv(t))
        elseif index <= b - s
            emit((1, index), inv(t))
        else
            emit((2, index + s), one(t))
        end
    else
        if copy == 1
            emit((2, index), one(t))
        else
            emit((2, index + s), one(t))
            index <= a + b - 1 - s && emit((1, index), t)
        end
    end
    return nothing
end

"""
    tripling_column(emit, a, b, leg, index, t)::Nothing

Substitute a source variable of `C(a,3b+a-1)` as in Lemma 5.2.

Call `emit(coordinate, coefficient)` for each term in its image. The lengths `a`
and `b` are positive integers, and `leg` and `index` are one-based integers.
`t` is a nonzero exact rational or an invertible `PhaseSum` monomial, as
accepted by `evaluation_parameter`.

The callback receives a `Rational{BigInt}` or `PhaseSum` coefficient. The
coordinate is an integer on leg 1 and a pair of integers `(sector, index)`
on legs 2 and 3. The middle sector still has its first-input indices
reversed and its second and third legs exchanged.
"""
function tripling_column(emit, a, b, leg, index, t)
    t = evaluation_parameter(t)
    if leg == 1
        emit(index, one(t))
        return nothing
    end
    left_length = leg == 2 ? b : b + a - 1
    middle_end = 2b + a - 1
    if index <= left_length
        emit((1, index), one(t))
    elseif index <= middle_end
        emit((2, index - left_length), leg == 2 ? t : inv(t))
    else
        emit((3, index - middle_end), one(t))
    end
    return nothing
end

"""
    type_multiplicity(counts)::BigInt

Return the multinomial coefficient of a finite iterable of nonnegative integer counts.
"""
function type_multiplicity(counts)
    total = big(0)
    multiplicity = big(1)
    for count in counts
        count >= 0 || throw(DomainError(count, "sector counts must be nonnegative"))
        total += count
        multiplicity *= binomial(total, count)
    end
    return multiplicity
end

"""
    SectorType{K}
    SectorType(counts::NTuple{K,BigInt}, multiplicity::BigInt)
    SectorType{K}(counts, multiplicity)

Store `K` sector counts and the corresponding multinomial coefficient.

The two-argument constructors take the coefficient as supplied. Use
`SectorType(counts)` to compute it from the counts.
"""
struct SectorType{K}
    counts::NTuple{K,BigInt}
    multiplicity::BigInt
end

"""
    _exact_sector_count(count::Integer)::BigInt

Convert a sector count to `BigInt` before computing the multinomial coefficient.
"""
_exact_sector_count(count::Integer) = BigInt(count)

"""
    SectorType(counts)

Construct a fixed type class from a finite iterable of nonnegative integer counts.

Store the counts in iteration order as an `NTuple{K,BigInt}` and compute
their multinomial coefficient with `type_multiplicity`.
"""
function SectorType(counts)
    exact_counts = Tuple(_exact_sector_count(count) for count in counts)
    return SectorType(exact_counts, type_multiplicity(exact_counts))
end

"""
    type_rank(sector_type, word)::Union{BigInt,Nothing}

Find the one-based lexicographic rank of a word in a fixed type class.

`word` is an iterable of one-based integer sector indices. Return
`nothing` when its counts differ from those of `sector_type` or it
contains an index outside the sector range.
"""
function type_rank(sector_type, word)
    remaining = collect(sector_type.counts)
    slots = sum(remaining; init=big(0))
    completions = sector_type.multiplicity
    rank = big(1)
    for sector in word
        iszero(slots) && return nothing
        1 <= sector <= length(remaining) || return nothing
        iszero(remaining[sector]) && return nothing
        for previous in 1:(sector - 1)
            rank += div(completions * remaining[previous], slots)
        end
        completions = div(completions * remaining[sector], slots)
        remaining[sector] -= 1
        slots -= 1
    end
    return iszero(slots) ? rank : nothing
end

"""
    type_word(sector_type, rank::Integer)::Vector{Int}

Recover the word at a one-based lexicographic rank in a fixed type class.

The rank ranges from 1 through `sector_type.multiplicity`. The total
count must fit in an `Int` to allocate the word.
"""
function type_word(sector_type, rank::Integer)
    1 <= rank <= sector_type.multiplicity ||
        throw(BoundsError(1:sector_type.multiplicity, rank))
    remaining = collect(sector_type.counts)
    slots = sum(remaining; init=big(0))
    completions = sector_type.multiplicity
    word = Vector{Int}(undef, Int(slots))
    for position in eachindex(word)
        for sector in eachindex(remaining)
            options = div(completions * remaining[sector], slots)
            if rank <= options
                word[position] = sector
                remaining[sector] -= 1
                completions = options
                slots -= 1
                break
            end
            rank -= options
        end
    end
    return word
end

"""
    ordered_sector_indices(sector_type, word, coordinates)::Tuple

Group source indices by sector while preserving their order within each sector.

Supply a word in the given type class and a sized iterable of indices
with one coordinate per factor of the word.
"""
function ordered_sector_indices(sector_type, word, coordinates)
    positions = cumsum([0; Int.(collect(sector_type.counts))])
    length(coordinates) == last(positions) ||
        throw(DimensionMismatch("expected one source coordinate per tensor factor"))
    ordered = Vector{eltype(coordinates)}(undef, length(coordinates))
    for (sector, index) in zip(word, coordinates)
        positions[sector] += 1
        ordered[positions[sector]] = index
    end
    return Tuple(ordered)
end

"""
    separation_character(leg, i, k, ρ) -> (phase, weight)

Return the Fourier and Laurent exponents for one leg of the separation map.

`leg` is in `1:3`. The type rank `i`, dot index `k` and copy number `ρ`
are zero-based. The exponents contribute the factor `ζ^phase * t^weight`.
"""
function separation_character(leg, i, k, ρ)
    leg == 1 && return (ρ * i, i^2)
    leg == 2 && return (ρ * (k - i), 2i * k - i^2)
    return (-ρ * k, -2i * k)
end

"""
    _admissible_separation_order(M, admissible_order)

Select a Fourier order for a positive `BigInt` multiplicity `M`.

Use `2M` if `admissible_order` is `nothing`, or validate an explicit
integer order equal to `2M` or `2M-1`. The caller chooses an order
invertible in its field.
"""
function _admissible_separation_order(M, admissible_order)
    isnothing(admissible_order) && return 2M
    admissible_order isa Integer && 2M - 1 <= admissible_order <= 2M ||
        throw(ArgumentError("the Fourier order must equal 2M or 2M−1"))
    return big(admissible_order)
end

"""
    separation_column(emit, sector_type, leg, ρ, coordinates, t,
                      rootpower=nothing; admissible_order=nothing)::Nothing

Substitute a source variable of `I_(2M) ⊗ (∑ᵢ Tᵢ)^⊗N` using Lemmas 5.1 and 5.5.

`sector_type` is a `SectorType` and `M` is its `BigInt` multiplicity.
`leg` is an integer in `1:3`, and `ρ` is an integer copy index in `0:2M-1`.
`admissible_order` is `nothing` for `L = 2M` or an integer equal to `2M`
or `2M-1` as in §7. The first `L` copies are active. `t` is a nonzero
exact rational or an invertible `PhaseSum` monomial, as accepted by
`evaluation_parameter`.

The finite iterable `coordinates` supplies one integer index per factor
on leg 1 or one pair of integers `(sector, index)` per factor on legs 2
and 3. Words outside the fixed type are dropped.
`emit(coordinate, coefficient)` receives one term at a time. Each image
coordinate is `(type_rank, dot_index, canonical_indices)` with two
one-based integers and a tuple of integer indices. The first leg uses
`dot_index == 1`.

`rootpower` is `nothing` or a callable mapping an integer exponent `e` to
the `e`th power of a primitive `L`th root of unity. Its result must support
multiplication by the exact evaluation coefficient. With the default root,
the emitted coefficient is a `Rational{BigInt}` or `PhaseSum`.
"""
function separation_column(
    emit, sector_type, leg, ρ, coordinates, t, rootpower=nothing; admissible_order=nothing
)
    t = evaluation_parameter(t)
    M = sector_type.multiplicity
    L = _admissible_separation_order(M, admissible_order)
    ρ >= L && return nothing
    rootpower = isnothing(rootpower) ? exponent -> root_of_unity(L, exponent) : rootpower
    coordinates = collect(coordinates)
    if leg == 1
        for j in 0:(M - 1)
            word = type_word(sector_type, j + 1)
            ordered = ordered_sector_indices(sector_type, word, coordinates)
            phase, weight = separation_character(leg, j, 0, ρ)
            emit((j + 1, 1, ordered), rootpower(phase) * t^weight)
        end
    else
        word = map(first, coordinates)
        rank = type_rank(sector_type, word)
        isnothing(rank) && return nothing
        ordered = ordered_sector_indices(sector_type, word, map(last, coordinates))
        i = rank - 1
        for k in 0:(M - 1)
            phase, weight = separation_character(leg, i, k, ρ)
            scale = t^weight
            leg == 3 && (scale /= L)
            emit((rank, k + 1, ordered), rootpower(phase) * scale)
        end
    end
    return nothing
end
