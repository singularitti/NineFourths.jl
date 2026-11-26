# A column callback expands the image of one source variable under substitution.
# Polynomial and sector indices are one-based. Fourier exponents are zero-based.

function evaluation_parameter(t::Union{Integer,Rational})
    isfinite(t) && !iszero(t) ||
        throw(DomainError(t, "Laurent substitutions require a finite nonzero parameter"))
    return Rational{BigInt}(t)
end

function evaluation_parameter(t::PhaseSum)
    length(t.terms) == 1 ||
        throw(DomainError(t, "Laurent substitutions require an invertible phase monomial"))
    evaluation_parameter(only(values(t.terms)))
    return t
end

"""
    midpoint_column(emit, a, b, s, leg, copy, index, t)

Substitute a variable of `C(a,b) ⊗ B_X(2)` as in Lemma 5.6. The first leg
uses a scalar index. On each other leg the output is `(sector, index)`,
with sector 1 the `b-s` kernel and sector 2 the `b+s` complement.
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
    tripling_column(emit, a, b, leg, index, t)

Substitute a variable of `C(a,3b+a-1)` as in Lemma 5.2. On the second and
third legs the image is indexed by `(sector, index)` in the three
consecutive intervals. The middle sector still has its first-input
indices reversed and its second and third legs exchanged.
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

struct SectorType{K}
    counts::NTuple{K,BigInt}
    multiplicity::BigInt
end

function SectorType(counts::NTuple{K,Integer}) where {K}
    return SectorType{K}(map(big, counts), type_multiplicity(counts))
end

function type_rank(sector_type::SectorType, word)
    remaining = collect(sector_type.counts)
    slots = sum(remaining)
    BigInt(length(word)) == slots || return nothing
    completions = sector_type.multiplicity
    rank = big(1)
    for sector in word
        1 <= sector <= length(remaining) || return nothing
        iszero(remaining[sector]) && return nothing
        for previous in 1:(sector - 1)
            rank += div(completions * remaining[previous], slots)
        end
        completions = div(completions * remaining[sector], slots)
        remaining[sector] -= 1
        slots -= 1
    end
    return rank
end

function type_word(sector_type::SectorType, rank::Integer)
    1 <= rank <= sector_type.multiplicity ||
        throw(BoundsError(1:sector_type.multiplicity, rank))
    remaining = collect(sector_type.counts)
    slots = sum(remaining)
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

function ordered_sector_indices(sector_type::SectorType, word, coordinates)
    positions = cumsum([0; Int.(collect(sector_type.counts))])
    ordered = Vector{eltype(coordinates)}(undef, length(coordinates))
    for (sector, index) in zip(word, coordinates)
        positions[sector] += 1
        ordered[positions[sector]] = index
    end
    return Tuple(ordered)
end

function separation_character(leg, i, k, ρ)
    if leg == 1
        return (ρ * i, i^2)
    elseif leg == 2
        return (ρ * (k - i), 2i * k - i^2)
    else
        return (-ρ * k, -2i * k)
    end
end

function _admissible_separation_order(M, admissible_order)
    isnothing(admissible_order) && return 2M
    admissible_order isa Integer && 2M - 1 <= admissible_order <= 2M ||
        throw(ArgumentError("the Fourier order must equal 2M or 2M−1"))
    return big(admissible_order)
end

"""
    separation_column(emit, sector_type, leg, ρ, coordinates, t,
                      [rootpower]; admissible_order=nothing)

Substitute one variable of `I_(2M) ⊗ (∑ᵢ Tᵢ)^⊗N` using Lemmas 5.1 and 5.5,
where `M = sector_type.multiplicity`. Use Fourier order `L = 2M` by default
or choose `L = 2M-1` as in §7. Copies are numbered from zero through `2M-1`.
The first `L` copies are active.
If supplied, `rootpower(e)` returns the `e`th power of a primitive
`L`th root of unity. Each image coordinate is
`(type_rank, dot_index, canonical_indices)`. The shared first leg uses
`dot_index == 1`. The second and third legs take a source coordinate
`(sector, index)` per tensor factor and drop words outside the fixed type.
"""
function separation_column(emit, sector_type::SectorType, leg, ρ, coordinates, t,
                           rootpower=nothing; admissible_order=nothing)
    t = evaluation_parameter(t)
    M = sector_type.multiplicity
    L = _admissible_separation_order(M, admissible_order)
    ρ >= L && return nothing
    rootpower = isnothing(rootpower) ? exponent -> root_of_unity(L, exponent) : rootpower
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
