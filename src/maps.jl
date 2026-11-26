"""
One leg of a tensor restriction. Columns label source variables and rows
label target variables. Entries and dimensions stay exact.
"""
struct LegMap
    in_dim::BigInt
    out_dim::BigInt
    entry::Function
    support::Union{Nothing,Function}
    selection::Union{Nothing,Function}
    function LegMap(in_dim, out_dim, entry, support=nothing, selection=nothing)
        in_dim >= 1 && out_dim >= 1 || throw(ArgumentError("empty tensor leg"))
        return new(big(in_dim), big(out_dim), entry, support, selection)
    end
end

Base.size(m::LegMap) = (m.out_dim, m.in_dim)
Base.size(m::LegMap, axis::Integer) = size(m)[axis]

function Base.getindex(m::LegMap, row::Integer, col::Integer)
    1 <= row <= m.out_dim && 1 <= col <= m.in_dim || throw(BoundsError(m, (row, col)))
    return m.entry(big(row), big(col))
end

function row_entries(m::LegMap, row::Integer)
    1 <= row <= m.out_dim || throw(BoundsError(m, row))
    isnothing(m.support) || return m.support(big(row))
    return (
        (col, weight) for col in 1:m.in_dim for
        weight in (m.entry(row, col),) if !iszero(weight)
    )
end

"""A row selects one source variable with coefficient one, or zero if its index is zero."""
function selection_map(in_dim, out_dim, source_column)
    function entries(row)
        col = source_column(row)
        return iszero(col) ? () : ((col, 1),)
    end
    return LegMap(
        in_dim,
        out_dim,
        (row, col) -> Int(source_column(row) == col),
        entries,
        source_column,
    )
end

struct TensorRestriction
    legs::NTuple{3,LegMap}
end

TensorRestriction(x::LegMap, y::LegMap, z::LegMap) = TensorRestriction((x, y, z))
source_dims(r::TensorRestriction) = map(m -> m.in_dim, r.legs)
target_dims(r::TensorRestriction) = map(m -> m.out_dim, r.legs)
unit_dims(k::Integer) = (big(k), big(k), big(k))
mm_dims(k::Integer) = unit_dims(big(k)^2)

function identity_restriction(dims)
    return TensorRestriction(ntuple(i -> selection_map(dims[i], dims[i], identity), 3))
end

function _compose_maps(a::LegMap, b::LegMap)
    a.out_dim == b.in_dim ||
        throw(DimensionMismatch("tensor restriction endpoints do not match"))
    if !isnothing(a.selection) && !isnothing(b.selection)
        function source_col(row)
            mid = b.selection(row)
            return iszero(mid) ? 0 : a.selection(mid)
        end
        return selection_map(a.in_dim, b.out_dim, source_col)
    end
    function entry(row, col)
        value = 0
        for (mid, weight) in row_entries(b, row)
            left = a[mid, col]
            iszero(left) || (value += weight * left)
        end
        return value
    end
    # Contributions at the same source index may occur several times.
    # Downstream contractions add them, including exact cancellations.
    function entries(row)
        return (
            (col, v * w) for (mid, w) in row_entries(b, row) for
            (col, v) in row_entries(a, mid)
        )
    end
    return LegMap(a.in_dim, b.out_dim, entry, entries)
end

compose_restrictions(r::TensorRestriction) = r

function compose_restrictions(
    first::TensorRestriction, second::TensorRestriction, rest::TensorRestriction...
)
    composed = TensorRestriction(map(_compose_maps, first.legs, second.legs))
    return isempty(rest) ? composed : foldl(compose_restrictions, rest; init=composed)
end

function _product_maps(a::LegMap, b::LegMap)
    src, dst = a.in_dim * b.in_dim, a.out_dim * b.out_dim
    if !isnothing(a.selection) && !isnothing(b.selection)
        function source_col(row)
            hi, lo = divrem(row - 1, a.out_dim)
            x, y = a.selection(lo + 1), b.selection(hi + 1)
            return iszero(x) || iszero(y) ? 0 : x + a.in_dim * (y - 1)
        end
        return selection_map(src, dst, source_col)
    end
    function entry(row, col)
        j, i = divrem(row - 1, a.out_dim)
        l, k = divrem(col - 1, a.in_dim)
        v = a[i + 1, k + 1]
        return iszero(v) ? v : v * b[j + 1, l + 1]
    end
    function entries(row)
        j, i = divrem(row - 1, a.out_dim)
        return (
            (x + a.in_dim * (y - 1), v * w) for (y, w) in row_entries(b, j + 1) for
            (x, v) in row_entries(a, i + 1)
        )
    end
    return LegMap(src, dst, entry, entries)
end

product_restriction() = identity_restriction(unit_dims(1))
product_restriction(r::TensorRestriction) = r

function product_restriction(
    a::TensorRestriction, b::TensorRestriction, rest::TensorRestriction...
)
    ab = TensorRestriction(map(_product_maps, a.legs, b.legs))
    return isempty(rest) ? ab : foldl(product_restriction, rest; init=ab)
end

function power_restriction(r::TensorRestriction, n::Integer)
    n >= 0 || throw(DomainError(n, "tensor power must be nonnegative"))
    n == 0 && return product_restriction()
    n == 1 && return r
    half = power_restriction(r, n ÷ 2)
    square = product_restriction(half, half)
    return iseven(n) ? square : product_restriction(square, r)
end

# All products use first-factor-fastest coordinates, including tensor powers.
function permute_factors(dimensions, order)
    sort(collect(order)) == collect(1:length(dimensions)) ||
        throw(ArgumentError("invalid permutation of tensor factors"))
    legs = ntuple(3) do leg
        dims = [big(d[leg]) for d in dimensions]
        strides = BigInt[]
        total = big(1)
        for d in dims
            push!(strides, total)
            total *= d
        end
        function source_col(row)
            index, col = row - 1, big(1)
            for i in order
                index, digit = divrem(index, dims[i])
                col += strides[i] * digit
            end
            return col
        end
        return selection_map(total, total, source_col)
    end
    return TensorRestriction(legs)
end

function mm_product(sides)
    ns = big.(collect(sides))
    all(>(0), ns) || throw(ArgumentError("matrix dimensions must be positive"))
    side = prod(ns; init=big(1))
    function source_col(row)
        y, x = divrem(row - 1, side)
        col, stride = big(1), big(1)
        for n in ns
            x, i = divrem(x, n)
            y, j = divrem(y, n)
            col += stride * (i + n * j)
            stride *= n^2
        end
        return col
    end
    leg = selection_map(side^2, side^2, source_col)
    return TensorRestriction(leg, leg, leg)
end

function mm_split(source_side::Integer, sides)
    ns = big.(collect(sides))
    all(>(0), ns) || throw(ArgumentError("matrix dimensions must be positive"))
    side = prod(ns; init=big(1))
    side <= source_side || throw(DimensionMismatch("matrix product does not fit in source"))
    function source_col(row)
        packed, x, y, stride = row - 1, big(0), big(0), big(1)
        for n in ns
            packed, digit = divrem(packed, n^2)
            j, i = divrem(digit, n)
            x += stride * i
            y += stride * j
            stride *= n
        end
        return 1 + x + big(source_side) * y
    end
    leg = selection_map(big(source_side)^2, side^2, source_col)
    return TensorRestriction(leg, leg, leg)
end

function unit_trim(k::Integer, t::Integer)
    1 <= t <= k || throw(DimensionMismatch("unit tensor cannot supply requested dimension"))
    leg = selection_map(k, t, identity)
    return TensorRestriction(leg, leg, leg)
end

"""Classical rank decomposition of a catalyst matrix tensor, with (i,k,j) digits."""
function unit_to_mm(n::Integer)
    n > 0 || throw(DomainError(n))
    b = big(n)
    function leg_map(leg)
        function entries(row)
            y, x = divrem(row - 1, b)
            if leg == 1
                return ((row + b^2 * j, 1) for j in 0:(b - 1))
            elseif leg == 2
                return ((1 + i + b * (row - 1), 1) for i in 0:(b - 1))
            end
            return ((1 + x + b * k + b^2 * y, 1) for k in 0:(b - 1))
        end
        function entry(row, col)
            kj, i = divrem(col - 1, b)
            j, k = divrem(kj, b)
            expected = if leg == 1
                i + b * k
            elseif leg == 2
                k + b * j
            else
                i + b * j
            end
            return Int(row == 1 + expected)
        end
        return LegMap(b^3, b^2, entry, entries)
    end
    return TensorRestriction(ntuple(leg_map, 3))
end

"""Discard a factor known to have coefficient one at coordinate (1,1,1)."""
function discard_restriction(dims)
    return TensorRestriction(ntuple(i -> selection_map(dims[i], 1, _ -> 1), 3))
end
