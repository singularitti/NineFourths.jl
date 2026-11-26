"""
One leg of a tensor restriction. Columns label source variables and rows
label target variables. The constructor takes positive `Integer` dimensions
`in_dim` and `out_dim` and stores them as `BigInt`.

Each callback can be a function or another callable object. It receives
one-based `BigInt` indices. `entry(row, col)` returns an exact coefficient,
for example an `Int`, `Rational{BigInt}`, or `PhaseSum`.
`support(row)` yields an iterable of `(column, weight)` pairs with integer
columns and exact weights. Their contributions add up to the row.
`selection(row)` returns the `Integer` index of the only nonzero column when
its coefficient is one, or zero for an all-zero row. Either optional callback
can be `nothing`.
"""
struct LegMap
    in_dim::BigInt
    out_dim::BigInt
    # Keep the map type fixed as composition and products capture other maps.
    entry
    support
    selection
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

"""
Iterate the `(column, weight)` contributions to a one-based `Integer` row.
`m` supplies `in_dim`, `out_dim`, `entry`, and `support` as in a `LegMap`.
When `support` is `nothing`, scan the columns and yield the nonzero entries.
"""
function row_entries(m, row::Integer)
    1 <= row <= m.out_dim || throw(BoundsError(m, row))
    row_index = big(row)
    isnothing(m.support) || return m.support(row_index)
    return (
        (col, weight) for col in 1:m.in_dim for
        weight in (m.entry(row_index, col),) if !iszero(weight)
    )
end

"""
Construct a `LegMap` from positive `Integer` dimensions. The callable
`source_column` maps a `BigInt` row to a one-based `Integer` column, or to zero
for an all-zero row. A selected column has coefficient `1::Int`.
"""
function selection_map(in_dim, out_dim, source_column)
    # Given a BigInt row, return an empty tuple or one (column, 1) contribution.
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

# Three LegMaps in tensor order, one each for the left input, right input, and output.
struct TensorRestriction
    legs::NTuple{3,LegMap}
end

TensorRestriction(x::LegMap, y::LegMap, z::LegMap) = TensorRestriction((x, y, z))

# A TensorRestriction's legs form an NTuple{3,LegMap} of maps with BigInt input dimensions.
source_dims(restriction) = map(m -> m.in_dim, restriction.legs)
# Read the BigInt output dimensions from the same three LegMap objects.
target_dims(restriction) = map(m -> m.out_dim, restriction.legs)

# The tensor has three equal BigInt leg dimensions. For a matrix tensor,
# the dimension of each leg is the square of the integer matrix side `k`.
unit_dims(k::Integer) = (big(k), big(k), big(k))
mm_dims(k::Integer) = unit_dims(big(k)^2)

# `dims` supports indexing over the three positive integer leg dimensions,
# for example an `NTuple{3,BigInt}`.
function identity_restriction(dims)
    return TensorRestriction(ntuple(i -> selection_map(dims[i], dims[i], identity), 3))
end

"""
Apply `a` first and `b` second, matching the intervening leg dimensions.
The operands are usually `LegMap`s. They expose `in_dim`, `out_dim`, and
`selection`, and a general composition uses `row_entries` and indexes `a`.
"""
function _compose_maps(a, b)
    a.out_dim == b.in_dim ||
        throw(DimensionMismatch("tensor restriction endpoints do not match"))
    if !isnothing(a.selection) && !isnothing(b.selection)
        # Map a BigInt target row through two selectors returning integer columns.
        function source_col(row)
            mid = b.selection(row)
            return iszero(mid) ? 0 : a.selection(big(mid))
        end
        return selection_map(a.in_dim, b.out_dim, source_col)
    end
    # For two BigInt indices, accumulate products of exact coefficients.
    function entry(row, col)
        value = 0
        for (mid, weight) in row_entries(b, row)
            left = a[mid, col]
            iszero(left) || (value += weight * left)
        end
        return value
    end
    # A BigInt row yields (integer column, exact weight) contributions.
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

# Compose the three corresponding legs of each TensorRestriction left to right.
compose_restrictions(r::TensorRestriction) = r

function compose_restrictions(
    first::TensorRestriction, second::TensorRestriction, rest::TensorRestriction...
)
    composed = TensorRestriction(map(_compose_maps, first.legs, second.legs))
    return isempty(rest) ? composed : foldl(compose_restrictions, rest; init=composed)
end

"""
Tensor two leg maps with the coordinates of the first factor varying fastest.
The operands are usually `LegMap`s. They expose `in_dim`, `out_dim`, and
`selection`, and a general product uses `row_entries` and indexed coefficients.
"""
function _product_maps(a, b)
    src, dst = a.in_dim * b.in_dim, a.out_dim * b.out_dim
    if !isnothing(a.selection) && !isnothing(b.selection)
        # Split a BigInt product row into factor rows and pack the integer source columns.
        function source_col(row)
            hi, lo = divrem(row - 1, a.out_dim)
            x, y = a.selection(lo + 1), b.selection(hi + 1)
            return iszero(x) || iszero(y) ? 0 : x + a.in_dim * (y - 1)
        end
        return selection_map(src, dst, source_col)
    end
    # BigInt row and column indices select one exact coefficient from each factor.
    function entry(row, col)
        j, i = divrem(row - 1, a.out_dim)
        l, k = divrem(col - 1, a.in_dim)
        v = a[i + 1, k + 1]
        return iszero(v) ? v : v * b[j + 1, l + 1]
    end
    # For a BigInt product row, yield (packed column, exact weight) pairs.
    function entries(row)
        j, i = divrem(row - 1, a.out_dim)
        return (
            (x + a.in_dim * (y - 1), v * w) for (y, w) in row_entries(b, j + 1) for
            (x, v) in row_entries(a, i + 1)
        )
    end
    return LegMap(src, dst, entry, entries)
end

# Take the tensor product leg by leg. Zero factors give the dimension-one identity.
product_restriction() = identity_restriction(unit_dims(1))
product_restriction(r::TensorRestriction) = r

function product_restriction(
    a::TensorRestriction, b::TensorRestriction, rest::TensorRestriction...
)
    ab = TensorRestriction(map(_product_maps, a.legs, b.legs))
    return isempty(rest) ? ab : foldl(product_restriction, rest; init=ab)
end

# Use `n` copies of the restriction as tensor factors, with `n` nonnegative.
function power_restriction(r::TensorRestriction, n::Integer)
    n >= 0 || throw(DomainError(n, "tensor power must be nonnegative"))
    n == 0 && return product_restriction()
    n == 1 && return r
    half = power_restriction(r, n ÷ 2)
    square = product_restriction(half, half)
    return iseven(n) ? square : product_restriction(square, r)
end

"""
Permute factors in first-factor-fastest coordinates. `dimensions` is an iterable
of positive integer leg-dimension triples, such as a `Vector{NTuple{3,BigInt}}`.
`order` is an iterable of one-based integer factor indices, such as `(3, 1, 2)`.
"""
function permute_factors(dimensions, order)
    dimensions = collect(dimensions)
    order = collect(order)
    length(order) == length(dimensions) && isperm(order) ||
        throw(ArgumentError("invalid permutation of tensor factors"))
    legs = ntuple(3) do leg
        dims = [big(d[leg]) for d in dimensions]
        strides = BigInt[]
        total = big(1)
        for d in dims
            push!(strides, total)
            total *= d
        end
        # Decode a BigInt row in the new factor order and return its original BigInt column.
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

# `sides` is an iterable of positive Integer matrix sides, such as `(2, 3)`.
# The target matrix side is their product.
function mm_product(sides)
    ns = big.(collect(sides))
    all(>(0), ns) || throw(ArgumentError("matrix dimensions must be positive"))
    side = prod(ns; init=big(1))
    # Map a BigInt matrix entry index to a BigInt column packed by factor.
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

# `sides` is an iterable of positive Integer factor sides. Their product gives
# the side of the leading square cut from the source matrix.
function mm_split(source_side::Integer, sides)
    ns = big.(collect(sides))
    all(>(0), ns) || throw(ArgumentError("matrix dimensions must be positive"))
    side = prod(ns; init=big(1))
    side <= source_side || throw(DimensionMismatch("matrix product does not fit in source"))
    # Decode a BigInt row packed by factor into a BigInt source matrix entry index.
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

# Keep the first `t` coordinates on each leg of a unit tensor of dimension `k`.
function unit_trim(k::Integer, t::Integer)
    1 <= t <= k || throw(DimensionMismatch("unit tensor cannot supply requested dimension"))
    leg = selection_map(k, t, identity)
    return TensorRestriction(leg, leg, leg)
end

"""
Construct the classical rank decomposition of a catalyst matrix tensor with
positive `Integer` side `n`. Each leg has `n^3` source columns encoding `(i,k,j)`
and `n^2` target rows encoding its pair of matrix indices.
"""
function unit_to_mm(n::Integer)
    n > 0 || throw(DomainError(n))
    b = big(n)
    # `leg` is an Int from 1 through 3, for X, Y, and Z respectively.
    function leg_map(leg)
        # For a BigInt row, yield pairs of a BigInt source column and coefficient 1::Int.
        function entries(row)
            y, x = divrem(row - 1, b)
            if leg == 1
                return ((row + b^2 * j, 1) for j in 0:(b - 1))
            elseif leg == 2
                return ((1 + i + b * (row - 1), 1) for i in 0:(b - 1))
            end
            return ((1 + x + b * k + b^2 * y, 1) for k in 0:(b - 1))
        end
        # BigInt row and column indices determine a coefficient of 0::Int or 1::Int.
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

"""
Discard a factor known to have coefficient one at coordinate `(1,1,1)`.
`dims` supplies its three positive integer leg dimensions by indexing,
for example as an `NTuple{3,BigInt}`.
"""
function discard_restriction(dims)
    return TensorRestriction(ntuple(i -> selection_map(dims[i], 1, _ -> 1), 3))
end
