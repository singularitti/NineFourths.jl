"""
    LegMap(in_dim, out_dim, entry, support=nothing, selection=nothing)

Represent a single leg of a tensor restriction from `in_dim` source variables
to `out_dim` target variables.

Each column gives the substitution of one source variable as a linear
combination of target variables. Dimensions are stored as `BigInt` and must
be positive, or the constructor throws `ArgumentError`.

Each callback receives one-based `BigInt` indices.

  - `entry(row, col)` returns the exact coefficient at that target row and source
    column, for example an `Int`, `Rational{BigInt}`, or `PhaseSum`.
  - `support(row)` yields `(column, weight)` contributions whose sum at each
    column equals `entry(row, col)`. A source column may occur more than once.
  - `selection(row)` returns the source column if it is the only nonzero entry
    and has weight one. It returns zero for an all-zero row. Supply this callback
    only if all rows satisfy this contract.

`support` and `selection` may be `nothing`. See also `row_entries` and
`selection_map`.
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

"""
    size(m::LegMap)::Tuple{BigInt,BigInt}

Return the number of target rows and source columns, in that order.
"""
Base.size(m::LegMap) = (m.out_dim, m.in_dim)

"""
    size(m::LegMap, axis::Integer)::BigInt

Return the number of target rows for axis `1` or source columns for axis `2`.
An axis outside this range raises `BoundsError`.
"""
Base.size(m::LegMap, axis::Integer) = size(m)[axis]

"""
    getindex(m::LegMap, row::Integer, col::Integer)

Return the exact coefficient of target variable `row` in the substitution for
source variable `col`.

The indices are one-based and out-of-range indices raise `BoundsError`.
"""
function Base.getindex(m::LegMap, row::Integer, col::Integer)
    1 <= row <= m.out_dim && 1 <= col <= m.in_dim || throw(BoundsError(m, (row, col)))
    return m.entry(big(row), big(col))
end

"""
    row_entries(m, row::Integer)

Return an iterable of `(source_column, weight)` contributions to target `row`.

`m` supplies `in_dim`, `out_dim`, `entry`, and `support` as in a `LegMap`.
If `support` is `nothing`, scan the columns and yield the nonzero entries.
Otherwise, use the callback as supplied, which may yield several contributions
to the same column. A row outside the one-based target range raises `BoundsError`.
"""
function row_entries(m, row::Integer)
    1 <= row <= m.out_dim || throw(BoundsError(m, row))
    row_index = big(row)
    isnothing(m.support) || return m.support(row_index)
    return ((col, weight) for col in 1:m.in_dim for
            weight in (m.entry(row_index, col),) if !iszero(weight))
end

"""
    selection_map(in_dim, out_dim, source_column)::LegMap

Construct a leg map that selects at most one source column per target row.

`source_column(row)` maps a one-based `BigInt` target row to a one-based
source column, or returns zero for an all-zero row. A selected column has
coefficient `1::Int`. Both dimensions must be positive.
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

"""
    TensorRestriction(legs::NTuple{3,LegMap})
    TensorRestriction(x::LegMap, y::LegMap, z::LegMap)

Represent the three variable substitutions of a restriction in tensor-leg order.

For matrix multiplication, these are the left input, right input, and output
legs. Each leg map has source columns and target rows.
"""
struct TensorRestriction
    legs::NTuple{3,LegMap}
end

TensorRestriction(x::LegMap, y::LegMap, z::LegMap) = TensorRestriction((x, y, z))

"""
    source_dims(restriction::TensorRestriction)::NTuple{3,BigInt}

Return the three source leg dimensions in tensor order.
"""
source_dims(restriction) = map(m -> m.in_dim, restriction.legs)

"""
    target_dims(restriction::TensorRestriction)::NTuple{3,BigInt}

Return the three target leg dimensions in tensor order.
"""
target_dims(restriction) = map(m -> m.out_dim, restriction.legs)

"""
    unit_dims(k::Integer)::NTuple{3,BigInt}

Return the leg dimensions of the unit tensor of size `k`.
"""
unit_dims(k::Integer) = (big(k), big(k), big(k))

"""
    mm_dims(k::Integer)::NTuple{3,BigInt}

Return the leg dimensions of the square matrix multiplication tensor of side `k`.

Each leg has `k^2` coordinates for one matrix's entries.
"""
mm_dims(k::Integer) = unit_dims(big(k)^2)

"""
    identity_restriction(dims)::TensorRestriction

Return the identity substitution on each leg of the given dimensions.

`dims` supports indexing over the three positive leg dimensions, for example
as an `NTuple{3,BigInt}`.
"""
function identity_restriction(dims)
    return TensorRestriction(ntuple(i -> selection_map(dims[i], dims[i], identity), 3))
end

"""
    _compose_maps(a, b)::LegMap

Compose leg maps by applying `a` first and `b` second.

The operands are usually `LegMap`s. They expose `in_dim`, `out_dim`, and
`selection`. A general composition uses `row_entries` and indexes `a`.
The returned row contributions multiply and sum through the intermediate leg,
which means repeated source columns are possible. Mismatched intermediate legs
raise `DimensionMismatch`.
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
        return ((col, v * w) for (mid, w) in row_entries(b, row) for
                (col, v) in row_entries(a, mid))
    end
    return LegMap(a.in_dim, b.out_dim, entry, entries)
end

"""
    compose_restrictions(r::TensorRestriction)
    compose_restrictions(first::TensorRestriction, second::TensorRestriction, rest...)

Apply tensor restrictions from left to right, composing their corresponding legs.

Each restriction's target dimensions must match the next one's source
dimensions. A single restriction passes through unchanged.
"""
compose_restrictions(r::TensorRestriction) = r

function compose_restrictions(
    first::TensorRestriction, second::TensorRestriction, rest::TensorRestriction...
)
    composed = TensorRestriction(map(_compose_maps, first.legs, second.legs))
    return isempty(rest) ? composed : foldl(compose_restrictions, rest; init=composed)
end

"""
    _product_maps(a, b)::LegMap

Tensor two leg maps with the coordinates of `a` varying fastest.

The operands are usually `LegMap`s. They expose `in_dim`, `out_dim`, and
`selection`, and a general product uses `row_entries` and indexed coefficients.
A coordinate pair `(i, j)` packs to `i + d * (j - 1)`, where `d` is the first
factor's source or target dimension as appropriate. Each row contribution
multiplies weights from one source coordinate in each factor.
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
        return ((x + a.in_dim * (y - 1), v * w) for (y, w) in row_entries(b, j + 1) for
                (x, v) in row_entries(a, i + 1))
    end
    return LegMap(src, dst, entry, entries)
end

"""
    product_restriction()
    product_restriction(r::TensorRestriction)
    product_restriction(a::TensorRestriction, b::TensorRestriction, rest...)

Take the tensor product of restrictions leg by leg, with the first factor varying fastest.

The empty product is the identity on a tensor with all three leg dimensions
equal to one. A single restriction passes through unchanged.
"""
product_restriction() = identity_restriction(unit_dims(1))
product_restriction(r::TensorRestriction) = r

function product_restriction(
    a::TensorRestriction, b::TensorRestriction, rest::TensorRestriction...
)
    ab = TensorRestriction(map(_product_maps, a.legs, b.legs))
    return isempty(rest) ? ab : foldl(product_restriction, rest; init=ab)
end

"""
    power_restriction(r::TensorRestriction, n::Integer)::TensorRestriction

Take the tensor product of `n` copies of `r`, with the first copy varying fastest.

A zero power gives the dimension-one identity. A negative power raises `DomainError`.
"""
function power_restriction(r::TensorRestriction, n::Integer)
    n >= 0 || throw(DomainError(n, "tensor power must be nonnegative"))
    n == 0 && return product_restriction()
    n == 1 && return r
    half = power_restriction(r, n ÷ 2)
    square = product_restriction(half, half)
    return iseven(n) ? square : product_restriction(square, r)
end

"""
    permute_factors(dimensions, order)::TensorRestriction

Reindex a tensor product so its factors occur in the given order.

`dimensions` lists the positive leg-dimension triples in source order. The
`order` iterable lists the one-based source factor indices in target order.
For example, `(3, 1, 2)` moves the third source factor first. Both layouts
use first-factor-fastest coordinates. An invalid permutation raises `ArgumentError`.
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

"""
    mm_product(sides)::TensorRestriction

Identify a tensor product of square matrix multiplication tensors with one
square matrix multiplication tensor whose side is `prod(sides)`.

`sides` lists the positive integer factor sides in source order. The source
coordinate packs each factor's row and column together, with the first factor
varying fastest. The target stores the assembled row and column in Julia
column-major order. An empty list gives the side-one identity and a nonpositive
side raises `ArgumentError`. See also `mm_split`.
"""
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

"""
    mm_split(source_side::Integer, sides)::TensorRestriction

Crop a square matrix multiplication tensor and split it into the specified factors.

`sides` lists positive integer sides in target order. Keep the first
`prod(sides)` indices in each matrix dimension, then apply the inverse of
`mm_product(sides)` to those coordinates. If the product exceeds `source_side`,
throw `DimensionMismatch`. A nonpositive factor side raises `ArgumentError`.
"""
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

"""
    unit_trim(k::Integer, t::Integer)::TensorRestriction

Keep the first `t` coordinates on each leg of the unit tensor of size `k`.

Throw `DimensionMismatch` unless `1 <= t <= k`.
"""
function unit_trim(k::Integer, t::Integer)
    1 <= t <= k || throw(DimensionMismatch("unit tensor cannot supply requested dimension"))
    leg = selection_map(k, t, identity)
    return TensorRestriction(leg, leg, leg)
end

"""
    unit_to_mm(n::Integer)::TensorRestriction

Construct the classical rank decomposition of a catalyst matrix tensor of side `n`.

Each leg has `n^3` source columns encoding `(i,k,j)` with `i` varying fastest.
The `n^2` target rows encode `(i,k)`, `(k,j)`, or `(i,j)` on the three legs in
column-major order. All contributions have weight one. A nonpositive side
raises `DomainError`.
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
    discard_restriction(dims)::TensorRestriction

Restrict a tensor factor to the scalar given by its coefficient at `(1,1,1)`.

The compiler uses this map when that coefficient is one. `dims` supplies the
three positive leg dimensions by indexing, for example as an `NTuple{3,BigInt}`.
"""
function discard_restriction(dims)
    return TensorRestriction(ntuple(i -> selection_map(dims[i], 1, _ -> 1), 3))
end
