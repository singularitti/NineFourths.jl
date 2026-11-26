"""
    _WitnessEvent(index, copies, counts, multiplicity, child_side, side)

Store the copy counts and matrix sides for one step in the reversed derivation.

`index` identifies the derivation node and `copies` counts the seed factors
processed there. `counts` holds the three sector counts for a tripling step
or the two midpoint counts followed by zero. `multiplicity` counts the
sector words with those counts. For other steps, all copies use the first
count and the multiplicity is one. `child_side` and `side` give the matrix
side before and after accounting for this step's gain and auxiliary factors.
"""
struct _WitnessEvent
    index::Int
    copies::BigInt
    counts::NTuple{3,BigInt}
    multiplicity::BigInt
    child_side::BigInt
    side::BigInt
end

"""
    _witness_events(nodes, N) -> (; events, baseline, side)

Allocate `N` copies among the dependencies of the final node in Lemma 6.7.

Supply a one-based indexed sequence of `DerivationNode`s in dependency
order and a positive integer `N`. The returned `events` list contains
`_WitnessEvent`s in reverse derivation order. The `baseline` list pairs
node indices with positive `BigInt` copy counts. `side` is the resulting
`BigInt` matrix side before the final power.
"""
function _witness_events(nodes, N)
    N >= 1 || throw(ArgumentError("the witness power must be positive"))
    isempty(nodes) && throw(ArgumentError("a witness needs a derivation"))
    demand = fill(big(0), length(nodes))
    demand[end] = N
    choices = Tuple{Int,BigInt,NTuple{3,BigInt},BigInt}[]
    for index in reverse(eachindex(nodes))
        k = demand[index]
        node = nodes[index]
        (iszero(k) || node.kind === :baseline) && continue
        parents = node.predecessors
        counts = (k, big(0), big(0))
        M = big(1)
        if node.kind === :midpoint
            α, β = nodes[parents[1]].value, nodes[parents[2]].value
            # Consecutive binomial terms straddle their maximum at this mode.
            j = min(k, floor(BigInt, (k + 1) * α / (α + β)))
            counts = (j, k - j, big(0))
            M = binomial(k, j)
            demand[parents[1]] += j
            demand[parents[2]] += k - j
        elseif node.kind === :tripling
            q, remainder = divrem(k, 3)
            counts = ntuple(i -> q + (i <= remainder), 3)
            M = binomial(k, counts[1]) * binomial(k - counts[1], counts[2])
            demand[only(parents)] += k
        elseif node.kind === :restriction || node.kind === :symmetry
            demand[only(parents)] += k
        else
            throw(ArgumentError("unknown derivation step"))
        end
        push!(choices, (index, k, counts, M))
    end
    baseline = [
        (i, demand[i]) for
        i in eachindex(nodes) if nodes[i].kind === :baseline && demand[i] > 0
    ]
    r = prod((max(nodes[i].a, nodes[i].b)^(2k) for (i, k) in baseline); init=big(1))
    events = _WitnessEvent[]
    for (index, k, counts, M) in Iterators.reverse(choices)
        child_side = r
        kind = nodes[index].kind
        if kind === :midpoint
            r = max(big(1), div(M^2 * r, big(4)^k))
        elseif kind === :tripling
            r *= M^2
        end
        push!(events, _WitnessEvent(index, k, counts, M, child_side, r))
    end
    reverse!(events)
    return (; events, baseline, side=r)
end

"""
    witness_side(nodes, N)

Calculate the matrix side in Lemma 6.2 without instantiating restriction maps.
This evaluates the binomial and multinomial multiplicities and the final power.
Supply a one-based indexed sequence of derivation entries in dependency order
and a positive integer power `N`. The entries are `DerivationNode`s and the
result is a `BigInt` matrix side after raising the planned side to `N^2`.
"""
witness_side(nodes, N::Integer) = _witness_events(nodes, N).side^(big(N)^2)

"""
    _witness_copies(S, N)::BigInt

Count the seed copies reserved for a derivation with step bound `S` and power `N`.

Preparation costs `16S*N^2` copies. Each of the `N` reuse rounds takes `N^2`
copies plus a budget of `18S*N`. Per step, the budget allows `6N` copies for
the unit factor and `6N` for each interpolation phase. The interpolation
allowance follows from `6N*9^N + 2 ≤ 64^N`.
"""
_witness_copies(S, N) = big(N)^3 + 34big(S) * big(N)^2

"""
    _WitnessTag

Identify a tensor factor by its symbolic role and integer index.
"""
const _WitnessTag = Tuple{Symbol,Int}

"""
    _WitnessDims

Store the three leg dimensions of a tensor factor as exact integers.
"""
const _WitnessDims = NTuple{3,BigInt}

"""
    _WitnessWire

Pair a tensor factor's `_WitnessTag` with its `_WitnessDims`.
"""
const _WitnessWire = Pair{_WitnessTag,_WitnessDims}

"""
    _wire(tag, dims)::_WitnessWire

Pair a factor tag with its three leg dimensions after converting them to `BigInt`.
"""
_wire(tag, dims) = _WitnessWire(tag, map(big, dims))

"""
    _power_dims(dims, n)::_WitnessDims

Raise each leg dimension in the tuple `dims` to the nonnegative integer power `n`.
"""
_power_dims(dims, n) = map(dimension -> big(dimension)^n, dims)

"""
    _wire_dims(wires)::_WitnessDims

Multiply the leg dimensions of a sequence of factors.

Return three unit dimensions for the empty product.
"""
function _wire_dims(wires)
    return ntuple(leg -> prod((wire.second[leg] for wire in wires); init=big(1)), 3)
end

"""
    _WitnessLayout(wires, stages)

Track the ordered tensor factors and restriction stages of a witness.

When a stage replaces selected factors, its restriction is tensored with
the identity on every remaining factor.
"""
struct _WitnessLayout
    wires::Vector{_WitnessWire}
    stages::Vector{TensorRestriction}
end

"""
    _WitnessLayout(wires)

Start with the given factors and an empty restriction-stage list.
"""
_WitnessLayout(wires) = _WitnessLayout(wires, TensorRestriction[])

"""
    _combine_restrictions(combine, maps, start=firstindex(maps), stop=lastindex(maps))

Combine a nonempty range of restrictions in their original order.

The callable `combine(a, b)` combines two `TensorRestriction`s. Splitting
the range into halves keeps the resulting restriction and its row iterator
logarithmic in depth.
"""
function _combine_restrictions(combine, maps, start=firstindex(maps), stop=lastindex(maps))
    start == stop && return maps[start]
    middle = start + (stop - start) ÷ 2
    return combine(
        _combine_restrictions(combine, maps, start, middle),
        _combine_restrictions(combine, maps, middle + 1, stop),
    )
end

"""
    _wire_position(layout, tag)::Int

Find the position of the factor named by `tag` in `layout`.
"""
function _wire_position(layout, tag)
    index = findfirst(wire -> wire.first == tag, layout.wires)
    isnothing(index) && error("missing tensor factor $(tag)")
    return index
end

"""
    _replace_wires!(layout, tags, outputs, restriction)

Apply `restriction` to the factors named by `tags` and record the stage.

Place the resulting `outputs` first and retain the other factors in their
relative order. The restriction's source and target dimensions must match
the products of the selected and replacement leg dimensions, respectively.
"""
function _replace_wires!(layout, tags, outputs, restriction)
    selected = [_wire_position(layout, tag) for tag in tags]
    untouched = setdiff(eachindex(layout.wires), selected)
    order = vcat(selected, untouched)
    if !issorted(order)
        push!(layout.stages, permute_factors([wire.second for wire in layout.wires], order))
    end
    rest = layout.wires[untouched]
    source_dims(restriction) == _wire_dims(layout.wires[selected]) ||
        error("incorrect source layout for restriction")
    target_dims(restriction) == _wire_dims(outputs) ||
        error("incorrect target layout for restriction")
    push!(
        layout.stages,
        product_restriction(restriction, identity_restriction(_wire_dims(rest))),
    )
    empty!(layout.wires)
    append!(layout.wires, outputs)
    append!(layout.wires, rest)
    return nothing
end

"""
    _order_wires!(layout, tags)

Reorder all factors in `layout` by `tags` and record any required permutation.
"""
function _order_wires!(layout, tags)
    order = [_wire_position(layout, tag) for tag in tags]
    length(order) == length(layout.wires) || error("incomplete tensor layout")
    if !issorted(order)
        push!(layout.stages, permute_factors([wire.second for wire in layout.wires], order))
        layout.wires[:] = layout.wires[order]
    end
    return nothing
end

"""
    _drop_wires!(layout, tags)

Discard the factors named by `tags` by restricting each to its first coordinate.
"""
function _drop_wires!(layout, tags)
    isempty(tags) && return nothing
    wires = [layout.wires[_wire_position(layout, tag)] for tag in tags]
    _replace_wires!(layout, tags, _WitnessWire[], discard_restriction(_wire_dims(wires)))
    return nothing
end

"""
    _coordinates(index, dimensions)::Vector{BigInt}

Unpack a one-based index using the given dimensions as radices.

The returned coordinates are one-based and the first varies fastest.
See also [`_coordinate`](@ref).
"""
function _coordinates(index, dimensions)
    coordinates = BigInt[]
    quotient = big(index) - 1
    for dimension in dimensions
        quotient, digit = divrem(quotient, dimension)
        push!(coordinates, digit + 1)
    end
    return coordinates
end

"""
    _coordinate(coordinates, dimensions)::BigInt

Pack one-based coordinates into a one-based index with the first coordinate fastest.

See also [`_coordinates`](@ref).
"""
function _coordinate(coordinates, dimensions)
    index, stride = big(1), big(1)
    for (digit, dimension) in zip(coordinates, dimensions)
        index += (digit - 1) * stride
        stride *= dimension
    end
    return index
end

"""
    _seed_restrict(a, b, c, d)::TensorRestriction

Restrict the seed at lengths `(a, b)` to the seed at lengths `(c, d)`.

Each leg selects source coordinates in the smaller range of all six
orientations. Assume positive lengths with `c ≤ a` and `d ≤ b`.
"""
function _seed_restrict(a, b, c, d)
    src, dst = (a, b, a + b - 1), (c, d, c + d - 1)
    return TensorRestriction(ntuple(3) do leg
        sd = map(p -> src[p[leg]], LEG_PERMUTATIONS)
        td = map(p -> dst[p[leg]], LEG_PERMUTATIONS)
        return selection_map(
            prod(sd), prod(td), row -> _coordinate(_coordinates(row, td), sd)
        )
    end...,)
end

"""
    _seed_symmetry(a, b)::TensorRestriction

Swap the two positive polynomial lengths by permuting the six seed orientations.
"""
function _seed_symmetry(a, b)
    src = (a, b, a + b - 1)
    order = map(LEG_PERMUTATIONS) do p
        swapped = map(i -> i == 3 ? i : 3 - i, p)
        return findfirst(==(swapped), LEG_PERMUTATIONS)
    end
    inverse = invperm(collect(order))
    return TensorRestriction(ntuple(3) do leg
        sd = map(p -> src[p[leg]], LEG_PERMUTATIONS)
        td = map(i -> sd[i], order)
        return selection_map(
            prod(sd), prod(td), row -> _coordinate(_coordinates(row, td)[inverse], sd)
        )
    end...,)
end

"""
    _replica_order(factors, N; inverse=false)::TensorRestriction

Reorder a product of tensor powers into a tensor power of the product.

`factors` supplies one dimension tuple per factor and `N` gives the copy
count. Each leg uses its own factor dimensions as radices. Set
`inverse=true` to reverse the permutation.
"""
function _replica_order(factors, N; inverse=false)
    dimensions = ntuple(leg -> prod((dims[leg] for dims in factors); init=big(1)), 3)
    powered = _power_dims(dimensions, N)
    (N == 1 || length(factors) <= 1) && return identity_restriction(powered)
    return TensorRestriction(ntuple(3) do leg
        radices = [dims[leg] for dims in factors]
        wire_radices = [d^N for d in radices]
        # Map a one-based factor-major index to one with the factors grouped by copy.
        function replica_major(index)
            remaining = _coordinates(index, wire_radices) .- 1
            result, stride = big(1), big(1)
            for _ in 1:N, i in eachindex(radices)
                remaining[i], digit = divrem(remaining[i], radices[i])
                result += digit * stride
                stride *= radices[i]
            end
            return result
        end
        # Map a one-based copy-major index to one with the copies grouped by factor.
        function wire_major(index)
            remaining = big(index) - 1
            coordinates = ones(BigInt, length(radices))
            strides = ones(BigInt, length(radices))
            for _ in 1:N, i in eachindex(radices)
                remaining, digit = divrem(remaining, radices[i])
                coordinates[i] += digit * strides[i]
                strides[i] *= radices[i]
            end
            return _coordinate(coordinates, wire_radices)
        end
        return selection_map(
            powered[leg], powered[leg], inverse ? replica_major : wire_major
        )
    end...,)
end

"""
    _matrix_power(side, N; inverse=false)::TensorRestriction

Pack `N` side-`side` matrix multiplication factors into one side-`side^N` factor.

Each leg changes from one pair of indices per copy to a single pair of
packed indices. Set `inverse=true` to unpack the factor.
"""
function _matrix_power(side, N; inverse=false)
    side, N = big(side), big(N)
    packed_side = side^N
    dimension = packed_side^2
    radix = side^2
    (side == 1 || N == 1) && return identity_restriction((dimension, dimension, dimension))
    # Pack a one-based index by collecting the two components separately across copies.
    function packed(index)
        remaining = big(index) - 1
        first, second, stride = big(0), big(0), big(1)
        for _ in 1:N
            remaining, low = divrem(remaining, side)
            remaining, high = divrem(remaining, side)
            first += low * stride
            second += high * stride
            stride *= side
        end
        return first + second * stride + 1
    end
    # Interleave the two packed components into one coordinate pair per copy.
    function interleaved(index)
        high, low = divrem(big(index) - 1, packed_side)
        result, stride = big(1), big(1)
        for _ in 1:N
            low, first = divrem(low, side)
            high, second = divrem(high, side)
            result += (first + side * second) * stride
            stride *= radix
        end
        return result
    end
    leg = selection_map(dimension, dimension, inverse ? packed : interleaved)
    return TensorRestriction(leg, leg, leg)
end

"""
    _binary_units(dimension)::Int

Count the binary unit factors needed to supply a unit tensor of size `dimension`.
"""
_binary_units(dimension) = dimension == 1 ? 0 : ndigits(dimension - 1; base=2)

"""
    _seed_to_unit(a, b, count, dimension)::TensorRestriction

Restrict `count` copies of the seed at `(a, b)` to a unit tensor of size `dimension`.

Extract one binary unit per seed and trim their product to the requested size.
For size one, restrict the whole product to its first coordinate.
"""
function _seed_to_unit(a, b, count, dimension)
    dimension == 1 && return discard_restriction(_power_dims(seed_dims(a, b), count))
    return compose_restrictions(
        power_restriction(seed_unit(a, b), count), unit_trim(big(2)^count, dimension)
    )
end

"""
    _draw_unit!(layout, budget, remaining::BigInt, dimension, tag, a, b)::BigInt

Spend seed copies from `budget` to supply a unit tensor named `tag`.

Use the minimum number of copies of the seed at lengths `(a, b)` needed for
the positive unit size `dimension`. Record the restriction in `layout` and
return the updated seed count after subtracting the cost from `remaining`.
"""
function _draw_unit!(layout, budget, remaining, dimension, tag, a, b)
    cost = _binary_units(dimension)
    after = remaining - cost
    after >= 0 || error("interpolation exceeds the unit allowance")
    dst = _power_dims(seed_dims(a, b), after)
    restriction = product_restriction(
        _seed_to_unit(a, b, cost, dimension), identity_restriction(dst)
    )
    _replace_wires!(
        layout,
        [budget],
        [_wire(tag, unit_dims(dimension)), _wire(budget, dst)],
        restriction,
    )
    return after
end

"""
    _interpolated_phase(transition, phase, N; admissible_order=nothing)

Extract the constant term of a sector phase after taking its `N`th tensor power.

`phase` selects stage 1 or 2 of `transition`. All copies of the phase use
the same evaluation point. If the powered stage has degree bound `D`,
the default evaluates at the integers from 1 to `D + 1` with signed
binomial weights.

Supply `admissible_order(n)::Bool` to select invertible Fourier orders.
The interpolated phase then averages over all roots of unity of the
selected order, which exceeds `D`. Return the sample count `points` and
the resulting `TensorRestriction`.
"""
function _interpolated_phase(transition, phase, N; admissible_order=nothing)
    degree = N * transition_degree(transition, phase)
    points =
        iszero(degree) ? big(1) : _sample_order(admissible_order, degree + 1, degree + 2)
    use_roots = !isnothing(admissible_order)
    # Build the stage restriction at the given integer or root-of-unity sample.
    evaluate = if use_roots
        M = transition.sector_type.multiplicity
        separation = _sample_order(admissible_order, 2M, 2M - 1)
        parameter -> transition_restriction(
            transition, phase, parameter; admissible_order=separation
        )
    else
        parameter -> transition_restriction(transition, phase, parameter)
    end
    sample = evaluate(big(1))
    src, dst = _power_dims(source_dims(sample), N), _power_dims(target_dims(sample), N)
    if points == 1
        return (; points, restriction=power_restriction(sample, N))
    end
    # Convert the one-based sample index to its evaluation point and build the map.
    sample_at(point) = evaluate(use_roots ? root_of_unity(points, point) : point)
    restriction = TensorRestriction(ntuple(3) do leg
        source_radix, target_radix = source_dims(sample)[leg], target_dims(sample)[leg]
        # Place the entire interpolation weight on leg 1 for this sample.
        function weight_at(point)
            leg != 1 && return big(1)
            use_roots && return big(1) // points
            return (isodd(point) ? 1 : -1) * binomial(points, point)
        end
        # Decode the sample from the source column and multiply the coefficients
        # of the replicas at that common sample.
        function coefficient(row, col)
            c, point = divrem(big(col) - 1, points)
            point += 1
            r = big(row) - 1
            evaluated = sample_at(point).legs[leg]
            weight = weight_at(point)
            for _ in 1:N
                r, i = divrem(r, target_radix)
                c, j = divrem(c, source_radix)
                term = evaluated[i + 1, j + 1]
                iszero(term) && return term
                weight *= term
            end
            return weight
        end
        # Stream all exact (source column, coefficient) pairs for a target row.
        function entries(row)
            # Insert this sample into the source columns and scale its row contributions.
            function sample_rows(point)
                evaluated = power_restriction(sample_at(point), N)
                weight = weight_at(point)
                return ((point + points * (col - 1), weight * value) for
                        (col, value) in row_entries(evaluated.legs[leg], row))
            end
            return Iterators.flatten(sample_rows(point) for point in 1:points)
        end
        return LegMap(points * src[leg], dst[leg], coefficient, entries)
    end...,)
    return (; points, restriction)
end

"""
    _attach_child!(layout, source, index)

Assign the factor named by `source` to the predecessor at `index`.

Rename the factor to `(:q, index)` or append it to the seed copies already
assigned to that predecessor.
"""
function _attach_child!(layout, source, index)
    target = (:q, index)
    here = _wire_position(layout, source)
    there = findfirst(wire -> wire.first == target, layout.wires)
    if isnothing(there)
        layout.wires[here] = _wire(target, layout.wires[here].second)
    else
        dims = _wire_dims(layout.wires[[there, here]])
        _replace_wires!(
            layout, [target, source], [_wire(target, dims)], identity_restriction(dims)
        )
    end
    return nothing
end

"""
    _auxiliary_wires(nodes, events, N) -> (wires, rank_maps)

Build the powered auxiliary factors and their preparation restrictions.

Allocate a unit factor for each midpoint or tripling event and a matrix
multiplication factor for each midpoint event. Each entry of `rank_maps`
restricts a unit tensor to the corresponding factor in `wires`.
"""
function _auxiliary_wires(nodes, events, N)
    wires = _WitnessWire[]
    rank_maps = TensorRestriction[]
    for event in events
        i = event.index
        kind = nodes[i].kind
        if kind === :midpoint || kind === :tripling
            dimension = event.multiplicity^(6N)
            push!(wires, _wire((:aux_unit, i), unit_dims(dimension)))
            push!(rank_maps, identity_restriction(unit_dims(dimension)))
        end
        if kind === :midpoint
            side = big(4)^(event.copies * N)
            push!(wires, _wire((:aux_matrix, i), mm_dims(side)))
            push!(rank_maps, unit_to_mm(side))
        end
    end
    return wires, rank_maps
end

"""
    _compile_sector!(layout, nodes, event, N, remaining, a, b, admissible_order=nothing)

Apply both interpolated phases of a midpoint or tripling event to `layout`.

Use `N` replicas of the event identified by `nodes` and `event`. Draw
unit factors from the seed at `(a, b)`, using the optional predicate
`admissible_order` to choose Fourier orders in each phase. Assign the
resulting seed copies to the predecessors, record the matrix gain, and
return the updated `BigInt` seed allowance.
"""
function _compile_sector!(
    layout, nodes, event, N, remaining, a, b, admissible_order=nothing
)
    i, k, M = event.index, event.copies, event.multiplicity
    node = nodes[i]
    midpoint = node.kind === :midpoint
    predecessors = node.predecessors
    parent = nodes[first(predecessors)]
    transition = if midpoint
        midpoint_transition(node.a, node.b, node.b - parent.b, event.counts[1], k)
    else
        tripling_transition(parent.a, parent.b, event.counts...)
    end
    budget = (:budget, 0)
    credit, unit, input = (:credit, i), (:aux_unit, i), (:q, i)
    remaining = _draw_unit!(layout, budget, remaining, big(64)^N, credit, a, b)
    unit_dims_single = unit_dims(64M^6)
    combined = _power_dims(unit_dims_single, N)
    _replace_wires!(
        layout, [credit, unit], [_wire(unit, combined)], identity_restriction(combined)
    )
    input_tags = [unit, input]
    input_factors = [unit_dims_single, _power_dims(seed_dims(node.a, node.b), k)]
    if midpoint
        matrix = (:aux_matrix, i)
        matrix_side = big(4)^k
        matrix_dims = mm_dims(matrix_side)
        unpack = _matrix_power(matrix_side, N; inverse=true)
        _replace_wires!(
            layout, [matrix], [_wire(matrix, _power_dims(matrix_dims, N))], unpack
        )
        push!(input_tags, matrix)
        push!(input_factors, matrix_dims)
    end
    phase = (:phase, i)
    first_phase = _interpolated_phase(transition, 1, N; admissible_order)
    remaining = _draw_unit!(layout, budget, remaining, first_phase.points, phase, a, b)
    group = product_restriction(
        identity_restriction(unit_dims(first_phase.points)),
        _replica_order(input_factors, N),
    )
    first_map = compose_restrictions(group, first_phase.restriction)
    middle = (:sector, i)
    _replace_wires!(
        layout,
        vcat([phase], input_tags),
        [_wire(middle, target_dims(first_map))],
        first_map,
    )
    second_phase = _interpolated_phase(transition, 2, N; admissible_order)
    remaining = _draw_unit!(layout, budget, remaining, second_phase.points, phase, a, b)
    output_factors = [unit_dims(M^6)]
    output_tags = [unit]
    child_counts = midpoint ? event.counts[1:2] : (k,)
    for (j, predecessor) in enumerate(predecessors)
        child = nodes[predecessor]
        push!(output_factors, _power_dims(seed_dims(child.a, child.b), child_counts[j]))
        push!(output_tags, (:child, j))
    end
    matrix = (:gain, i)
    push!(output_factors, mm_dims(M^2))
    push!(output_tags, matrix)
    second_map = compose_restrictions(
        second_phase.restriction, _replica_order(output_factors, N; inverse=true)
    )
    outputs = [
        _wire(tag, _power_dims(dims, N)) for (tag, dims) in zip(output_tags, output_factors)
    ]
    _replace_wires!(layout, [phase, middle], outputs, second_map)
    _replace_wires!(
        layout, [matrix], [_wire(matrix, mm_dims(M^(2N)))], _matrix_power(M^2, N)
    )
    for (j, predecessor) in enumerate(predecessors)
        if iszero(child_counts[j])
            _drop_wires!(layout, [(:child, j)])
        else
            _attach_child!(layout, (:child, j), predecessor)
        end
    end
    return remaining
end

"""
    _compile_round(nodes, plan, auxiliary, N, S, admissible_order=nothing)

Build the restriction for one reuse of the powered auxiliary tensor.

`plan` comes from [`_witness_events`](@ref). The source has `N^2` seed
copies, `18S*N` budget copies, and the factors in `auxiliary`. The target
has a matrix multiplication factor of side `plan.side^N` followed by the
returned auxiliary factors in their original order. Pass `admissible_order`
to select Fourier orders for the interpolated phases.
"""
function _compile_round(nodes, plan, auxiliary, N, S, admissible_order=nothing)
    last_node = last(nodes)
    a, b = last_node.a, last_node.b
    starting = (:q, length(nodes))
    budget = (:budget, 0)
    allowance = 18S * N
    layout = _WitnessLayout(vcat(
        [
            _wire(starting, _power_dims(seed_dims(a, b), N^2)),
            _wire(budget, _power_dims(seed_dims(a, b), allowance)),
        ],
        auxiliary,
    ),)
    executed = _WitnessEvent[]
    fallback = false
    for event in plan.events
        i = event.index
        node = nodes[i]
        if node.kind === :midpoint && event.side == 1
            fallback = true
            break
        elseif node.kind === :midpoint || node.kind === :tripling
            allowance = _compile_sector!(
                layout, nodes, event, N, allowance, a, b, admissible_order
            )
            push!(executed, event)
        else
            predecessor = only(node.predecessors)
            child = nodes[predecessor]
            map = if node.kind === :symmetry
                _seed_symmetry(node.a, node.b)
            else
                _seed_restrict(node.a, node.b, child.a, child.b)
            end
            power = event.copies * N
            _replace_wires!(
                layout,
                [(:q, i)],
                [_wire((:child, 1), _power_dims(seed_dims(child.a, child.b), power))],
                power_restriction(map, power),
            )
            _attach_child!(layout, (:child, 1), predecessor)
        end
    end
    result = (:product, 0)
    _drop_wires!(layout, [budget])
    if fallback
        _drop_wires!(layout, [wire.first for wire in layout.wires if wire.first[1] === :q])
        # In this branch the auxiliary factors were never consumed or changed.
        _replace_wires!(
            layout,
            _WitnessTag[],
            [_wire(result, mm_dims(1))],
            identity_restriction(mm_dims(1)),
        )
        side = big(1)
    else
        baseline_tags = _WitnessTag[]
        baseline_sides = BigInt[]
        for (index, copies) in plan.baseline
            node = nodes[index]
            leg_side = max(node.a, node.b)^2
            power = copies * N
            side = leg_side^power
            map = compose_restrictions(
                power_restriction(seed_baseline(node.a, node.b), power),
                _matrix_power(leg_side, power),
            )
            tag = (:q, index)
            _replace_wires!(layout, [tag], [_wire(tag, mm_dims(side))], map)
            push!(baseline_tags, tag)
            push!(baseline_sides, side)
        end
        side = prod(baseline_sides; init=big(1))
        _replace_wires!(
            layout,
            baseline_tags,
            [_wire(result, mm_dims(side))],
            mm_product(baseline_sides),
        )
    end
    for event in Iterators.reverse(executed)
        i = event.index
        @assert side == event.child_side^N
        gain = event.multiplicity^(2N)
        combined_side = side * gain
        map = mm_product([side, gain])
        side = event.side^N
        outputs = [_wire(result, mm_dims(side))]
        if nodes[i].kind === :midpoint
            returned = big(4)^(event.copies * N)
            map = compose_restrictions(map, mm_split(combined_side, [side, returned]))
            push!(outputs, _wire((:aux_matrix, i), mm_dims(returned)))
        end
        _replace_wires!(layout, [result, (:gain, i)], outputs, map)
    end
    _order_wires!(layout, vcat([result], [wire.first for wire in auxiliary]))
    @assert side == plan.side^N
    return _combine_restrictions(compose_restrictions, layout.stages)
end

"""
    WitnessRecipe(nodes, power, step_bound)

Store the derivation and budgets needed to rebuild a witness over another field.

`nodes` contains the derivation entries in dependency order, `power`
sets the tensor powers and reuse count, and `step_bound` determines the
reserved seed budget.
"""
struct WitnessRecipe
    nodes::Vector{DerivationNode}
    power::BigInt
    step_bound::BigInt
end

"""
    CompiledWitness(side, copies, restriction, recipe)

Represent an exact restriction from a seed power to matrix multiplication.

`side` is the matrix dimension and `copies` counts the seed factors in
the source. The `recipe` is a `WitnessRecipe` when the witness can be
rebuilt from a derivation, or `nothing` for a supplied restriction.
"""
struct CompiledWitness
    side::BigInt
    copies::BigInt
    restriction::TensorRestriction
    recipe::Union{Nothing,WitnessRecipe}
end

"""
    CompiledWitness(side, copies, restriction)

Wrap a supplied restriction without recording a derivation recipe.
"""
function CompiledWitness(side, copies, restriction)
    return CompiledWitness(side, copies, restriction, nothing)
end

"""
    compile_witness(nodes, N; step_bound=nothing, admissible_order=nothing)

Lower a derivation to the exact restriction in Lemma 6.2. Interpolation is
performed separately on the two phases of each sector transition after taking
the Nth tensor power. The powered auxiliary tensor is prepared once, returned
by each of N applications, and then restricted to a scalar.

Supply a finite iterable of `DerivationNode` entries in dependency order and a
positive integer power `N`. The derivation is collected into a
`Vector{DerivationNode}`. An integer `step_bound` must be at least the number of
non-baseline entries. The power, step bound, and seed-copy counts are `BigInt`s
in the compiler.

When provided, `admissible_order(order)` takes a `BigInt` Fourier order and
returns a `Bool` indicating whether that order is invertible in the coefficient
field. This also interpolates every phase at roots of unity.

Return a `CompiledWitness` with a `BigInt` matrix side and seed-copy count,
the `TensorRestriction`, and the `WitnessRecipe` used to build it.
"""
function compile_witness(
    nodes, N::Integer; step_bound::Union{Nothing,Integer}=nothing, admissible_order=nothing
)
    N = big(N)
    nodes = vec(collect(DerivationNode, nodes))
    plan = _witness_events(nodes, N)
    S = count(node -> node.kind !== :baseline, nodes)
    S_bound = isnothing(step_bound) ? big(S) : big(step_bound)
    S_bound >= S || throw(ArgumentError("the step bound is smaller than the derivation"))
    recipe = WitnessRecipe(nodes, N, S_bound)
    a, b = last(nodes).a, last(nodes).b
    copies = _witness_copies(S_bound, N)
    if iszero(S_bound)
        side = max(a, b)^2
        restriction = compose_restrictions(
            power_restriction(seed_baseline(a, b), copies), _matrix_power(side, copies)
        )
        return CompiledWitness(side^copies, copies, restriction, recipe)
    end
    seed = seed_dims(a, b)
    auxiliary, rank_maps = _auxiliary_wires(nodes, plan.events, N)
    prepare_copies = 16S_bound * N^2
    batch_copies = N^2 + 18S_bound * N
    round = _compile_round(nodes, plan, auxiliary, N, S_bound, admissible_order)
    round_side = plan.side^N
    raw, result = (:raw, 0), (:accumulator, 0)
    preparation = (:preparation, 0)
    layout = _WitnessLayout([
        _wire(preparation, _power_dims(seed, prepare_copies)),
        _wire(raw, _power_dims(seed, batch_copies * N)),
    ])
    aux_from_unit = if isempty(rank_maps)
        identity_restriction(unit_dims(1))
    else
        _combine_restrictions(product_restriction, rank_maps)
    end
    rank_count = source_dims(aux_from_unit)[1]
    prepare = compose_restrictions(
        _seed_to_unit(a, b, prepare_copies, rank_count), aux_from_unit
    )
    _replace_wires!(layout, [preparation], auxiliary, prepare)
    _replace_wires!(
        layout, _WitnessTag[], [_wire(result, mm_dims(1))], identity_restriction(mm_dims(1))
    )
    aux_tags = [wire.first for wire in auxiliary]
    batch, produced = (:batch, 0), (:produced, 0)
    side = big(1)
    for repetition in 1:N
        batch_dims = _power_dims(seed, batch_copies)
        raw_dims = _power_dims(seed, batch_copies * (N - repetition))
        resized = [_wire(batch, batch_dims), _wire(raw, raw_dims)]
        _replace_wires!(layout, [raw], resized, identity_restriction(_wire_dims(resized)))
        _replace_wires!(
            layout,
            vcat([batch], aux_tags),
            vcat([_wire(produced, mm_dims(round_side))], auxiliary),
            round,
        )
        map = mm_product([side, round_side])
        side *= round_side
        _replace_wires!(layout, [result, produced], [_wire(result, mm_dims(side))], map)
    end
    _drop_wires!(layout, vcat(aux_tags, [raw]))
    @assert side == plan.side^(N^2)
    restriction = _combine_restrictions(compose_restrictions, layout.stages)
    @assert source_dims(restriction) == _power_dims(seed, copies)
    @assert target_dims(restriction) == mm_dims(side)
    return CompiledWitness(side, copies, restriction, recipe)
end
