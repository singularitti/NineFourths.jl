# Section 6.1. Reverse the derivation before making any substitution maps.
struct _WitnessEvent
    index::Int
    copies::BigInt
    counts::NTuple{3,BigInt}
    multiplicity::BigInt
    child_side::BigInt
    side::BigInt
end

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
and a positive integer power `N`.
"""
witness_side(nodes, N::Integer) = _witness_events(nodes, N).side^(big(N)^2)

# Preparation costs 16SN². Each reuse costs N² seeds plus at most 18SN
# seeds: 6N for the unit credit and at most 6N for each interpolation phase
# per derivation step. The latter follows from 6N*9^N + 2 ≤ 64^N.
_witness_copies(S, N) = big(N)^3 + 34big(S) * big(N)^2

const _WitnessTag = Tuple{Symbol,Int}
const _WitnessDims = NTuple{3,BigInt}
const _WitnessWire = Pair{_WitnessTag,_WitnessDims}

_wire(tag, dims) = _WitnessWire(tag, map(big, dims))
_power_dims(dims, n) = map(dimension -> big(dimension)^n, dims)

function _wire_dims(wires)
    return ntuple(leg -> prod((wire.second[leg] for wire in wires); init=big(1)), 3)
end

# Each wire holds one complete tensor factor. A substitution consumes named
# factors and is tensored with identities on the remaining factors.
struct _WitnessLayout
    wires::Vector{_WitnessWire}
    stages::Vector{TensorRestriction}
end

_WitnessLayout(wires) = _WitnessLayout(wires, TensorRestriction[])

# Keep the restriction and its row iterator logarithmic in the number of
# stages. The leaves still appear in their original application order.
function _combine_restrictions(combine, maps, start=firstindex(maps), stop=lastindex(maps))
    start == stop && return maps[start]
    middle = start + (stop - start) ÷ 2
    return combine(
        _combine_restrictions(combine, maps, start, middle),
        _combine_restrictions(combine, maps, middle + 1, stop),
    )
end

function _wire_position(layout, tag)
    index = findfirst(wire -> wire.first == tag, layout.wires)
    isnothing(index) && error("missing tensor factor $(tag)")
    return index
end

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

function _order_wires!(layout, tags)
    order = [_wire_position(layout, tag) for tag in tags]
    length(order) == length(layout.wires) || error("incomplete tensor layout")
    if !issorted(order)
        push!(layout.stages, permute_factors([wire.second for wire in layout.wires], order))
        layout.wires[:] = layout.wires[order]
    end
    return nothing
end

function _drop_wires!(layout, tags)
    isempty(tags) && return nothing
    wires = [layout.wires[_wire_position(layout, tag)] for tag in tags]
    _replace_wires!(layout, tags, _WitnessWire[], discard_restriction(_wire_dims(wires)))
    return nothing
end

function _coordinates(index, dimensions)
    coordinates = BigInt[]
    quotient = big(index) - 1
    for dimension in dimensions
        quotient, digit = divrem(quotient, dimension)
        push!(coordinates, digit + 1)
    end
    return coordinates
end

function _coordinate(coordinates, dimensions)
    index, stride = big(1), big(1)
    for (digit, dimension) in zip(coordinates, dimensions)
        index += (digit - 1) * stride
        stride *= dimension
    end
    return index
end

function _seed_restrict(a, b, c, d)
    src, dst = (a, b, a + b - 1), (c, d, c + d - 1)
    return TensorRestriction(
        ntuple(3) do leg
            sd = map(p -> src[p[leg]], LEG_PERMUTATIONS)
            td = map(p -> dst[p[leg]], LEG_PERMUTATIONS)
            return selection_map(
                prod(sd), prod(td), row -> _coordinate(_coordinates(row, td), sd)
            )
        end...,
    )
end

function _seed_symmetry(a, b)
    src = (a, b, a + b - 1)
    order = map(LEG_PERMUTATIONS) do p
        swapped = map(i -> i == 3 ? i : 3 - i, p)
        return findfirst(==(swapped), LEG_PERMUTATIONS)
    end
    inverse = invperm(collect(order))
    return TensorRestriction(
        ntuple(3) do leg
            sd = map(p -> src[p[leg]], LEG_PERMUTATIONS)
            td = map(i -> sd[i], order)
            return selection_map(
                prod(sd), prod(td), row -> _coordinate(_coordinates(row, td)[inverse], sd)
            )
        end...,
    )
end

# Change from (U^N)⊗(V^N)⊗⋯ to (U⊗V⊗⋯)^N, or the inverse. The
# radix for each wire is determined independently on each tensor leg.
function _replica_order(factors, N; inverse=false)
    dimensions = ntuple(leg -> prod((dims[leg] for dims in factors); init=big(1)), 3)
    powered = _power_dims(dimensions, N)
    (N == 1 || length(factors) <= 1) && return identity_restriction(powered)
    return TensorRestriction(
        ntuple(3) do leg
            radices = [dims[leg] for dims in factors]
            wire_radices = [d^N for d in radices]
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
        end...,
    )
end

# A matrix side power uses one packed row/column pair, whereas a tensor power
# uses interleaved pairs, one for each copy.
function _matrix_power(side, N; inverse=false)
    side, N = big(side), big(N)
    packed_side = side^N
    dimension = packed_side^2
    radix = side^2
    (side == 1 || N == 1) && return identity_restriction((dimension, dimension, dimension))
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

_binary_units(dimension) = dimension == 1 ? 0 : ndigits(dimension - 1; base=2)

function _seed_to_unit(a, b, count, dimension)
    dimension == 1 && return discard_restriction(_power_dims(seed_dims(a, b), count))
    return compose_restrictions(
        power_restriction(seed_unit(a, b), count), unit_trim(big(2)^count, dimension)
    )
end

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

# Evaluate the same point at every copy of this phase. For samples 1,…,D+1
# the constant-term weights are signed binomials. Over a field of arbitrary
# characteristic, use the mean of evaluations at Lth roots with L > D.
function _interpolated_phase(transition, phase, N; admissible_order=nothing)
    degree = N * transition_degree(transition, phase)
    points =
        iszero(degree) ? big(1) : _sample_order(admissible_order, degree + 1, degree + 2)
    use_roots = !isnothing(admissible_order)
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
    sample_at(point) = evaluate(use_roots ? root_of_unity(points, point) : point)
    restriction = TensorRestriction(
        ntuple(3) do leg
            source_radix, target_radix = source_dims(sample)[leg], target_dims(sample)[leg]
            function weight_at(point)
                leg != 1 && return big(1)
                use_roots && return big(1) // points
                return (isodd(point) ? 1 : -1) * binomial(points, point)
            end
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
            function entries(row)
                function sample_rows(point)
                    evaluated = power_restriction(sample_at(point), N)
                    weight = weight_at(point)
                    return (
                        (point + points * (col - 1), weight * value) for
                        (col, value) in row_entries(evaluated.legs[leg], row)
                    )
                end
                return Iterators.flatten(sample_rows(point) for point in 1:points)
            end
            return LegMap(points * src[leg], dst[leg], coefficient, entries)
        end...,
    )
    return (; points, restriction)
end

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

function _compile_round(nodes, plan, auxiliary, N, S, admissible_order=nothing)
    last_node = last(nodes)
    a, b = last_node.a, last_node.b
    starting = (:q, length(nodes))
    budget = (:budget, 0)
    allowance = 18S * N
    layout = _WitnessLayout(
        vcat(
            [
                _wire(starting, _power_dims(seed_dims(a, b), N^2)),
                _wire(budget, _power_dims(seed_dims(a, b), allowance)),
            ],
            auxiliary,
        ),
    )
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

struct WitnessRecipe
    nodes::Vector{DerivationNode}
    power::BigInt
    step_bound::BigInt
end

struct CompiledWitness
    side::BigInt
    copies::BigInt
    restriction::TensorRestriction
    recipe::Union{Nothing,WitnessRecipe}
end

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
positive integer power `N`. An integer `step_bound` must be at least the number
of non-baseline entries.

Supply an `admissible_order` predicate to choose Fourier orders invertible in
a coefficient field. This also interpolates every phase at roots of unity.
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
