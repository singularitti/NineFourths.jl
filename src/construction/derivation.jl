"""
    ShpilkaDerivation(parameters::ShpilkaParameters)

Store the exact parameters for the derivation in Shpilka's Theorem 1.2.

The derivation starts with the baseline at `(q, q)` and applies Lemma 6.5
successively at step lengths `1, 2, 4, …, 2^(q-1)`. See
`materialize_derivation` for the resulting list of proof entries.
[Exposition of OpenAI’s Matrix Multiplication in Exponent 9/4 (and an explicit algorithm)](https://eccc.weizmann.ac.il/report/2026/281/).
"""
struct ShpilkaDerivation
    parameters::ShpilkaParameters
end

"""
    DerivationNode(a, b, value, kind, predecessors)

Represent one lower bound and its justification in a materialized derivation.

`a` and `b` are `BigInt` polynomial lengths. `value` is an exact
`Rational{BigInt}` lower bound on `F(a, b)`, the paper's supremum of witness
rates for the balanced polynomial tensor at those lengths. `kind` is one of
`:baseline`, `:restriction`, `:symmetry`, `:midpoint`, or `:tripling`.

`predecessors` stores `Int` indices into earlier entries of the same derivation.
A baseline has no predecessors, a midpoint has two in increasing column
order, and other rules have one.
"""
struct DerivationNode
    a::BigInt
    b::BigInt
    value::Rational{BigInt}
    kind::Symbol
    predecessors::Tuple{Vararg{Int}}
end

"""
    _push_derivation_node!(nodes, a, b, value, kind, predecessors)

Append a `DerivationNode` and return its one-based index.

`nodes` supports `push!` and `length`, as a `Vector{DerivationNode}` does.
Supply integer lengths, an exact rational bound, a rule symbol, and a tuple
of predecessor indices convertible to `Int`.
"""
function _push_derivation_node!(nodes, a, b, value, kind, predecessors)
    push!(nodes, DerivationNode(a, b, value, kind, predecessors))
    return length(nodes)
end

"""
    _extend_row!(nodes, start, distance, depth)

Extend a derivation along one row and return the index at the requested column.

Given `nodes[start]` at `(a,b)`, reach `(a,b + distance)` using Lemma 6.3
and Claim 6.4. `distance` lies in `1:a+2b`, and `depth` is the nonnegative
limit on the number of midpoint steps. `nodes` is a one-based, appendable
collection of `DerivationNode` entries. Build the chain of midpoint targets,
then append its steps in dependency order, starting from an endpoint or a
restriction of the original bound.
"""
function _extend_row!(nodes, start, distance, depth)
    initial = nodes[start]
    a, b, value = initial.a, initial.b, initial.value
    tripled = _push_derivation_node!(nodes, a, 3b + a - 1, 3value, :tripling, (start,))
    upper_column = 3b + a
    upper = _push_derivation_node!(nodes, a, upper_column, 3value, :restriction, (tripled,))
    chain = Tuple{BigInt,Int}[]
    column = b + distance
    while depth > 0 && b < column < upper_column
        endpoint = 2column <= b + upper_column ? start : upper
        push!(chain, (column, endpoint))
        column = 2column - nodes[endpoint].b
        depth -= 1
    end
    index = if column == b
        start
    elseif column == upper_column
        upper
    else
        _push_derivation_node!(nodes, a, column, value, :restriction, (start,))
    end
    for (column, endpoint) in Iterators.reverse(chain)
        predecessors = endpoint == start ? (endpoint, index) : (index, endpoint)
        midpoint = (nodes[endpoint].value + nodes[index].value) / 2
        index = _push_derivation_node!(nodes, a, column, midpoint, :midpoint, predecessors)
    end
    return index
end

"""
    materialize_derivation(derivation)::Vector{DerivationNode}

Generate the proof entries in dependency order with exact dyadic values.
Use a `ShpilkaDerivation` or another description exposing a positive `Integer`
`derivation.parameters.q`. This enumerates the full derivation, including
intermediate entries of the row extensions. For targets close to `9//4` it
can require substantial resources.
"""
function materialize_derivation(derivation)
    q = derivation.parameters.q
    nodes = [DerivationNode(q, q, q // 1, :baseline, ())]
    index = 1
    distance = big(1)
    for _ in 1:q
        # Lemma 6.5 uses q moves of this length to double both coordinates.
        for _ in 1:q
            index = _extend_row!(nodes, index, distance, q)
            moved = nodes[index]
            index = _push_derivation_node!(
                nodes, moved.b, moved.a, moved.value, :symmetry, (index,)
            )
            index = _extend_row!(nodes, index, distance, q)
        end
        distance *= 2
    end
    return nodes
end
