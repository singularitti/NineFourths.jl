"""
    ShpilkaDerivation(parameters::ShpilkaParameters)

Store the exact `ShpilkaParameters` for the derivation in Theorem 1.2 of Shpilka's
*Exposition of OpenAI’s Matrix Multiplication in Exponent 9/4
(and an explicit algorithm)*.
It starts with the baseline at `(q, q)` and applies Lemma 6.5 at step lengths
`1, 2, 4, …, 2^(q-1)`.
"""
struct ShpilkaDerivation
    parameters::ShpilkaParameters
end

"""
An entry of a materialized derivation. `a` and `b` are `BigInt` polynomial
lengths, and `value` is an exact `Rational{BigInt}` lower bound on `F(a, b)`.
`kind` is a rule symbol such as `:baseline` or `:midpoint`. `predecessors`
is a tuple of `Int` indices into earlier entries of the same derivation.
Midpoint predecessors are in increasing column order.
"""
struct DerivationNode
    a::BigInt
    b::BigInt
    value::Rational{BigInt}
    kind::Symbol
    predecessors::Tuple{Vararg{Int}}
end

# Append to a collection such as Vector{DerivationNode} supporting push! and
# length. Supply integer lengths, an exact rational bound, a rule Symbol and
# a tuple of predecessor indices convertible to Int. Return the new index.
function _push_derivation_node!(nodes, a, b, value, kind, predecessors)
    push!(nodes, DerivationNode(a, b, value, kind, predecessors))
    return length(nodes)
end

# Lemma 6.3 and Claim 6.4. Build the chain of midpoint targets, then emit
# its steps in dependency order starting from the endpoint or restriction.
# Use a one-based, appendable collection of DerivationNode entries, an integer
# start index, an integer distance and a nonnegative integer depth limit.
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
    materialize_derivation(derivation) -> Vector{DerivationNode}

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
