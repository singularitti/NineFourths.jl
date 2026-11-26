@testset "Shpilka parameters" begin
    params = NineFourths.ShpilkaParameters(5 // 2)
    @test params.target == 5 // 2
    @test params.epsilon == 1 // 4
    @test params.q == 256
    @test params.a == big(256) << 256
    @test params.step_bound == 256 * (2 * 256^2 + 7 * 256)
    @test params.length_bound == 4 * params.a
    @test NineFourths.ShpilkaParameters(10).q == 16
    @test_throws DomainError NineFourths.ShpilkaParameters(9 // 4)
    @test_throws DomainError NineFourths.ShpilkaParameters(2)
    @test_throws DomainError NineFourths.ShpilkaParameters(1 // 0)
    @test_throws MethodError NineFourths.ShpilkaParameters(2.5)

    gap = 1 // big(10)^20
    large = NineFourths.ShpilkaParameters(9 // 4 + gap)
    @test large.epsilon == gap
    @test large.q == 16 * big(10)^40
    @test large.a.coefficient == large.q
    @test large.a.exponent == large.q
    @test large.length_bound.coefficient == 4 * large.q
    @test large.length_bound.exponent == large.q

    expanded = NineFourths._scaled_power_of_two(Int8(3), UInt16(200))
    @test expanded isa BigInt
    @test expanded == big(3) << 200
    factored = NineFourths._scaled_power_of_two(UInt8(3), Int16(4097))
    @test factored.coefficient == 3
    @test factored.exponent == 4097
end

@testset "Shpilka derivation" begin
    params = NineFourths.ShpilkaParameters(13 // 4)
    derivation = NineFourths.ShpilkaDerivation(params)
    nodes = NineFourths.materialize_derivation(derivation)
    @test length(nodes) - 1 <= params.step_bound
    @test nodes[1].a == nodes[1].b == nodes[1].value == params.q
    @test nodes[1].kind == :baseline
    @test isempty(nodes[1].predecessors)
    @test nodes[end].a == nodes[end].b == params.a
    @test 8 * nodes[end].value^3 >= params.q^3 * (big(1) << Int(4 * params.q))

    kinds = Set{Symbol}()
    for (i, node) in enumerate(nodes)
        push!(kinds, node.kind)
        @test 1 <= node.a < params.length_bound
        @test 1 <= node.b < params.length_bound
        @test ispow2(denominator(node.value))
        @test all(1 <= predecessor < i for predecessor in node.predecessors)

        if node.kind == :midpoint
            left, right = nodes[collect(node.predecessors)]
            @test left.a == node.a == right.a
            @test left.b < node.b < right.b
            @test left.b + right.b == 2 * node.b
            @test node.value == (left.value + right.value) / 2
        elseif node.kind == :tripling
            previous = nodes[only(node.predecessors)]
            @test node.a == previous.a
            @test node.b == 3 * previous.b + previous.a - 1
            @test node.value == 3 * previous.value
        elseif node.kind == :symmetry
            previous = nodes[only(node.predecessors)]
            @test (node.a, node.b, node.value) == (previous.b, previous.a, previous.value)
        elseif node.kind == :restriction
            previous = nodes[only(node.predecessors)]
            @test node.a >= previous.a
            @test node.b >= previous.b
            @test node.value == previous.value
        else
            @test i == 1
        end
    end
    @test kinds == Set((:baseline, :midpoint, :tripling, :symmetry, :restriction))
end
