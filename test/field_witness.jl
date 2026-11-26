import Nemo

@testset "Compiled midpoint tensor identity in characteristic two" begin
    field, root = Nemo.finite_field(2, 3, :z)
    @test root^7 == one(field) && root != one(field)
    powers = [root^i for i in 0:6]

    embed(value::Integer) = field(value)
    embed(value::Rational) = field(numerator(value)) / field(denominator(value))
    function embed(value::NineFourths.PhaseSum)
        return sum(value.terms; init=zero(field)) do (phase, weight)
            # Phases can have denominator fourteen after sign normalization.
            # In characteristic two, the fourteenth-root symbol maps to
            # root^4, whose square is root.
            exponent = 14 * phase
            @assert isinteger(exponent)
            return embed(weight) * powers[Int(mod(4 * numerator(exponent), 7)) + 1]
        end
    end

    nodes = [NineFourths.DerivationNode(1, 1, 1 // 1, :baseline, ()),
             NineFourths.DerivationNode(1, 3, 3 // 1, :baseline, ()),
             NineFourths.DerivationNode(1, 2, 2 // 1, :midpoint, (1, 2))]
    witness = NineFourths.compile_witness(nodes, 1; admissible_order=isodd)
    @test witness.side == 2
    test_midpoint_tensor_identity(witness; embed, zero_weight=zero(field))
end
