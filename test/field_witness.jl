@testset "Compiled midpoint tensor identity in characteristic two" begin
    field, root = Nemo.finite_field(2, 3, :z)
    @test root^7 == one(field) && root != one(field)
    # `Vector{typeof(root)}` indexed by the exponent modulo seven plus one.
    powers = [root^i for i in 0:6]

    # Embed an integer as an element of the Nemo extension field.
    embed(value::Integer) = field(value)
    # Embed a rational whose denominator is invertible in the field.
    embed(value::Rational) = field(numerator(value)) / field(denominator(value))
    # Embed a symbolic sum of rationally weighted roots into the same field.
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

    nodes = [
        NineFourths.DerivationNode(1, 1, 1 // 1, :baseline, ()),
        NineFourths.DerivationNode(1, 3, 3 // 1, :baseline, ()),
        NineFourths.DerivationNode(1, 2, 2 // 1, :midpoint, (1, 2)),
    ]
    witness = NineFourths.compile_witness(
        Iterators.Stateful(nodes), 1; admissible_order=isodd
    )
    @test witness.side == 2
    test_midpoint_tensor_identity(witness; embed, zero_weight=zero(field))
end
