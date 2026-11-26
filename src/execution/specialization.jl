"""
    _specialize_scheme(scheme, admissible)

Prepare `scheme` for the scalar domain identified by `admissible`.

The callback accepts a positive integer order and reports whether it is usable
in that domain. Return `scheme` unchanged when it has no field-dependent construction.
"""
_specialize_scheme(scheme, admissible) = scheme

"""
    _specialize_scheme(scheme::ShpilkaScheme, admissible)

Lower a symbolic scheme by selecting admissible Fourier and interpolation orders.
"""
function _specialize_scheme(s::ShpilkaScheme, admissible)
    return lower_scheme(s; admissible_order=admissible)
end

"""
    _specialize_scheme(scheme::LoweredScheme, admissible)

Rebuild the polynomial seed and any nonbaseline witness for admissible orders.

Use the witness's stored recipe when it records a nonbaseline construction.
Reuse the witness when the recipe is absent or the witness is a baseline restriction.
"""
function _specialize_scheme(s::LoweredScheme, admissible)
    recipe = s.witness.recipe
    a, b, _ = size(s.seed.polynomial)
    seed = seed_decomposition(a, b, s.seed.copies; admissible_order=admissible)
    # The baseline restriction is just a selection of variables. It is valid
    # verbatim in every characteristic, even when the seed's rank changes.
    witness = if isnothing(recipe) || iszero(recipe.step_bound)
        s.witness
    else
        compile_witness(
            recipe.nodes,
            recipe.power;
            step_bound=recipe.step_bound,
            admissible_order=admissible,
        )
    end
    return LoweredScheme(seed, witness)
end

"""
    _scheme_arithmetic(scheme, inputs) -> (scheme, domain)

Pair a specialized executable scheme with the domain from `_field_inputs`.

Determine admissible orders from their integer embeddings in the selected domain.
"""
function _scheme_arithmetic(scheme, inputs)
    # Return whether an integer order is invertible in the selected scalar field.
    admissible(order) = _field_unit_integer(inputs.one, order)
    return (; scheme=_specialize_scheme(scheme, admissible), domain=inputs)
end

"""
    _scheme_weight(field, value::PhaseSum)

Embed the rational weights of a formal phase sum in the selected domain.

Return a native scalar when the phase sum simplifies to one, or a `FieldPhaseSum`.
"""
function _scheme_weight(field, value::PhaseSum)
    return _field_phase_coefficient(
        weight -> _field_rational(field.one, weight), value, field.zero
    )
end

"""
    _scheme_weight(field, value::Nemo.QQBarFieldElem)

Embed an algebraic coefficient in the domain described by `field`.

Embed rational values through the rational method. Keep other values algebraic
for inferred Julia exact arithmetic. For a complex exact domain, require rational
real and imaginary components. Other domains use native coefficient embedding.
"""
function _scheme_weight(field, value::Nemo.QQBarFieldElem)
    Nemo.is_rational(value) && return _scheme_weight(field, rational_result(value))
    field.legacy && return value
    if field.one isa Complex{<:_BuiltinExact}
        try
            return complex(rational_result(real(value)), rational_result(imag(value)))
        catch error
            error isa DomainError || rethrow()
            throw(CoefficientIncompatible("the algebraic coefficient is outside the Gaussian rational field"),)
        end
    end
    return _field_embed_native(field, value)
end

"""
    _scheme_weight(field, value)

Embed a scalar coefficient using the configuration returned by `_field_configuration`.
"""
_scheme_weight(field, value) = _field_embed_native(field, value)

"""
    _field_coefficient(field, scheme, term, leg, coordinate)

Read and embed a scheme coefficient in the execution domain.

The indices are one-based. Legs 1 and 2 address the left and right input forms,
and leg 3 addresses the output weights. Blocks use column-major coordinates.
"""
function _field_coefficient(field, scheme, term, leg, coordinate)
    return _scheme_weight(field, scheme_coefficient(scheme, term, leg, coordinate))
end

"""
    _concrete_algebraic_value(value)::Nemo.QQBarFieldElem

Evaluate formal phase terms in Nemo's algebraic closure of the rationals.

Use a consistent embedding for roots of unity and algebraic weights. Each pair
in `value.terms` supplies one phase and a weight that embeds in the closure.
"""
function _concrete_algebraic_value(value)
    result = ALGEBRAIC_NUMBERS(0)
    for (phase, weight) in value.terms
        root = root_of_unity(denominator(phase), numerator(phase))
        result += weight * (root isa PhaseSum ? as_qqbar(root) : root)
    end
    return result
end

"""
    _field_result(field, value)

Convert a native scalar or a formal phase work value to the output element type.

Resolve any phases in the selected scalar domain before converting to `field.eltype`.
"""
function _field_result(field, value)
    if value isa FieldPhaseSum
        if field.one isa Nemo.QQBarFieldElem ||
            any(w -> w isa Nemo.QQBarFieldElem, values(value.terms))
            value = _concrete_algebraic_value(value)
        elseif field.one isa Complex
            value = _project_complex_value(value)
        elseif field.legacy
            terms = Dict(phase => to_exact(weight) for (phase, weight) in value.terms)
            value = rational_result(PhaseSum(terms))
        else
            value = _project_field_value(value)
        end
    end
    if field.legacy && value isa Nemo.QQBarFieldElem
        value = rational_result(value)
    end
    if field.eltype === Nemo.ZZRingElem && value isa Nemo.QQFieldElem
        return Nemo.ZZ(value)
    end
    return convert(field.eltype, value)
end
