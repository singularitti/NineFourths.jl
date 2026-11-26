# The symbolic target is field-independent. At execution time every Fourier
# order and interpolation denominator must be invertible in the input field.
# The admissible callback accepts a positive integer order and returns Bool.
# Schemes without a field-dependent construction are already specialized.
_specialize_scheme(scheme, admissible) = scheme

# Lower a symbolic ShpilkaScheme using the integer-to-Bool admissibility test.
function _specialize_scheme(s::ShpilkaScheme, admissible)
    return lower_scheme(s; admissible_order=admissible)
end

# Rebuild a LoweredScheme for the admissible Fourier orders. The optional
# WitnessRecipe carries the construction inputs needed to rebuild its witness.
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

# Pair an executable scheme with its domain, the field configuration and
# normalized matrices returned by _field_inputs.
function _scheme_arithmetic(scheme, inputs)
    # Return whether an integer order is invertible in the selected scalar field.
    admissible(order) = _field_unit_integer(inputs.one, order)
    return (; scheme=_specialize_scheme(scheme, admissible), domain=inputs)
end

# The field is the _field_configuration named tuple, with or without the input
# matrices. Embed a scheme coefficient as a scalar or FieldPhaseSum work value.
function _scheme_weight(field, value::PhaseSum)
    return _field_phase_coefficient(
        weight -> _field_rational(field.one, weight), value, field.zero
    )
end

# field is the configuration record. A QQBar weight may be rational,
# Gaussian rational, or a native element of its algebraic coefficient field.
function _scheme_weight(field, value::Nemo.QQBarFieldElem)
    Nemo.is_rational(value) && return _scheme_weight(field, rational_result(value))
    field.legacy && return value
    if field.one isa Complex{<:_BuiltinExact}
        try
            return complex(rational_result(real(value)), rational_result(imag(value)))
        catch error
            error isa DomainError || rethrow()
            throw(
                CoefficientIncompatible(
                    "the algebraic coefficient is outside the Gaussian rational field"
                ),
            )
        end
    end
    return _field_embed_native(field, value)
end

# Embed the scalar weight value in the domain described by the field configuration.
_scheme_weight(field, value) = _field_embed_native(field, value)

# scheme is a BilinearScheme or supplies scheme_coefficient, and field is the
# field configuration. The integer indices identify the one-based term, leg
# (1, 2, or 3), and block coordinate.
function _field_coefficient(field, scheme, term, leg, coordinate)
    return _scheme_weight(field, scheme_coefficient(scheme, term, leg, coordinate))
end

# A supplied algebraic-number coefficient can belong to the same concrete
# number field as a symbolic root. Evaluate them with a consistent embedding.
# value.terms supplies (phase, weight) pairs as in a FieldPhaseSum. Its weights
# embed in Nemo's algebraic closure of the rationals. Return a Nemo.QQBarFieldElem.
function _concrete_algebraic_value(value)
    result = ALGEBRAIC_NUMBERS(0)
    for (phase, weight) in value.terms
        root = root_of_unity(denominator(phase), numerator(phase))
        result += weight * (root isa PhaseSum ? as_qqbar(root) : root)
    end
    return result
end

# Convert a scalar or FieldPhaseSum work value to the output eltype in the
# field configuration. The legacy flag selects inferred exact Julia arithmetic.
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
