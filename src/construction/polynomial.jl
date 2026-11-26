# Six NTuple{3,Int} permutations map legs in Q to legs in C(a,b).
const LEG_PERMUTATIONS = ((1, 2, 3), (3, 1, 2), (2, 3, 1), (2, 1, 3), (3, 2, 1), (1, 3, 2))

struct PolynomialDecomposition
    dimensions::NTuple{3,BigInt}
    order::BigInt
end

# For positive integer input lengths a and b, return the three leg sizes
# as an NTuple{3,BigInt}.
function polynomial_dims(a::Integer, b::Integer)
    a > 0 && b > 0 || throw(ArgumentError("polynomial input lengths must be positive"))
    first, second = BigInt(a), BigInt(b)
    return (first, second, first + second - 1)
end

# preferred and alternate are positive BigInt orders. admissible_order is
# nothing or a callable returning Bool for a candidate order.
function _sample_order(admissible_order, preferred, alternate)
    isnothing(admissible_order) && return preferred
    admissible_order(preferred) && return preferred
    admissible_order(alternate) && return alternate
    return throw(ArgumentError("neither root-of-unity order is invertible in the coefficient field"))
end

"""
Return a `PolynomialDecomposition` by evaluating and interpolating at roots
of unity, as in Theorem 3.1. The input lengths `a` and `b` are positive
integers. Supply `nothing` or an `admissible_order(order)` callable returning
`Bool` for a `BigInt` order. It selects an invertible order from `a+b-1` and
`a+b`. Both orders exceed the degree of the product.
"""
function polynomial_decomposition(a, b; admissible_order=nothing)
    dimensions = polynomial_dims(a, b)
    minimum_order = dimensions[3]
    order = _sample_order(admissible_order, minimum_order, minimum_order + 1)
    return PolynomialDecomposition(dimensions, order)
end

Base.size(decomposition::PolynomialDecomposition) = decomposition.dimensions

# The polynomial rank is the BigInt Fourier order.
rank_count(decomposition::PolynomialDecomposition) = decomposition.order

# Return a Rational{BigInt} or PhaseSum for the one-based integer term, leg
# and coordinate in a PolynomialDecomposition.
function rank_coefficient(
    decomposition::PolynomialDecomposition, term::Integer, leg::Integer, coordinate::Integer
)
    check_rank_coordinate(decomposition, term, leg, coordinate)
    order = rank_count(decomposition)
    exponent = (BigInt(term) - 1) * (BigInt(coordinate) - 1)
    # The inverse Vandermonde is the conjugate transform divided by its side.
    return if leg == 3
        root_of_unity(order, -exponent) / order
    else
        root_of_unity(order, exponent)
    end
end

struct SeedDecomposition
    polynomial::PolynomialDecomposition
    copies::BigInt
    dimensions::NTuple{3,BigInt}
    terms::BigInt
end

# For positive integer polynomial lengths a and b, return the balanced seed's
# leg dimensions as an NTuple{3,BigInt}.
function seed_dims(a, b)
    dimension = prod(polynomial_dims(a, b))^2
    return (dimension, dimension, dimension)
end

"""
Return a `SeedDecomposition` of `Q(a,b)⊗m` for positive integer lengths `a`
and `b` and a nonnegative integer number of copies `m`. The first tensor
factor varies fastest. `admissible_order` is `nothing` or a callable mapping
a `BigInt` order to `Bool`, as in `polynomial_decomposition`.
"""
function seed_decomposition(a, b, m::Integer=1; admissible_order=nothing)
    m >= 0 || throw(ArgumentError("the number of seed copies must be nonnegative"))
    polynomial = polynomial_decomposition(a, b; admissible_order)
    copies = BigInt(m)
    dimensions = map(dimension -> dimension^copies, seed_dims(a, b))
    return SeedDecomposition(
        polynomial, copies, dimensions, rank_count(polynomial)^(6copies)
    )
end

Base.size(decomposition::SeedDecomposition) = decomposition.dimensions

function Base.size(
    decomposition::Union{PolynomialDecomposition,SeedDecomposition}, leg::Integer
)
    return size(decomposition)[leg]
end

# The seed rank is the BigInt count of terms in the tensor power.
rank_count(decomposition::SeedDecomposition) = decomposition.terms

# Use a decomposition supporting rank_count and a three-leg size tuple.
# term, leg and coordinate are one-based integers.
function check_rank_coordinate(decomposition, term, leg, coordinate)
    1 <= leg <= 3 || throw(BoundsError(1:3, leg))
    1 <= term <= rank_count(decomposition) || throw(BoundsError(decomposition, term))
    1 <= coordinate <= size(decomposition)[leg] ||
        throw(BoundsError(decomposition, coordinate))
    return nothing
end

# Return a Rational{BigInt} or PhaseSum for the one-based integer term, leg
# and coordinate in a SeedDecomposition.
function rank_coefficient(
    decomposition::SeedDecomposition, term::Integer, leg::Integer, coordinate::Integer
)
    check_rank_coordinate(decomposition, term, leg, coordinate)
    polynomial = decomposition.polynomial
    order = rank_count(polynomial)
    exponent = big(0)
    term_index, coordinate_index = BigInt(term) - 1, BigInt(coordinate) - 1
    for _ in 1:decomposition.copies, permutation in LEG_PERMUTATIONS
        original_leg = permutation[leg]
        term_index, term_digit = divrem(term_index, order)
        coordinate_index, coordinate_digit = divrem(
            coordinate_index, size(polynomial)[original_leg]
        )
        local_exponent = term_digit * coordinate_digit
        exponent += original_leg == 3 ? -local_exponent : local_exponent
    end
    # Each leg includes the polynomial output twice per seed copy.
    return root_of_unity(order, exponent) / order^(2decomposition.copies)
end

# The shorter input is fixed to its constant term in each copy of C(a,b).
# Each dot product then shares one digit of the matrix row, inner or column
# index, depending on the leg containing its scalar.
# dimensions is an NTuple{3,BigInt}. scalar_leg and leg are one-based integer
# leg indices. matrix_size, digit_base and the one-based coordinate are integers.
# Each permutation contains scalar_leg exactly once, so missing_leg is its Int
# position in 1:3. The resulting source coordinate is a BigInt.
function baseline_source_coordinate(
    dimensions, scalar_leg, leg, matrix_size, digit_base, coordinate
)
    column, row = divrem(BigInt(coordinate) - 1, matrix_size)
    unused = big(0)
    axis_digits = if leg == 1
        (unused, row, column)
    elseif leg == 2
        (column, unused, row)
    else
        (column, row, unused)
    end
    source = big(0)
    stride = big(1)
    for permutation in LEG_PERMUTATIONS
        original_leg = permutation[leg]
        if original_leg != scalar_leg
            missing_leg = findfirst(==(scalar_leg), permutation)
            remaining, digit = divrem(axis_digits[missing_leg], digit_base)
            axis_digits = Base.setindex(axis_digits, remaining, missing_leg)
            source += stride * digit
        end
        stride *= dimensions[original_leg]
    end
    return source + 1
end

# a and b are positive integer lengths. target_dimensions is an NTuple{3,BigInt}.
# matrix_coordinate maps a BigInt target row to a one-based integer matrix
# coordinate for each leg of the resulting TensorRestriction.
function seed_matrix_selection(a, b, target_dimensions, matrix_coordinate)
    dimensions = polynomial_dims(a, b)
    source_dimensions = seed_dims(a, b)
    scalar_leg = a <= b ? 1 : 2
    digit_base = BigInt(max(a, b))
    matrix_size = digit_base^2
    legs = ntuple(3) do leg
        # A BigInt target row maps to one BigInt source column for this leg.
        source_column = function (row)
            return baseline_source_coordinate(
                dimensions,
                scalar_leg,
                leg,
                matrix_size,
                digit_base,
                matrix_coordinate(row),
            )
        end
        return selection_map(source_dimensions[leg], target_dimensions[leg], source_column)
    end
    return TensorRestriction(legs...)
end

"""
Construct a `TensorRestriction` from `Q(a,b)` to `M_max(a,b)^2` using
Lemmas 3.4 and 3.8. The lengths `a` and `b` are positive integers.
"""
function seed_baseline(a::Integer, b::Integer)
    return seed_matrix_selection(a, b, mm_dims(BigInt(max(a, b))^2), identity)
end

"""
Construct a `TensorRestriction` from `Q(a,b)` to `I₂` for positive integer
lengths `a` and `b` with `(a,b) ≠ (1,1)`.
"""
function seed_unit(a::Integer, b::Integer)
    matrix_size = BigInt(max(a, b))^2
    matrix_size >= 2 || throw(ArgumentError("a seed of size (1,1) cannot restrict to I₂"))
    return seed_matrix_selection(
        a, b, unit_dims(2), row -> 1 + (row - 1) * (matrix_size + 1)
    )
end
