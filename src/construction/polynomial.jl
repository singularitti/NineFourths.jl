# Each permutation maps a leg in Q to its original leg in C(a,b).
const LEG_PERMUTATIONS = ((1, 2, 3), (3, 1, 2), (2, 3, 1), (2, 1, 3), (3, 2, 1), (1, 3, 2))

struct PolynomialDecomposition
    dimensions::NTuple{3,BigInt}
end

function polynomial_dims(a::Integer, b::Integer)
    a > 0 && b > 0 || throw(ArgumentError("polynomial input lengths must be positive"))
    first, second = BigInt(a), BigInt(b)
    return (first, second, first + second - 1)
end

"""Theorem 3.1, with evaluation and exact interpolation at all `(a+b-1)`-th roots of unity."""
function polynomial_decomposition(a::Integer, b::Integer)
    return PolynomialDecomposition(polynomial_dims(a, b))
end

Base.size(decomposition::PolynomialDecomposition) = decomposition.dimensions
rank_count(decomposition::PolynomialDecomposition) = size(decomposition)[3]

function rank_coefficient(
    decomposition::PolynomialDecomposition, term::Integer, leg::Integer, coordinate::Integer
)
    check_rank_coordinate(decomposition, term, leg, coordinate)
    order = rank_count(decomposition)
    exponent = (BigInt(term) - 1) * (BigInt(coordinate) - 1)
    # The inverse Vandermonde is the conjugate transform divided by its side.
    return leg == 3 ? root_of_unity(order, -exponent) / order :
           root_of_unity(order, exponent)
end

struct SeedDecomposition
    polynomial::PolynomialDecomposition
    copies::BigInt
    dimensions::NTuple{3,BigInt}
    terms::BigInt
end

function seed_dims(a::Integer, b::Integer)
    dimension = prod(polynomial_dims(a, b))^2
    return (dimension, dimension, dimension)
end

"""Rank decomposition of `Q(a,b)⊗m` with the first tensor factor varying fastest."""
function seed_decomposition(a::Integer, b::Integer, m::Integer=1)
    m >= 0 || throw(ArgumentError("the number of seed copies must be nonnegative"))
    polynomial = polynomial_decomposition(a, b)
    copies = BigInt(m)
    dimensions = map(dimension -> dimension^copies, seed_dims(a, b))
    return SeedDecomposition(polynomial, copies, dimensions, rank_count(polynomial)^(6copies))
end

Base.size(decomposition::SeedDecomposition) = decomposition.dimensions
Base.size(decomposition::Union{PolynomialDecomposition,SeedDecomposition}, leg::Integer) =
    size(decomposition)[leg]
rank_count(decomposition::SeedDecomposition) = decomposition.terms

function check_rank_coordinate(decomposition, term, leg, coordinate)
    1 <= leg <= 3 || throw(BoundsError(1:3, leg))
    1 <= term <= rank_count(decomposition) || throw(BoundsError(decomposition, term))
    1 <= coordinate <= size(decomposition)[leg] || throw(BoundsError(decomposition, coordinate))
    return nothing
end

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
        coordinate_index, coordinate_digit = divrem(coordinate_index, size(polynomial)[original_leg])
        local_exponent = term_digit * coordinate_digit
        exponent += original_leg == 3 ? -local_exponent : local_exponent
    end
    # Each leg includes the polynomial output twice per seed copy.
    return root_of_unity(order, exponent) / order^(2decomposition.copies)
end

# The shorter input is fixed to its constant term in each copy of C(a,b).
# Each dot product then shares one digit of the matrix row, inner or column
# index, depending on the leg containing its scalar.
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
            missing_leg = findfirst(==(scalar_leg), permutation)::Int
            remaining, digit = divrem(axis_digits[missing_leg], digit_base)
            axis_digits = Base.setindex(axis_digits, remaining, missing_leg)
            source += stride * digit
        end
        stride *= dimensions[original_leg]
    end
    return source + 1
end

function seed_matrix_selection(a, b, target_dimensions, matrix_coordinate)
    dimensions = polynomial_dims(a, b)
    source_dimensions = seed_dims(a, b)
    scalar_leg = a <= b ? 1 : 2
    digit_base = BigInt(max(a, b))
    matrix_size = digit_base^2
    legs = ntuple(3) do leg
        source_column = function (row)
            return baseline_source_coordinate(
                dimensions, scalar_leg, leg, matrix_size, digit_base, matrix_coordinate(row)
            )
        end
        selection_map(source_dimensions[leg], target_dimensions[leg], source_column)
    end
    return TensorRestriction(legs...)
end

"""Restrict `Q(a,b)` to `M_max(a,b)^2` using Lemmas 3.4 and 3.8."""
function seed_baseline(a::Integer, b::Integer)
    return seed_matrix_selection(a, b, mm_dims(BigInt(max(a, b))^2), identity)
end

"""Restrict `Q(a,b)` to `I₂` for any `(a,b) ≠ (1,1)`."""
function seed_unit(a::Integer, b::Integer)
    matrix_size = BigInt(max(a, b))^2
    matrix_size >= 2 || throw(ArgumentError("a seed of size (1,1) cannot restrict to I₂"))
    return seed_matrix_selection(a, b, unit_dims(2), row -> 1 + (row - 1) * (matrix_size + 1))
end
