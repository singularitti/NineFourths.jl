using Nemo: Nemo
using NineFourths
using Test

# A read-only wrapper around a one-based, two-dimensional table `entries::M`,
# such as a `Matrix`. Both exposed axes start at `origin::Int`.
struct TestMatrixLike{M}
    entries::M
    origin::Int
end

# Wrap a one-based table with zero-based axes by default.
TestMatrixLike(entries) = TestMatrixLike(entries, 0)
Base.size(matrix::TestMatrixLike) = size(matrix.entries)
Base.eltype(::Type{TestMatrixLike{M}}) where {M} = eltype(M)
# Return the two integer index ranges starting at the wrapper's origin.
function Base.axes(matrix::TestMatrixLike)
    return map(size(matrix)) do n
        return Base.IdentityUnitRange(matrix.origin:(matrix.origin + n - 1))
    end
end

# Translate integer row and column indices on the wrapper's axes and return
# the scalar entry from the wrapped table.
function Base.getindex(matrix::TestMatrixLike, i, j)
    return matrix.entries[i - matrix.origin + 1, j - matrix.origin + 1]
end

@testset "NineFourths.jl" begin
    include("derivation.jl")
    include("maps.jl")
    include("polynomial.jl")
    include("separation.jl")
    include("witness.jl")
    include("field_witness.jl")
    include("construction.jl")
    include("verification.jl")
    include("execution.jl")
    include("generic_execution.jl")
end
