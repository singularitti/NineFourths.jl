using Nemo: Nemo
using NineFourths
using Test

# A read-only matrix with scalar indexing and configurable index origins.
struct TestMatrixLike{M}
    entries::M
    origin::Int
end

TestMatrixLike(entries) = TestMatrixLike(entries, 0)
Base.size(matrix::TestMatrixLike) = size(matrix.entries)
Base.eltype(::Type{TestMatrixLike{M}}) where {M} = eltype(M)
function Base.axes(matrix::TestMatrixLike)
    return map(size(matrix)) do n
        return Base.IdentityUnitRange(matrix.origin:(matrix.origin + n - 1))
    end
end

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
