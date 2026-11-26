using Nemo: Nemo
using NineFourths
using Test

"""
    TestMatrixLike(entries, origin=0)

Wrap a one-based table with read-only, two-dimensional indexed access.

Forward the size and element type of `entries`. Use `origin` as the first
index of each exposed axis to exercise the matrix-like input interface.
"""
struct TestMatrixLike{M}
    entries::M
    origin::Int
end

TestMatrixLike(entries) = TestMatrixLike(entries, 0)
Base.size(matrix::TestMatrixLike) = size(matrix.entries)
Base.eltype(::Type{TestMatrixLike{M}}) where {M} = eltype(M)

"""
    Base.axes(matrix::TestMatrixLike)

Return both axes as identity index ranges starting at the wrapper's origin.
"""
function Base.axes(matrix::TestMatrixLike)
    return map(size(matrix)) do n
        return Base.IdentityUnitRange(matrix.origin:(matrix.origin + n - 1))
    end
end

"""
    Base.getindex(matrix::TestMatrixLike, i, j)

Translate indices on the exposed axes to one-based indices in the wrapped table.
"""
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
