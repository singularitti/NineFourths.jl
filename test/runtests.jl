using NineFourths
using Test

@testset "NineFourths.jl" begin
    include("derivation.jl")
    include("maps.jl")
    include("polynomial.jl")
    include("separation.jl")
    include("witness.jl")
    include("construction.jl")
    include("verification.jl")
    include("execution.jl")
end
