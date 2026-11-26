using NineFourths
using Test

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
