module NineFourths

using Nemo: Nemo

export BilinearScheme, multiplication_scheme, verify_scheme, multiply

include("coefficients.jl")
include("maps.jl")
include("construction/parameters.jl")
include("construction/derivation.jl")
include("construction/polynomial.jl")
include("construction/separation.jl")
include("construction/sectors.jl")
include("construction/compile.jl")
include("schemes.jl")
include("execution/fields.jl")
include("execution/phase_action.jl")
include("execution/specialization.jl")
include("verification.jl")
include("execution/feasibility.jl")
include("execution/multiply.jl")

end
