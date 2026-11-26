# Installation Guide

From the repository root, activate the package environment and install its declared
dependencies with the Julia executable you intend to use.

```sh
julia --project=. -e 'using Pkg; Pkg.instantiate()'
julia --project=.
```

Load NineFourths and check that you can construct a rule.

```jldoctest
julia> using NineFourths

julia> multiplication_scheme() isa BilinearScheme
true
```

To use this checkout from a different Julia project, activate that project and run
`Pkg.develop(path="/path/to/NineFourths")` after importing `Pkg`. Edits to the checkout
will be visible the next time you load the package in a fresh Julia session.

See [Multiplication schemes](@ref) for an executable rule and [Contributing](@ref)
for the package tests and local documentation build.
