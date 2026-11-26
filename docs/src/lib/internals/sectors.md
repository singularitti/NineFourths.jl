# Polynomial seed and sector maps

Polynomial multiplication supplies a rank decomposition for the initial tensor.
The separation, midpoint, and tripling operations turn that seed into the sector
restrictions used by the finite construction.

## Polynomial seed

```@autodocs
Modules = [NineFourths]
Public = false
Pages = ["src/construction/polynomial.jl"]
```

## Fourier separation

```@autodocs
Modules = [NineFourths]
Public = false
Pages = ["src/construction/separation.jl"]
```

## Midpoint and tripling

```@autodocs
Modules = [NineFourths]
Public = false
Pages = ["src/construction/sectors.jl"]
```
