# Rectangular execution

The planner checks index ranges, coefficient visits, and live workspace before
the executor forms padded blocks. The multiplication routines combine each term
in its coefficient domain and accumulate the output blocks.

## Dimensions and resource estimates

```@autodocs
Modules = [NineFourths]
Public = false
Pages = ["src/execution/feasibility.jl"]
```

## Block recursion and accumulation

```@autodocs
Modules = [NineFourths]
Public = false
Pages = ["src/execution/multiply.jl"]
```
