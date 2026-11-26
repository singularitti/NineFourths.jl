# Witness compiler

The compiler assembles restrictions, extracts coefficients by interpolation,
and handles the auxiliary matrix tensor. Coefficients can be evaluated from this
representation without storing dense tables for the full witness.

```@autodocs
Modules = [NineFourths]
Public = false
Pages = ["src/construction/compile.jl"]
```
