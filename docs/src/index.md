# NineFourths.jl

```@docs
NineFourths
```

## Start here

- [Installation Guide](@ref) loads a checkout into Julia.
- [Multiplication schemes](@ref) explains the three coefficient tables and builds an
  eight-product rule for a `2×2` block. The same page shows how to inspect the
  automatically selected Shpilka construction.
- [Multiplying matrices](@ref) covers rectangular products, field elements, and the
  choice to allow a conventional product when the requested scheme cannot run.
- [Public API](@ref) lists the exported types and functions. The internal reference
  follows the construction from tensor maps through the rectangular executor.

The same docstrings are available at the Julia prompt. Type `?` to enter help
mode, then look up an exported function such as `multiply` or a qualified
internal name such as `NineFourths.compile_witness`.

## Mathematical sources

The original upper-bound proof describes how tensor restrictions give matrix
multiplication algorithms. [OpenAI, *An Upper Bound of 9/4 for the Matrix
Multiplication Exponent*](https://github.com/openai/math/blob/main/preprints/Matrix-Multiplication-Nine-Fourths-October-2-2026/build/paper.tex).

The package implements the finite construction in Shpilka's exposition. Sections
3–5 develop the polynomial seed and tensor restrictions, §6 assembles the finite
witness, and §7 treats the field of coefficients. [Amir Shpilka, *Exposition of
OpenAI’s Matrix Multiplication in Exponent 9/4 (and an explicit algorithm)*](https://eccc.weizmann.ac.il/report/2026/281/).
