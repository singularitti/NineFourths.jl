# Design Principles

```@contents
Pages = ["design-principles.md"]
Depth = 2:2
```

NineFourths turns the proof of a matrix multiplication exponent bound into a
finite bilinear scheme. Its main responsibility is to preserve the tensor
identities from the derivation through coefficient access and execution.

## Follow the construction

`src/construction/parameters.jl` and `derivation.jl` choose the exact parameters
and record the baseline, restriction, symmetry, midpoint, and tripling steps.
`polynomial.jl`, `separation.jl`, and `sectors.jl` implement the polynomial seed
and the substitutions for individual steps. `compile.jl` composes those steps,
interpolates the degenerations, and prepares and reuses the auxiliary tensors.
Use the lemma, claim, or equation number to explain the origin of a formula.
[Shpilka's exposition, §§3–7](https://eccc.weizmann.ac.il/report/2026/281/).

The constructed scheme stores operations and exact parameters. Indexing a
Shpilka scheme gives a deferred coefficient. Keep powers and dimensions
symbolic when expanding them would dominate the work.

## Preserve the coordinate conventions

In `src/maps.jl`, a leg map has source columns and target rows. The column for
one source variable gives its substitution into the target variables. A sparse
row callback may emit several contributions to the same source column. Their
sum must equal the corresponding indexed coefficient.

Tensor products pack the first factor fastest. Matrix coordinates use Julia's
one-based column-major order. When changing a permutation, restriction, or
packing rule, check that each map's target coordinates match the next map's
source coordinates.

## Keep arithmetic in the input field

The executor reads the operands' scalar field and returns a dense Julia matrix
whose elements use that field. Julia integer and rational inputs use unbounded
exact arithmetic. Custom scalars can obtain their identities from a field
parent and need only the scalar operations used by the calculation. The
executor also accepts matrix containers with compatible dimensions, axes, and
scalar indexing.

Fourier separation and interpolation use orders that are invertible in the
chosen field. Temporary cyclotomic expressions carry base-field weights.
Project to the base field after assembling the product. A change to coefficient
embedding or projection should preserve both the multiplication identity and
the element type and parent of the result.

## Verify identities and enforce execution limits

Verification of a Shpilka scheme checks the symbolic construction and its
exponent bound. Verification of explicit coefficient tables checks their action
on pairs of matrix units. Tests also contract a compiled midpoint restriction
and exercise the compiled polynomial baseline over finite fields. These checks
cover tensor identities that an exponent calculation alone cannot establish.

The execution planner checks index bounds, coefficient visits, and dense
workspace before applying a scheme layer. Execution pads the row, inner, and
column dimensions independently. A classical product is available when the
caller explicitly chooses `fallback=:classical`.

See [Contributing](@ref) for the test and documentation commands and
[Style Guide](@ref) for docstring conventions.
