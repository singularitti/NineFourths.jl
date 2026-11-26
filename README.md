# NineFourths

| **Documentation** | [![Stable](https://img.shields.io/badge/docs-stable-blue.svg)](https://singularitti.github.io/NineFourths.jl/stable/) [![Dev](https://img.shields.io/badge/docs-dev-blue.svg)](https://singularitti.github.io/NineFourths.jl/dev/)                                                                                                                                                                                                                                                                                                 |
| :---------------: | :------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| **Build Status**  | [![Build Status](https://github.com/singularitti/NineFourths.jl/actions/workflows/CI.yml/badge.svg?branch=main)](https://github.com/singularitti/NineFourths.jl/actions/workflows/CI.yml?query=branch%3Amain) [![Build Status](https://ci.appveyor.com/api/projects/status/github/singularitti/NineFourths.jl?svg=true)](https://ci.appveyor.com/project/singularitti/NineFourths-jl)[![Build Status](https://api.cirrus-ci.com/github/singularitti/NineFourths.jl.svg)](https://cirrus-ci.com/github/singularitti/NineFourths.jl) |
|   **Coverage**    | [![Coverage](https://github.com/singularitti/NineFourths.jl/badges/main/coverage.svg)](https://github.com/singularitti/NineFourths.jl/commits/main) [![Coverage](https://codecov.io/gh/singularitti/NineFourths.jl/branch/main/graph/badge.svg)](https://codecov.io/gh/singularitti/NineFourths.jl)                                                                                                                                                                                                                |
|    **Others**     | [![Code Style: Blue](https://img.shields.io/badge/code%20style-blue-4495d1.svg)](https://github.com/JuliaDiff/BlueStyle) [![License](https://img.shields.io/github/license/singularitti/NineFourths.jl)](https://github.com/singularitti/NineFourths.jl/blob/main/LICENSE)                                                                                                                                                                                                                                                 |

NineFourths implements Amir Shpilka's explicit construction of bilinear schemes
for square matrix multiplication with target exponents above OpenAI's `9//4`
upper bound. Its executor multiplies compatible rectangular matrices over a
common scalar field, including finite fields and user-defined fields.

This repository is created and maintained by
[@singularitti](https://github.com/singularitti), and contributions are highly welcome.

## Using the package

From the repository root, start the installed Julia 1.14 with `julia --project=.`.
Install the project dependencies once with `import Pkg; Pkg.instantiate()`.

```julia
using NineFourths

scheme = multiplication_scheme()             # default target 5//2
closer = multiplication_scheme(23//10)        # one optional positional argument
report = verify_scheme(scheme)
report.identity                              # :symbolic_restriction
report.exponent                              # 2385//1042, a certified upper bound
scheme[1, 2, 1]                               # term 1, right input, coordinate 1
```

The matrix multiplication exponent is an infimum. For a target `t > 9//4`,
the package chooses a finite construction with certified arithmetic exponent at
most `t`. Use an exact integer or rational for `t`. The default `5//2` asks for
an $O(n^{5/2})$ algorithm. Moving the target closer to `9//4` increases the
construction parameters. The endpoint itself has no finite parameter choice in
this construction.

A scheme specifies three coefficient maps for a block of side `u`. For each
term it forms one linear combination of the left blocks and one of the right
blocks, multiplies them, then weights that product into each output block.
Scheme coordinates are one-based and follow Julia's column-major order.
To use coefficient tables of your own, pass them to `BilinearScheme(U, V, W)`.
The `NineFourths.ShpilkaScheme` returned by `multiplication_scheme` stores the
operations that generate its coefficients. Indexing it returns a deferred
`NineFourths.ShpilkaCoefficient`.

```julia
import Nemo
F = Nemo.GF(5)
A = F.([1 2 3; 4 0 1])
B = reshape(F.([1, 2, 3]), 3, 1)

C = multiply(A, B, scheme; fallback=:classical)
@assert C == reshape(F.([4, 2]), 2, 1)
```

`multiply(A, B, scheme)` accepts `m×k` and `k×n` inputs and returns a dense
Julia `m×n` matrix. For positive dimensions it requires at least one scheme
layer. Each recursion level pads the three dimensions independently and uses
ordinary multiplication at the leaves. If the requested layer exceeds a
resource limit or an explicit rule has an undefined coefficient in the input
field, the default raises an exception. `fallback=:classical` permits an
ordinary product in the same field. In the example, the default Shpilka scheme
exceeds the index limit, so this explicit fallback computes the result.

The executor accepts Julia `AbstractMatrix` containers and Nemo matrices.
The two inputs must share a field or admit a common scalar representation.
Native field elements retain their arithmetic and parent. Supported examples
include Nemo prime fields, finite extensions, algebraic number fields and
custom scalar types outside `Number`.
A custom field supplies addition, subtraction, multiplication, equality,
additive and multiplicative identities, and inversion or division for
fractional coefficients. When one scalar type represents several fields,
`parent(x)` lets the executor check that the elements share a parent.
Built-in Julia integers and rationals retain exact
arithmetic with `BigInt` and `Rational{BigInt}` results. Floating-point
inputs use their native rounding.

When any dimension is zero, the shape determines the empty or zero product.
A nonempty `m×0` by `0×n` result needs the field's additive identity. If the
arrays carry the element type alone and that type has multiple possible
parents, use `multiply(A, B, scheme; field=F)`. A callable parent, scalar
type with identities, or representative field element can supply the domain.

## Construction and verification

For the default target, the proof already needs polynomial length
`a = 2^264` before taking tensor powers. The full target scheme stays symbolic
on this machine. Its verification checks the construction choices, degree and
rank budgets, and the exponent inequality. It relies on Shpilka's lemmas and
the implementation of the corresponding tensor maps.

For explicit tables, `verify_scheme` checks the matrix multiplication identity
on all input matrix units in their common exact field. A callable field parent
can also be supplied as `verify_scheme(scheme; field=F)`. The test suite runs
Shpilka's baseline $Q(1,2)$ through the compiler and `multiply`. It exhaustively
checks the 64-term rule for a block of side four and compares an exact product
with Julia's matrix multiplication. A separate check contracts all 64 tensor entries
of a size-two midpoint construction, including preparation and return of its
auxiliary matrix tensor. Finite-field execution selects Fourier orders
invertible in the input field, performs interpolation with roots of unity, and
projects temporary cyclotomic expressions back into that field. The suite
also checks rectangular products computed with the compiled baseline in small
characteristics against independent products. Run it with `import Pkg; Pkg.test()`
from the active project.

| Source | Responsibility |
| --- | --- |
| `src/coefficients.jl`, `src/maps.jl` | Exact scalar arithmetic, sparse tensor restrictions and composition |
| `src/construction/parameters.jl`, `derivation.jl` | Shpilka's parameter choices and finite derivation |
| `src/construction/polynomial.jl`, `separation.jl`, `sectors.jl` | Polynomial seed, Fourier separation, midpoint and tripling maps |
| `src/construction/compile.jl` | Interpolation, auxiliary tensor preparation and reuse, and final restriction |
| `src/schemes.jl`, `src/verification.jl` | Scheme construction, coefficient access and verification reports |
| `src/execution/` | Field arithmetic and specialization, resource checks, rectangular block recursion |

The algorithm follows the polynomial construction in §3, the separation and
degeneration maps in §§4–5, and the finite witness and exponent in §6 and
Theorem 1.2 of Shpilka's exposition. Section 7 gives the field-dependent
separation and descent argument. [Amir Shpilka, *Exposition of OpenAI’s Matrix Multiplication in Exponent 9/4 (and an explicit algorithm)* (2026)](https://eccc.weizmann.ac.il/report/2026/281/).
The original upper-bound proof gives the underlying tensor restrictions and
their conversion to matrix multiplication algorithms. [OpenAI, *An Upper Bound of 9/4 for the Matrix Multiplication Exponent* (2026)](https://github.com/openai/math/blob/main/preprints/Matrix-Multiplication-Nine-Fourths-October-2-2026/build/paper.tex).

## Questions and contributions

You can post usage questions on
[our discussion page](https://github.com/singularitti/NineFourths.jl/discussions).

We welcome contributions, feature requests, and suggestions. If you encounter any problems,
please open an [issue](https://github.com/singularitti/NineFourths.jl/issues).
The [Contributing](@ref) page has
a few guidelines that should be followed when opening pull requests and contributing code.
