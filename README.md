# NineFourths

| **Documentation** | [![Stable](https://img.shields.io/badge/docs-stable-blue.svg)](https://singularitti.github.io/NineFourths.jl/stable/) [![Dev](https://img.shields.io/badge/docs-dev-blue.svg)](https://singularitti.github.io/NineFourths.jl/dev/)                                                                                                                                                                                                                                                                                                 |
| :---------------: | :------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| **Build Status**  | [![Build Status](https://github.com/singularitti/NineFourths.jl/actions/workflows/CI.yml/badge.svg?branch=main)](https://github.com/singularitti/NineFourths.jl/actions/workflows/CI.yml?query=branch%3Amain) [![Build Status](https://ci.appveyor.com/api/projects/status/github/singularitti/NineFourths.jl?svg=true)](https://ci.appveyor.com/project/singularitti/NineFourths-jl)[![Build Status](https://api.cirrus-ci.com/github/singularitti/NineFourths.jl.svg)](https://cirrus-ci.com/github/singularitti/NineFourths.jl) |
|   **Coverage**    | [![Coverage](https://github.com/singularitti/NineFourths.jl/badges/main/coverage.svg)](https://github.com/singularitti/NineFourths.jl/commits/main) [![Coverage](https://codecov.io/gh/singularitti/NineFourths.jl/branch/main/graph/badge.svg)](https://codecov.io/gh/singularitti/NineFourths.jl)                                                                                                                                                                                                                |
|    **Others**     | [![Code Style: Blue](https://img.shields.io/badge/code%20style-blue-4495d1.svg)](https://github.com/invenia/BlueStyle) [![License](https://img.shields.io/github/license/singularitti/NineFourths.jl)](https://github.com/singularitti/NineFourths.jl/blob/main/LICENSE)                                                                                                                                                                                                                                                   |

NineFourths constructs exact bilinear schemes for square matrix multiplication
from OpenAI's upper bound and Shpilka's explicit construction. It accepts integer
and rational matrices and uses exact arithmetic throughout.

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
Coordinates are one-based and follow Julia's column-major order. The paper
scheme stores the finite operations that generate these coefficients. Indexing
it returns a deferred coefficient.

```julia
A = [1 2; 3 4]
B = [1//2 0; 0 1//3]
# Request a paper layer. For the default scheme this raises ExecutionInfeasible.
# multiply(A, B, scheme)

C = multiply(A, B, scheme; fallback=:classical)
# 2×2 Matrix{Rational{BigInt}} with rows [1//2, 2//3] and [3//2, 4//3]
```

`multiply(A, B, scheme)` requires at least one scheme layer. When it cannot run
one, the exception gives the failed resource check. With `fallback=:classical`
the caller permits an ordinary exact matrix product. Integer-only inputs produce
`Matrix{BigInt}`; rational inputs produce `Matrix{Rational{BigInt}}`. Inputs
must be same-size, one-based square matrices. On executable schemes, recursive
layers use implicit zero padding and ordinary exact multiplication at the leaves.

## Construction and verification

For the default target, the proof already needs polynomial length
`a = 2^264` before taking tensor powers. The full target scheme stays symbolic
on this machine. Its verification checks the construction choices, degree and
rank budgets, and the exponent inequality. It relies on the paper's lemmas and
the implementation of the corresponding tensor maps.

For an expanded scheme, `verify_scheme` checks the matrix multiplication identity
on all input matrix units. The test suite also runs the paper's executable
baseline $Q(1,2)$ through the compiler and `multiply`. It exhaustively checks
the 64-term rule for a block of side four and compares an exact product with
Julia's matrix multiplication. A separate check contracts all 64 tensor entries
of a size-two midpoint construction, including preparation and return of its
auxiliary matrix tensor. Run the suite with `import Pkg; Pkg.test()` from the
active project.

| Source | Responsibility |
| --- | --- |
| `src/coefficients.jl`, `src/maps.jl` | Exact scalar arithmetic, sparse tensor restrictions and composition |
| `src/construction/parameters.jl`, `derivation.jl` | Automatic parameter selection and finite derivation |
| `src/construction/polynomial.jl`, `separation.jl`, `sectors.jl` | Polynomial seed, Fourier separation, midpoint and tripling maps |
| `src/construction/compile.jl` | Interpolation, auxiliary tensor preparation and reuse, and final restriction |
| `src/schemes.jl`, `src/verification.jl` | Scheme construction, coefficient access and verification reports |
| `src/execution/` | Resource checks and exact block-recursive multiplication |

The algorithm follows the polynomial construction in §3, the separation and
degeneration maps in §§4–5, and the finite witness and exponent in §6 and
Theorem 1.2 of Shpilka's exposition. [Amir Shpilka, *Exposition of OpenAI’s Matrix Multiplication in Exponent 9/4 (and an explicit algorithm)* (2026)](https://eccc.weizmann.ac.il/report/2026/281/).
The original upper-bound proof gives the underlying tensor restrictions and
their conversion to matrix multiplication algorithms. [OpenAI, original upper-bound paper (2026)](https://github.com/openai/math/blob/main/preprints/Matrix-Multiplication-Nine-Fourths-October-2-2026/build/paper.tex).

## Questions and contributions

You can post usage questions on
[our discussion page](https://github.com/singularitti/NineFourths.jl/discussions).

We welcome contributions, feature requests, and suggestions. If you encounter any problems,
please open an [issue](https://github.com/singularitti/NineFourths.jl/issues).
The [Contributing](@ref) page has
a few guidelines that should be followed when opening pull requests and contributing code.
