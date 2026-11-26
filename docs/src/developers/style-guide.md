# Style Guide

```@contents
Pages = ["style-guide.md"]
Depth = 2:3
```

Follow the conventions of the surrounding Julia code. NineFourths adopts
BlueStyle and uses the repository's `.JuliaFormatter.toml` for formatting.
[BlueStyle](https://github.com/JuliaDiff/BlueStyle).

## Formatting

Use JuliaFormatter on the Julia files you change. If JuliaFormatter is
available in your tooling environment, you can run it from the repository
root. Adjust the paths to match your changes. Keep unrelated formatting changes
in a separate pull request.

```julia
using JuliaFormatter: format
format("src")
format("test")
```

## Julia interfaces

Use descriptive names for dimensions, indices, and coefficients. Give a
mutating operation a `!` suffix when it changes an argument. Add an argument
type annotation when it selects a method or expresses a requirement, such as
an integer tensor power. For generic code, describe the operations the
argument must supply.

State whether indices are one-based and which coordinate varies fastest when
packing several indices. Keep exact quantities as integers, rationals, or the
appropriate field elements. Use `BigInt` for construction dimensions and
bounds that can exceed a machine integer.

## Docstrings

Document public and internal functions, types, and constants with native Julia
docstrings. Start with the signature or binding on an indented line. Follow
it with one sentence describing the operation or representation. Add the
argument roles, relevant Julia types or required operations, returned values,
and validation rules that the reader needs. For an implementation of a proof
step, identify the relevant lemma, claim, or equation and explain its role in
the computation. [Julia documentation conventions](https://docs.julialang.org/en/v1/manual/documentation/).

List related method signatures together when one explanation covers them.
Give a method its own docstring when its behavior needs a separate explanation.
Document an extension of a `Base` function on the NineFourths method.

For a locally scoped callback, explain its contract in the enclosing docstring
and place a short comment next to its definition. For example, describe
whether a callback receives a source or target index and whether it returns a
selection, a single coefficient, or several contributions to a row.

Use `jldoctest` for examples with stable expected output and a short runtime.
Put package setup commands in ordinary code fences so a documentation build
can use its prepared environment.
See [Contributing](@ref) for the build commands.
