# Contributing

```@contents
Pages = ["contributing.md"]
Depth = 2:3
```

Use the repository's Discussions tab for questions about running NineFourths or
following the construction. Use Issues for reproducible bugs and concrete
feature requests. Discuss changes to the public API or to the proof construction
before spending time on an implementation.

## Report a problem

Include the Julia and NineFourths versions, the relevant call, and the actual
and expected behavior. For `multiplication_scheme`, report the exact target
exponent. For `multiply`, report the dimensions, the scalar field, and any
fallback or resource-limit options. State whether you used Shpilka's construction
or supplied explicit coefficient tables. Remove credentials and identifying
paths from any logs you share.

## Make a change

Work from a local checkout on a branch. Keep each pull request focused on one
change. Follow the [Design Principles](@ref) and [Style Guide](@ref). When a
change affects an argument, callback, result, or error, update the associated
source docstring and any relevant guide. For a behavior change, cover the
affected invariant with a deterministic test in the corresponding `test/` file.

### Run the tests

The commands on this page use Julia 1.14 and run from the repository root.

```sh
julia --project=. -e 'using Pkg; Pkg.test()'
```

The tests exercise derivation entries, coordinate maps, compiled tensor
identities, and execution in several scalar fields. Use these finite identities
when testing changes to the construction. The full default scheme is far too
large to expand on a conventional machine.

### Build the documentation

Documenter reads the Markdown pages in `docs/src/` and the docstrings in `src/`.
The documentation project selects the local checkout via its relative
`[sources]` entry. Instantiate that environment, then build the site.

```sh
julia --project=docs -e 'using Pkg; Pkg.instantiate()'
julia --project=docs docs/make.jl
```

Open `docs/build/index.html` to review the rendered pages and their cross-links.
Run the environment preparation command again when its dependencies change.

## Submit a pull request

Summarize the problem, the change, and the tests you ran. If you changed a proof
step or an index convention, cite the relevant section of the paper and explain
which identity the tests check. Link any issue the pull request addresses.
