# Multiplication schemes

A bilinear scheme specifies how to multiply matrices partitioned into `u×u`
blocks. Each of its `r` terms forms a weighted sum of blocks from the left
matrix and a weighted sum from the right. It multiplies those two sums, then
adds a weighted share of that product to each output block.

## Supply coefficient tables

[`BilinearScheme(U, V, W)`](@ref BilinearScheme) expects three tables of shape
`(u^2, r)` with one-based axes. Column `t` gives the weights of term `t`.
Rows use Julia's column-major order, so block `(i, j)` has row number
`i + (j - 1) * u`. The three tables describe the left, right, and output
blocks in that order.

Let `aᵢ`, `bⱼ`, and `cₚ` denote individual blocks of the left input, right
input, and output in that order. The rule computes each output block as

```math
c_p = \sum_{t=1}^{r} W_{pt}
  \left(\sum_{i=1}^{u^2} U_{it} a_i\right)
  \left(\sum_{j=1}^{u^2} V_{jt} b_j\right).
```

For ordinary multiplication of `2×2` blocks, each triple `(i, k, j)` contributes
the product of left block `(i, k)` and right block `(k, j)` to output block
`(i, j)`. This gives eight products. The example builds the corresponding tables,
verifies every input matrix-unit pair, and runs the rule on rectangular inputs.

```jldoctest
julia> using NineFourths

julia> U, V, W = (zeros(Int, 4, 8) for _ in 1:3);

julia> row = LinearIndices((2, 2));

julia> for (t, (i, k, j)) in enumerate(Iterators.product(1:2, 1:2, 1:2))
           U[row[i, k], t] = 1
           V[row[k, j], t] = 1
           W[row[i, j], t] = 1
       end

julia> scheme = BilinearScheme(U, V, W);

julia> verify_scheme(scheme).identity
:exact_coefficients

julia> multiply([1 2 3; 4 5 6], [2 1; 0 2; -1 0], scheme) == [-1 5; 2 14]
true
```

## Select a target exponent

[`multiplication_scheme`](@ref) takes one optional positional argument. For an exact
target `t > 9//4`, the package selects parameters that certify an arithmetic
exponent at most `t`. The default `5//2` is one such finite target. As the
targets approach the infimum `9//4`, the required construction grows.

```jldoctest
julia> using NineFourths

julia> scheme = multiplication_scheme(5//2);

julia> report = verify_scheme(scheme);

julia> (report.valid, report.identity, report.exponent, report.target)
(true, :symbolic_restriction, 2385//1042, 5//2)
```

The result stores instructions for generating coefficients. Indexing
`scheme[term, leg, coordinate]` returns a deferred coefficient, with legs
`1`, `2`, and `3` referring to `U`, `V`, and `W`. The verification report
checks the construction parameters, rank bounds, and exponent inequality
symbolically. Executing even one layer of the default scheme exceeds Julia's
array indexing limit. See [Multiplying matrices](@ref) for the execution
policy.
