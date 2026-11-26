# Troubleshooting

## The requested scheme cannot run

[`multiply`](@ref) raises [`NineFourths.ExecutionInfeasible`](@ref) when a
positive-size product cannot execute one layer within the available index range
or the configured budgets. The error identifies the failed check.

- `max_coefficient_visits` bounds coefficient reads during recursive execution.
- `max_workspace_entries` bounds the number of simultaneously live dense
  entries, including the normalized inputs and result.

Both default to `10_000_000`. Raising a budget can help with an addressable
scheme. The block side of the default Shpilka scheme already exceeds Julia's
index range. Use `fallback=:classical` when a conventional product is acceptable,
or use a smaller explicit rule as in [Multiplication schemes](@ref).

## A coefficient is undefined in the field

A coefficient such as `1//2` requires the image of `2` to be invertible. Over a
field of characteristic two it is zero. For explicit tables, [`verify_scheme`](@ref)
accepts a `field` keyword to check the rule in the intended domain. A strict
product reports [`NineFourths.CoefficientIncompatible`](@ref) for an incompatible
weight. An explicit classical fallback can compute the product using the input
field alone.

## The shape or parent is ambiguous

Check that `size(A, 2) == size(B, 1)` for Julia arrays. A custom container
must provide a two-dimensional `size(M)` and support scalar indexing
`M[i, j]`. Matrices over different runtime parents need a common scalar domain.
An array with no entries may carry only an element type shared by several
parents. Pass `field=F` to provide the identities of the intended field.
