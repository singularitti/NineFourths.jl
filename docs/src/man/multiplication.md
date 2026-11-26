# Multiplying matrices

[`multiply(A, B, scheme)`](@ref multiply) accepts an `m×k` matrix and a `k×n`
matrix and returns a dense Julia `m×n` matrix. With positive dimensions the
default requires a scheme layer. The executor pads each dimension independently
as it forms blocks. It also accepts inputs such as Nemo matrices and custom
containers that supply two dimensions and scalar indexing.

## Field arithmetic

Built-in integer inputs produce `BigInt` entries. Built-in rational inputs,
including mixtures with built-in integers, produce `Rational{BigInt}` entries.
Elements of a common finite field, number field, or user-defined field use that
field's arithmetic. The following product uses the explicit scalar rule and
reduces its entries modulo five.

```jldoctest
julia> using NineFourths

julia> import Nemo

julia> F = Nemo.GF(5);

julia> A = F.([1 2 3; 4 0 1]); B = reshape(F.([1, 2, 3]), 3, 1);

julia> rule = BilinearScheme([1;;], [1;;], [1;;]);

julia> C = multiply(A, B, rule);

julia> C == reshape(F.([4, 2]), 2, 1) && parent(C[1, 1]) === F
true
```

Custom elements supply addition, subtraction, multiplication, equality, zero
and one. Coefficients with denominators also need inversion or division in the
field. When several fields share an element type, a `parent(x)` method lets
the executor distinguish them. Supply `field=F` to choose the domain explicitly.
For instance, an `m×0` by `0×n` product with positive `m` and `n` needs the
additive identity even when both inputs have no entries.

## Permit a classical fallback

The default `fallback=:error` reports the reason when a scheme cannot run.
Passing `fallback=:classical` allows ordinary multiplication in the same field
when a scheme layer exceeds the execution limits or a coefficient cannot act in
that field. The workspace limit also applies to the fallback.

```jldoctest
julia> using NineFourths

julia> scheme = multiplication_scheme();

julia> A = [1//2 1//3]; B = reshape([6, 3], 2, 1);

julia> only(multiply(A, B, scheme; fallback=:classical))
4//1
```

The default scheme exceeds the indexing limit, so this example uses the
classical path. See [Troubleshooting](@ref) for the resource limits and error types.
