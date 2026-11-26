# Scheme representations and verification

An explicit rule stores its coefficient tables. The Shpilka representation stores
a program and can return deferred coefficient queries. Verification reports record
which identity was checked and which exponent bound was obtained.

## Scheme types and coefficient access

```@autodocs
Modules = [NineFourths]
Public = false
Pages = ["src/schemes.jl"]
```

## Verification reports and checks

```@autodocs
Modules = [NineFourths]
Public = false
Pages = ["src/verification.jl"]
```
