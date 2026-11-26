# Field arithmetic and specialization

The executor infers or accepts a scalar field, specializes roots of unity and
interpolation for that field, and converts the result back to the field of the
inputs.

## Scalar domains

```@autodocs
Modules = [NineFourths]
Public = false
Pages = ["src/execution/fields.jl"]
```

## Roots of unity in the input field

```@autodocs
Modules = [NineFourths]
Public = false
Pages = ["src/execution/phase_action.jl"]
```

## Specializing a witness

```@autodocs
Modules = [NineFourths]
Public = false
Pages = ["src/execution/specialization.jl"]
```
