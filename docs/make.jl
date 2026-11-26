using NineFourths
using Documenter

DocMeta.setdocmeta!(NineFourths, :DocTestSetup, :(using NineFourths); recursive=true)

# Documenter's checkdocs catches registered docs missing from the site. Also
# catch package bindings with no docstring registered in the first place.
let docstrings = Base.Docs.meta(NineFourths)
    missing = filter(names(NineFourths; all=true, imported=false)) do name
        # Julia generates eval, include, and hidden names with a leading '#'.
        return name ∉ (:eval, :include) &&
               !startswith(string(name), '#') &&
               !haskey(docstrings, Base.Docs.Binding(NineFourths, name))
    end
    isempty(missing) || error("Missing NineFourths docstrings for ", join(missing, ", "))
end

makedocs(;
    modules=[NineFourths],
    checkdocs=:all,
    doctest=true,
    authors="NineFourths.jl contributors",
    sitename="NineFourths.jl",
    format=Documenter.HTML(;
        canonical="https://singularitti.github.io/NineFourths.jl",
        edit_link="main",
        prettyurls=get(ENV, "CI", "false") == "true",
        mathengine=Documenter.HTMLWriter.MathJax3(),
    ),
    pages=[
        "Home" => "index.md",
        "Manual" => [
            "man/installation.md",
            "man/schemes.md",
            "man/multiplication.md",
            "man/troubleshooting.md",
        ],
        "Reference" => [
            "Public API" => "lib/public.md",
            "Internals" => [
                "lib/internals/algebra.md",
                "lib/internals/derivation.md",
                "lib/internals/sectors.md",
                "lib/internals/compiler.md",
                "lib/internals/schemes.md",
                "lib/internals/fields.md",
                "lib/internals/execution.md",
            ],
        ],
        "Developer Docs" => [
            "developers/contributing.md",
            "developers/style-guide.md",
            "developers/design-principles.md",
        ],
    ],
)

if get(ENV, "GITHUB_ACTIONS", "false") == "true"
    deploydocs(; repo="github.com/singularitti/NineFourths.jl", devbranch="main")
end
