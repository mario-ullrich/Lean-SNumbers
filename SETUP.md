# Blueprint workflow

This repository uses the GitHub Actions workflow defined in
`.github/workflows/blueprint.yml` to build both the Lean project and the
[leanblueprint](https://github.com/PatrickMassot/leanblueprint) documentation.

The workflow does the following:

- resolves the Lean toolchain from `lean-toolchain`
- runs `lake exe cache get` and `lake build`, so the build uses exactly the
  Mathlib revision pinned in `lake-manifest.json` (it deliberately avoids
  `lake update`, which would re-resolve the dependencies and make CI builds
  non-reproducible)
- builds the blueprint PDF and web site via `leanblueprint`
- checks with `leanblueprint checkdecls` that every `\lean{...}` declaration
  named in the blueprint actually exists in the compiled project
- deploys the web blueprint to GitHub Pages, and additionally uploads
  `blueprint-web` and `blueprint-pdf` as downloadable run artifacts

The published blueprint is at <https://mario-ullrich.github.io/Lean-SNumbers/>.
Pages must be enabled once, under *Settings → Pages → Source: GitHub Actions*.

Local reproduction (from the project root, with `leanblueprint` installed):

```bash
lake exe cache get
lake build
leanblueprint pdf          # blueprint/print/blueprint.pdf
leanblueprint web          # blueprint/web/index.html
leanblueprint checkdecls
```
