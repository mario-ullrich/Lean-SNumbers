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
- uploads `blueprint-web` and `blueprint-pdf` as downloadable run artifacts,
  with the PDF also bundled into the web artifact as `blueprint.pdf`

To read the blueprint, download `blueprint-web` from a run summary, unzip it and
open `index.html`.

Local reproduction (from the project root, with `leanblueprint` installed):

```bash
lake exe cache get
lake build
leanblueprint pdf          # blueprint/print/print.pdf
leanblueprint web          # blueprint/web/index.html
leanblueprint checkdecls
```
