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
- deploys `blueprint/web` to GitHub Pages, at
  <https://mario-ullrich.github.io/Lean-SNumbers/> with the PDF at
  [`blueprint.pdf`](https://mario-ullrich.github.io/Lean-SNumbers/blueprint.pdf)

The deploy job runs only on `main` and only while the repository is public
(GitHub Pages on the free plan requires a public repository; on a private
repository the job is skipped and the artifacts remain the way to read the
blueprint). The job enables Pages with source "GitHub Actions" automatically
on its first run, so no repository setting needs to be touched.

To read the blueprint without Pages, download `blueprint-web` from a run
summary, unzip it and open `index.html`.

Local reproduction (from the project root, with `leanblueprint` installed):

```bash
lake exe cache get
lake build
leanblueprint pdf          # blueprint/print/print.pdf
leanblueprint web          # blueprint/web/index.html
leanblueprint checkdecls
```
