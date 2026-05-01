# Blueprint workflow

This repository uses the GitHub Actions workflow defined in
`.github/workflows/blueprint.yml` to build both the Lean project and the
leanblueprint documentation.

The workflow does the following:

- resolves the Lean toolchain from `lean-toolchain`
- runs `lake update` and `lake build`
- builds the blueprint PDF and web site via `leanblueprint`
- uploads `blueprint-web` and `blueprint-pdf` as workflow artifacts

Local reproduction (from the project root):

```bash
lake update
lake build
leanblueprint web
```

The workflow is intended for private repositories, so the generated web
blueprint is made available as a downloadable artifact rather than a
public GitHub Pages site.
