# s-Numbers — Lean 4 / Mathlib formalisation

A Lean 4 / Mathlib formalisation of the **Pietsch axiomatic theory of
s-numbers** for bounded linear operators between Banach spaces.

**Repository** (private): <https://github.com/M-Ull/Lean-SNumbers>

**Blueprint**: built by GitHub Actions, available as a downloadable
artifact under *Actions → latest run → blueprint-web*.

## Layout

```
.
├── lakefile.toml               ← Lake configuration; depends on Mathlib
├── lean-toolchain              ← Lean 4 version
├── SNumbers.lean               ← s-numbers library entry point
├── SNumbers/
│   ├── Basic.lean              ← rank API + Pietsch axioms (S1)–(S5)
│   │                              + IsSNumberSequence / IsStrictSNumberSequence
│   ├── Helpers.lean            ← shared rank facts + ε-limit lemma
│   ├── Approximation.lean      ← approximationNumber + (S1)–(S5')
│   ├── Bernstein.lean          ← bernsteinNumber  (statement only)
│   ├── Gelfand.lean            ← gelfandNumber    (statement only)
│   ├── Kolmogorov.lean         ← kolmogorovNumber + (S1)–(S5')
│   ├── Hilbert.lean            ← hilbertNumber    (statement only)
│   └── Inequalities.lean       ← Pietsch's sandwich theorem
├── BasicResults.lean           ← separate library entry point
├── BasicResults/
│   ├── Auerbach.lean           ← Auerbach's lemma (full proof, ℝ-only)
│   └── SVD.lean                ← compact-operator SVD (blueprint only)
├── LICENSE                     ← Apache 2.0
└── blueprint/
    ├── plastex.cfg             ← leanblueprint configuration
    └── src/
        ├── main.tex            ← pdflatex master
        ├── web.tex             ← leanblueprint web master
        └── content.tex         ← actual content with \lean / \uses tags
```

## What is formalised

| Axiom / Object                            | Status              |
|-------------------------------------------|---------------------|
| `IsSNumberSequence` (S1–S5)               | ✅ defined          |
| `IsStrictSNumberSequence` (adds S5')      | ✅ defined          |
| `rank` of `X →L[𝕜] Y`                     | ✅ defined          |
| Approximation number `aₙ`                 | ✅ defined          |
|   ↳ (S1)–(S5)                             | ✅ proved           |
|   ↳ (S5') strict normalisation            | ✅ proved (Riesz)   |
| Bernstein number `bₙ`                     | 🟡 defined, no proof|
| Gelfand number `cₙ`                       | 🟡 defined, no proof|
| Kolmogorov number `dₙ`                    | ✅ proved (S1–S5')  |
| Hilbert number `hₙ` (real case)           | 🟡 defined, no proof|
| Pietsch's sandwich `hₙ ≤ sₙ ≤ aₙ`         | 🟡 upper proved     |
| Hilbert-space coincidence (`s = a`)       | 🟡 declared, no proof|
| Auerbach's lemma                          | ✅ proved (ℝ)       |
| Compact-operator SVD blueprint            | 🟡 declared, no proof|

A green check means fully proved (no `sorry`); 🟡 means the statement is
in place but the proof is `sorry`.

## Building

```bash
lake update     # fetches Mathlib
lake build      # builds the project
```

## Building the blueprint

The blueprint follows the [leanblueprint](https://github.com/PatrickMassot/leanblueprint)
convention. With `leanblueprint` installed:

```bash
leanblueprint pdf      # produces blueprint/print/blueprint.pdf
leanblueprint web      # produces blueprint/web/index.html
leanblueprint checkdecls   # checks that every \lean{Decl} resolves
```

The simplest way to obtain the rendered blueprint is to push to GitHub:
the workflow at `.github/workflows/blueprint.yml` builds it on every push
and uploads `blueprint-web` and `blueprint-pdf` as artifacts.

## License

Apache 2.0 — same as Mathlib. See [LICENSE](LICENSE).

## References

* A. Pietsch, *s-Numbers of operators in Banach spaces*, Studia Math. 51
  (1974), 201–223.
* A. Pietsch, *Eigenvalues and s-numbers*, Cambridge studies in advanced
  mathematics 13, Cambridge University Press, 1987.
* M. Ullrich, *Inequalities between s-numbers*. <https://doi.org/10.1007/s43036-024-00386-x>
