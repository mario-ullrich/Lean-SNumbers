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
│   │                              + homogeneity sₙ(c•T)=‖c‖·sₙ(T) (norm_smul_sn)
│   ├── Helpers.lean            ← shared rank facts + norm bounds for the
│   │                              Mathlib quotient CLMs Submodule.mkQL/liftQL
│   ├── Approximation.lean      ← approximationNumber + (S1)–(S5')
│   │                              + sₙ ≤ aₙ (aₙ is the largest s-number)
│   ├── Bernstein.lean          ← bernsteinNumber  + (S1)–(S5')
│   ├── Gelfand.lean            ← gelfandNumber    + (S1)–(S5')
│   ├── Kolmogorov.lean         ← kolmogorovNumber + (S1)–(S5')
│   ├── KolmogorovLifting.lean  ← Pietsch identity dₙ S = aₙ(S∘Q_X)
│   │                              (Banach-only variant; SNumbers.Lifting)
│   ├── Hilbert.lean            ← hilbertNumber + (S1)–(S5)
│   ├── Uniqueness.lean         ← sₙ = aₙ on Hilbert spaces (Pietsch 2.11.9);
│   │                              Hilbert spaces only (from the SVD blackbox)
│   ├── Inequalities.lean       ← general-space comparison: hₙ ≤ sₙ and
│   │                              Pietsch sandwich hₙ ≤ sₙ ≤ aₙ
│   └── Injectivity.lean        ← injective / surjective s-numbers:
│                                  cₙ injective, dₙ surjective (full proofs)
├── BasicResults.lean           ← library entry point
├── BasicResults/
│   ├── Auerbach.lean           ← Auerbach's lemma (full proof, ℝ-only)
│   └── SVD.lean                ← compact SVD via singular-value iteration:
│                                  norm_isSingularValue (proved), `SVD`,
│                                  Eckart–Young, diagonal factorisation, and
│                                  the scalar factorisation `B∘S∘A = c·id`
│                                  (the s-numbers blackbox)
├── AddOns.lean                 ← auxiliary library entry point
├── AddOns/
│   ├── Approximable.lean       ← `IsApproximable` (aₙ→0); approximable ⇒ compact
│   └── Compact.lean            ← compact ⇔ approximable on Hilbert
├── LICENSE                     ← Apache 2.0
├── SETUP.md                    ← notes on the GitHub Actions blueprint workflow
└── blueprint/
    └── src/
        ├── plastex.cfg         ← plastex / leanblueprint configuration
        ├── extra_styles.css    ← CSS tweaks for the rendered web blueprint
        ├── print.tex           ← pdflatex master (leanblueprint pdf)
        ├── web.tex             ← plastex master (leanblueprint web)
        └── content.tex         ← actual content with \lean / \uses tags
```

## What is formalised

| Axiom / Object                            | Status              |
|-------------------------------------------|---------------------|
| `IsSNumberSequence` (S1–S5)               | ✅ defined          |
| `IsStrictSNumberSequence` (adds S5')      | ✅ defined          |
| `rank` of `X →L[𝕜] Y`                     | ✅ defined          |
| Approximation number `aₙ`                 | ✅ proved (S1–S5')  |
| Bernstein number `bₙ`                     | ✅ proved (S1–S5')  |
| Gelfand number `cₙ`                       | ✅ proved (S1–S5')  |
| Kolmogorov number `dₙ`                    | ✅ proved (S1–S5')  |
|       ↳ alternative definition `dₙ S = aₙ(S∘Q_X)` | ✅ proved (for Banach spaces) |
| Hilbert number `hₙ` (any `RCLike 𝕜`)      | ✅ proved (S1)–(S5); forms an s-number sequence |
| Pietsch's sandwich `hₙ ≤ sₙ ≤ aₙ`         | ✅ proved (modulo SVD blackbox) |
| Reverse homogeneity `‖c‖·sₙ(T) ≤ sₙ(c·T)` | ✅ proved           |
| Hilbert-space coincidence `sₙ = aₙ` (2.11.9) | ✅ proved (modulo SVD blackbox) |
| Metric injection / surjection classes     | ✅ defined          |
| `sₙ(J∘S) ≤ sₙ(S)`, `sₙ(S∘Q) ≤ sₙ(S)` (any `s`) | ✅ proved        |
| Gelfand numbers `cₙ` **injective**        | ✅ proved           |
| Kolmogorov numbers `dₙ` **surjective**    | ✅ proved           |
| Auerbach's lemma                          | ✅ proved (ℝ)       |
| Approximable operators (`SVD.IsApproximable`) | ✅ defined; closure properties proved |
| `norm_isSingularValue` (compact attains norm) | ✅ proved        |
| Compact SVD `IsCompactOperator.SVD` `S = Σ aₖ⟨uₖ,·⟩vₖ` | 🟡 declared (singular-value iteration)|
| Eckart–Young `‖S - Sₙ‖ = aₙ(S)`           | 🟡 declared, no proof|
| Diagonal factorisation `B∘S∘A = diag(aₖ)` (top `n+1` pairs) | 🟡 declared, no proof|
| Scalar factorisation `B∘S∘A = c·id` (`c < aₙ`, general `S`) | 🟡 declared, no proof (the SVD blackbox the uniqueness theorem consumes)|
| Compact ⇔ approximable on Hilbert         | 🟡 declared, no proof|

A green check means fully proved (no `sorry`); 🟡 means the statement is
in place but the proof is `sorry`.

### Uniqueness on Hilbert spaces, and injective / surjective `s`-numbers

* **Uniqueness (`SNumbers.Uniqueness`).** On Hilbert spaces every `s`-number
  sequence equals the approximation numbers, `sₙ(S) = aₙ(S)`
  (`allSNumbers_eq_on_HilbertSpace`, Pietsch 2.11.9). This is **fully proved
  on top of one SVD input**: the scalar factorisation
  `SVD.exists_scalar_factorisation` (`B∘S∘A = c·id` for `c < aₙ(S)`,
  itself a `sorry` blackbox in `BasicResults.SVD`). The reduction uses the
  reverse-homogeneity lemma `norm_smul_le_sn`, axiom (S3), axiom (S5), and
  the already-proven upper bound `sn_le_approximationNumber`.
* **Injective / surjective (`SNumbers.Injectivity`).** A sequence is
  *injective* if `sₙ(J∘S) = sₙ(S)` for every metric injection `J`
  (isometric embedding), *surjective* if `sₙ(S∘Q) = sₙ(S)` for every metric
  surjection `Q` (quotient map). The "easy" inequality `≤` holds for every
  `s`-number sequence (`sn_comp_metricInjection_le`,
  `sn_comp_metricSurjection_le`). The two flagship facts are proved in
  full: the **Gelfand numbers are injective** (`injective_gelfandNumber`)
  and the **Kolmogorov numbers are surjective** (`surjective_kolmogorovNumber`),
  because their defining restriction- / quotient-norms are literally
  unchanged under composition with an isometry / metric surjection
  (`‖J∘T‖ = ‖T‖`, `‖T∘Q‖ = ‖T‖`).

The approximation numbers `aₙ` are neither injective nor surjective in
general (their injective and surjective hulls are exactly `cₙ` and `dₙ`).
The Hilbert numbers `hₙ` are both, though that is not yet formalised here.


## Open `sorry`s

The entire `SNumbers/` library is **`sorry`-free**: all five s-number
sequences (`aₙ, bₙ, cₙ, dₙ, hₙ`) are proved to satisfy the Pietsch axioms,
and the uniqueness/sandwich/injectivity results are complete *as
reductions*. Every remaining `sorry` lives on the SVD side.

* **`SVD.exists_scalar_factorisation`** (`BasicResults.SVD`) — *the*
  important one: the Hilbert-space coincidence `sₙ = aₙ` (Pietsch 2.11.9), 
  Pietsch's sandwich `hₙ ≤ sₙ ≤ aₙ`, and the whole comparison story are 
  proved **modulo this one fact** (`B∘S∘A = c·id` for `c < aₙ(S)`, 
  for *any* bounded `S`).
  It needs the spectral theorem for bounded, positive (non-compact) operators, specifically the spectral subspace of `S*S` for `[c²,∞)`.
* `SVD.IsCompactOperator.SVD`, `…truncation_residual_eq_approxNumber`
  (Eckart–Young), `…diagonalFactorisation`, and
  `SVD.IsCompactOperator.isApproximable` (compact ⇒ approximable on Hilbert)
  — the standalone compact-SVD results, built on the *proved*
  `norm_isSingularValue`. These are **not** consumed by the s-number core.

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
