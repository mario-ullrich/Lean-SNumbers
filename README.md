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
│   ├── Inequalities.lean       ← general-space comparison: hₙ ≤ sₙ,
│   │                              sandwich hₙ ≤ sₙ ≤ aₙ,
│   │                              aₙ ≤ (1+√n)·min(cₙ,dₙ) via Garling–Gordon
│   │                              / Kadets–Snobar, and the maximal
│   │                              difference thm max(cₙ,dₙ) ≤ (n+1)·(∏hₖ)^{1/(n+1)}
│   │                              (deep inputs left as `sorry`)
│   ├── SingularValuesFinDim.lean ← fin-dim: Mathlib's σₙ coincide with every
│   │                              s-number (sₙ = σₙ) via uniqueness +
│   │                              Eckart–Young; rests on the compact-SVD
│   │                              existence `sorry`
│   └── Injectivity.lean        ← injective / surjective s-numbers:
│                                  cₙ injective, dₙ surjective (full proofs)
├── BasicResults.lean           ← library entry point
├── BasicResults/
│   ├── Auerbach.lean           ← Auerbach's lemma (full proof, ℝ-only)
│   ├── SVD.lean                ← compact SVD via singular-value iteration:
│   │                              norm_isSingularValue (proved), `SVD` (`sorry`),
│   │                              Eckart–Young, diagonal factorisation, and
│   │                              the scalar factorisation `B∘S∘A = c·id`
│   │                              (input to uniqueness)
│   └── Determinant.lean        ← det facts: det T* = conj det T, and
│                                  ‖det T‖ = ∏ₖ σₖ (singular values); ingredient
│                                  of the maximal difference thm
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
| Sandwich theorem `hₙ ≤ sₙ ≤ aₙ`         | ✅ proved (modulo the spectral projection) |
| `aₙ ≤ (1+√n)·min(cₙ,dₙ)`                  | ✅ proved (modulo Garling–Gordon / Kadets–Snobar) |
| Garling–Gordon projection (`‖P‖ ≤ √n`, ker `P` = `M`) | 🟡 declared, no proof |
| Kadets–Snobar projection (`‖P‖ ≤ √n`, range `P` = `V`) | 🟡 declared, no proof |
| `max(cₙ,dₙ) ≤ (n+1)·(∏ₖ₌₀ⁿ hₖ)^{1/(n+1)}` (maximal difference thm) | ✅ proved (modulo the triangular factorisation) |
| Determinant product bound `∏ₖ₌₀ⁿ cₖ ≤ (n+1)ⁿ⁺¹·∏ₖ₌₀ⁿ hₖ` (and `dₖ` analogue) | ✅ proved (modulo the triangular factorisation) |
| Triangular determinant factorisation `∏ cₖ ≤ ‖det(B∘S∘A)‖` (and `dₖ`) | 🟡 declared, no proof |
| `det T* = conj(det T)` | ✅ proved |
| `‖det T‖ = ∏ₖ σₖ(T)` (singular values) | ✅ proved |
| `aₙ(B∘S∘A) ≤ ‖B‖‖A‖·hₙ(S)` | ✅ proved |
| `∏ aₖ(T) = ‖det T‖` (fin-dim) | ✅ proved |
| `sₙ(S) = σₙ(S)` (fin-dim: all s-numbers = Mathlib singular numbers) | ✅ proved (modulo compact-SVD existence) |
| Singular-value uniqueness `project σ = Mathlib σ` (`project_singularValues_eq`) | ✅ proved |
| `IsCompactOperator.SVD` (`OrthonormalOrZero`-indexed) | 🟡 existence is a `sorry` |
| Reverse homogeneity `‖c‖·sₙ(T) ≤ sₙ(c·T)` | ✅ proved           |
| Hilbert-space coincidence `sₙ = aₙ` (2.11.9) | ✅ proved (modulo the spectral projection) |
| Metric injection / surjection classes     | ✅ defined          |
| `sₙ(J∘S) ≤ sₙ(S)`, `sₙ(S∘Q) ≤ sₙ(S)` (any `s`) | ✅ proved        |
| Gelfand numbers `cₙ` **injective**        | ✅ proved           |
| Kolmogorov numbers `dₙ` **surjective**    | ✅ proved           |
| Auerbach's lemma                          | ✅ proved (ℝ)       |
| Approximable operators (`SVD.IsApproximable`) | ✅ defined; closure properties proved |
| `norm_isSingularValue` (compact attains norm) | ✅ proved        |
| Compact SVD `IsCompactOperator.SVD` `S = Σ aₖ⟨uₖ,·⟩vₖ` | 🟡 declared (singular-value iteration)|
| Eckart–Young `‖S - Sₙ‖ = aₙ(S)`           | ✅ proved (modulo `IsCompactOperator.SVD`)|
| Diagonal factorisation `B∘S∘A = diag(aₖ)` (top `n+1` pairs) | ✅ proved (modulo `IsCompactOperator.SVD`)| 
| Scalar factorisation `B∘S∘A = c·id` (`c < aₙ`, general `S`) | ✅ proved (modulo the spectral projection of `S*S`)|
| Compact ⇔ approximable on Hilbert         | 🟡 declared, no proof|

A green check means fully proved (no `sorry`); 🟡 means the statement is
in place but the proof is `sorry`.

### Uniqueness on Hilbert spaces, and injective / surjective `s`-numbers

* **Uniqueness (`SNumbers.Uniqueness`).** On Hilbert spaces every `s`-number
  sequence equals the approximation numbers, `sₙ(S) = aₙ(S)`
  (`allSNumbers_eq_on_HilbertSpace`, Pietsch 2.11.9). It reduces, via the scalar
  factorisation `SVD.exists_scalar_factorisation` (`B∘S∘A = c·id` for `c < aₙ(S)`),
  to the reverse-homogeneity lemma `norm_smul_le_sn`, axiom (S3), axiom (S5), and
  the already-proven upper bound `sn_le_approximationNumber`. That factorisation
  is proved, resting on the spectral projection of `S*S` (the one analytic
  `sorry`, in `BasicResults.Spectral`).
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

The `SNumbers/` library has a small number of clearly-flagged `sorry`s.
Two are in `SNumbers/Inequalities.lean`, classical results of Banach-space
geometry used as inputs to `aₙ ≤ (1+√n)·min(cₙ,dₙ)`:

* **`exists_projection_ker_eq_of_codim_le`** — the **Garling–Gordon**
  theorem (Garling–Gordon 1971; Pietsch [Pie87, 1.7.17]): a closed
  subspace `M ⊆ X` of codimension `≤ n` is the kernel of a bounded
  projection `P` with `‖P‖ ≤ √n`.
* **`exists_projection_range_eq_of_rank_le`** — the **Kadets–Snobar**
  theorem (Kadets–Snobar 1971; Pietsch [Pie87, 1.5.5]): a subspace
  `V ⊆ Y` of dimension `≤ n` is the range of a bounded projection `P`
  with `‖P‖ ≤ √n`.

Two more are in the same file, the **triangular determinant factorisations**
behind the maximal difference theorem:

* **`exists_gelfandNumber_det_factorisation`** /
  **`exists_kolmogorovNumber_det_factorisation`** — the inductive triangular /
  determinant construction of arXiv:2405.05509: factors `A : ℓ₂ⁿ⁺¹ → X`,
  `B : Y → ℓ₂ⁿ⁺¹` with `‖A‖,‖B‖ ≤ √(n+1)` and `∏ cₖ(S) ≤ ‖det(B∘S∘A)‖` (resp.
  `dₖ`). The product bounds `prod_gelfand/kolmogorovNumber_le` and the maximal
  difference theorem are proved on top of these, using the determinant identity
  `∏ aₖ = ‖det‖` (`prod_approximationNumber_eq_norm_det`).

Everything else in `SNumbers/` — including `aₙ ≤ (1+√n)·min(cₙ,dₙ)`, the maximal
difference theorem (modulo the factorisations above), the singular-value
uniqueness `project_singularValues_eq`, and the universality `sₙ = σₙ` (modulo
compact-SVD existence) — is `sorry`-free.

The remaining `sorry`s concern the SVD / spectral theory (to be done elsewhere):

* **`SVD.exists_scalar_factorisation`** (`BasicResults.SVD`) is proved, but
  rests on the **spectral projection** of `S*S`,
  `SpectralRepresentation.exists_spectral_projection` (`BasicResults.Spectral`,
  a `sorry`). This single spectral-theory input is what the Hilbert-space
  coincidence `sₙ = aₙ` (Pietsch 2.11.9) and the sandwich `hₙ ≤ sₙ ≤ aₙ`
  ultimately rest on — the spectral subspace of `S*S` for `[c²,∞)`, for bounded
  positive (non-compact) operators.
* **`SVD.IsCompactOperator.SVD`** — the compact SVD / Schmidt decomposition
  `S = Σ aₖ⟨uₖ,·⟩vₖ`, built on the proved `norm_isSingularValue`. Its
  consequences `…truncation_residual_eq_approxNumber` (Eckart–Young),
  `…diagonalFactorisation`, and `SVD.IsCompactOperator.isApproximable` are
  **not** consumed by the s-number core.
* **compact ⇔ approximable on Hilbert** (`AddOns/Compact.lean`).

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
* M. Ullrich, *Inequalities between s-numbers*, Advances in Operator Theory **9** (2024), no. 4, article no. 82. <https://doi.org/10.1007/s43036-024-00386-x> (preprint: arXiv:2405.05509).
