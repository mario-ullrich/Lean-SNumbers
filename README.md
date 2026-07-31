# s-Numbers — Lean 4 / Mathlib formalisation

A Lean 4 / Mathlib formalisation of the **Pietsch axiomatic theory of
s-numbers** for bounded linear operators between Banach spaces.

**Repository**: <https://github.com/mario-ullrich/Lean-SNumbers>

**Blueprint**: a human-readable account of the mathematics with links into the
Lean code and a dependency graph, built from `blueprint/` by GitHub Actions on
every push and available as a downloadable artifact under *Actions → latest run
→ blueprint-web* (the PDF is bundled with it).

## What are s-numbers?

**s-numbers are a generalisation of singular values** to bounded 
linear operators `T : X → Y` between arbitrary Banach (or normed) 
spaces, while singular values are only defined for operators 
between Hilbert spaces. 

Following Pietsch's axiomatic approach, an **s-number sequence** is a rule `s` assigning to each operator `T` a
non-increasing sequence of non-negative reals `s₀(T) ≥ s₁(T) ≥ ⋯ ≥ 0`
(indexing starts at `0`) satisfying

* **(S1) norm + monotonicity:** `s₀(T) = ‖T‖` and `s₀(T) ≥ s₁(T) ≥ ⋯ ≥ 0`;
* **(S2) subadditivity:** `sₙ(S + T) ≤ sₙ(S) + ‖T‖`;
* **(S3) ideal property:** `sₙ(B ∘ T ∘ A) ≤ ‖B‖ · sₙ(T) · ‖A‖`;
* **(S4) rank:** `sₙ(T) = 0` whenever `rank T ≤ n`;
* **(S5) norming:** `sₙ(id : ℓ₂ⁿ⁺¹ → ℓ₂ⁿ⁺¹) = 1`.

A *strict* s-number sequence strengthens (S5) to **(S5')**
`sₙ(id_X) = 1` for every space `X` with `dim X > n`, not just `ℓ₂ⁿ⁺¹`.
The classical examples are the **approximation** `aₙ`, **Gelfand** `cₙ`,
**Kolmogorov** `dₙ`, **Bernstein** `bₙ`, and **Hilbert** `hₙ` numbers.

The whole theory is held together by a few inequalities relating these
examples, which are the central targets of this formalisation:

* `aₙ` is the **largest** and `hₙ` the **smallest** s-number, giving the
  sandwich `hₙ(T) ≤ sₙ(T) ≤ aₙ(T)` for every s-number sequence `s`;
* `aₙ(T) ≤ (1 + √n) · min(cₙ(T), dₙ(T))` (Gelfand and Kolmogorov numbers
  cannot both be much smaller than the approximation numbers);
* the **maximal difference theorem**
  `max(cₙ(T), dₙ(T)) ≤ e · (n+1) · hₙ(T)` — hence `≤ e·(n+1)·sₙ(T)` for
  every s-number sequence, in particular the **Mityagin–Henkin conjecture**
  `max(cₙ,dₙ) ≤ e·(n+1)·bₙ` up to the constant `e` (sharp constant
  `(n+1)^{n+1}/nⁿ`);
* **on Hilbert spaces all s-numbers coincide**, `sₙ(T) = aₙ(T)`, and equal
  the classical singular values `σₙ(T)`.

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
│   │                              + finrank (EuclideanSpace 𝕜 (Fin n)) = n
│   ├── PiLpCoordinates.lean    ← generic ℓ^p facts: norm monotonicity, dim ℓ^p_k = k,
│   │                              and the coordinate projection/embedding
│   │                              contractions projFin / padFin (ℓ^p_n ↔ ℓ^p_m)
│   ├── Approximation.lean      ← approximationNumber + (S1)–(S5')
│   │                              + sₙ ≤ aₙ (aₙ is the largest s-number)
│   ├── Bernstein.lean          ← bernsteinNumber  + (S1)–(S5')
│   │                              + bₙ = smallest injective strict s-number
│   ├── Gelfand.lean            ← gelfandNumber    + (S1)–(S5')
│   ├── Kolmogorov.lean         ← kolmogorovNumber + (S1)–(S5')
│   ├── KolmogorovLifting.lean  ← Pietsch identity dₙ S = aₙ(S∘Q_X)
│   │                              (Banach-only variant; SNumbers.Lifting)
│   │                              + kolmogorovNumber_eq_approx: the identity
│   │                              itself, dₙ = aₙ(S∘Q) for the canonical dₙ
│   ├── Hilbert.lean            ← hilbertNumber + (S1)–(S5)
│   ├── Uniqueness.lean         ← sₙ = aₙ on Hilbert spaces (Pietsch 2.11.9),
│   │                              for all bounded operators (ℝ and ℂ), proved
│   ├── Inequalities.lean       ← general-space comparison: hₙ ≤ sₙ,
│   │                              sandwich hₙ ≤ sₙ ≤ aₙ, aₙ ≤ (1+√n)·min(cₙ,dₙ)
│   │                              via Garling–Gordon / Kadets–Snobar (now proved
│   │                              through John), and the determinant
│   │                              ingredients ∏aₖ(T)=‖det T‖ + point selection
│   ├── MaxDifference.lean      ← the maximal difference theorem
│   │                              max(cₙ,dₙ) ≤ e·(n+1)·hₙ (proved), hence
│   │                              ≤ e·(n+1)·sₙ for every s-number sequence and
│   │                              the Mityagin–Henkin conjecture up to `e`;
│   │                              via the determinant quantities Δₖ(S)
│   ├── SingularValuesFinDim.lean ← fin-dim: Mathlib's σₙ coincide with every
│   │                              s-number (sₙ = σₙ) via uniqueness +
│   │                              Eckart–Young (proved)
│   ├── Injectivity.lean        ← injective / surjective s-numbers:
│   │                              cₙ injective, dₙ surjective (full proofs)
│   └── Examples/
│       ├── ExHelpers.lean       ← ingredients shared by the examples: coordinate
│       │                          pigeonhole + (weighted) flatness lemmas behind
│       │                          the Gelfand-width lower bounds, rank of id_{ℓ^p_k}
│       ├── Identity.lean        ← identity id : ℓ^q_m → ℓ^p_m (p ≤ q):
│       │                          ‖id‖ = m^{1/p-1/q}, aₙ = (m-n)^{1/p-1/q}
│       │                          (the unit-diagonal case, self-contained)
│       ├── DiagonalMatrices.lean ← worked example: s-numbers of the diagonal
│       │                          operators, all pairs of exponents.
│       │                          Same exponent D_σ : ℓ^p_m → ℓ^p_m: sₙ = ‖σ_n‖.
│       │                          Mixed p < q: aₙ = (∑_{k≥n}‖σ_k‖^r)^{1/r}
│       │                          (1/r = 1/p - 1/q); q ≤ p (incl p = ∞):
│       │                          ‖D_σ‖ = maxᵢ‖σᵢ‖ and sₙ ≤ ‖σ_n‖
│       └── IdentityL1Linfty.lean ← inclusion I : ℓ₁ → ℓ_∞: ½ ≤ cₙ(I) ≤ 1 and
│                                  hₙ(I) ≥ 1/(n+1) (n+1 in the max-difference thm
│                                  is order-optimal; hₙ ≤ 1/(n+1) still to do)
├── BasicResults.lean           ← library entry point
├── BasicResults/
│   ├── Auerbach.lean           ← Auerbach's lemma (full proof, ℝ-only)
│   ├── SVD.lean                ← compact SVD via singular-value iteration:
│   │                              norm_isSingularValue, `SVD` (Schmidt decomp.),
│   │                              Eckart–Young, diagonal factorisation, and
│   │                              the scalar factorisation `B∘S∘A = c·id`
│   │                              (input to uniqueness) — all proved
│   ├── Determinant.lean        ← det facts: det T* = conj det T, ‖det T‖ = ∏ₖ σₖ
│   │                              (singular values), and det of a diagonal
│   │                              endomorphism = ∏ diagonal entries; ingredient
│   │                              of the maximal difference theorem
│   ├── GarlingGordon.lean      ← Garling–Gordon projection (‖P‖ ≤ √n + ε, ker = M),
│   │                              reduced to `John.exists_projection_ker`
│   ├── KadetsSnobar.lean       ← Kadets–Snobar projection (‖P‖ ≤ √n, range = V),
│   │                              reduced to `John.exists_projection`
│   ├── John.lean               ← John's ellipsoid over any RCLike 𝕜: max-volume
│   │                              position + decomposition of identity
│   │                              `john_decomposition` + Kadets–Snobar
│   │                              `exists_projection` (‖P‖ ≤ √dim) + Garling–Gordon
│   │                              `exists_projection_ker` (‖P‖ ≤ √dim + ε); all proved
│   ├── JohnAux.lean            ← general ingredients (Mathlib candidates): compact
│   │                              convex hulls, seminorm Hahn–Banach, trace duality,
│   │                              ∏(1+aᵢ) ≥ 1−2∑aᵢ²
│   └── Spectral/               ← spectral projection of S*S for any RCLike 𝕜
│                                  (cfc over ℂ + complexification for ℝ); the
│                                  input to s-number uniqueness for bounded ops
├── AddOns.lean                 ← auxiliary library entry point
├── AddOns/
│   ├── Approximable.lean       ← `IsApproximable` (aₙ→0); approximable ⇒ compact
│   └── Compact.lean            ← compact ⇔ approximable on Hilbert
├── LICENSE                     ← Apache 2.0
├── SETUP.md                    ← notes on the GitHub Actions blueprint workflow
├── .github/workflows/          ← CI: builds the project and the blueprint
└── blueprint/
    └── src/
        ├── plastex.cfg         ← plastex / leanblueprint configuration
        ├── extra_styles.css    ← CSS tweaks for the rendered web blueprint
        ├── print.tex           ← pdflatex master (leanblueprint pdf)
        ├── web.tex             ← plastex master (leanblueprint web)
        └── content.tex         ← actual content with \lean / \uses tags
```

## What is formalised

A green check means fully proved (no `sorry`).

### Axioms and framework

| Axiom / Object                            | Status              |
|-------------------------------------------|---------------------|
| `IsSNumberSequence` (S1–S5)               | ✅ defined          |
| `IsStrictSNumberSequence` (adds S5')      | ✅ defined          |
| `rank` of `X →L[𝕜] Y`                     | ✅ defined          |
| Metric injection / surjection classes     | ✅ defined          |
| Homogeneity `sₙ(c•T) = ‖c‖·sₙ(T)`         | ✅ proved           |
| Norm bound `sₙ(T) ≤ ‖T‖` (`IsSNumberSequence.le_norm`) | ✅ proved  |
| Auerbach's lemma                          | ✅ proved (ℝ)       |
| Garling–Gordon projection (`‖P‖ ≤ √n + ε`, ker `P` = `M`) | ✅ proved |
| Kadets–Snobar projection (`‖P‖ ≤ √n`, range `P` = `V`) | ✅ proved |
| John's ellipsoid: max-volume position (`exists_maxVolume`) | ✅ proved |
| Kadets–Snobar via John (`John.exists_projection`, `‖P‖ ≤ √dim`) | ✅ proved |
| John decomposition of identity (`john_decomposition`) | ✅ proved |

### The classical s-numbers

| Object                                    | Status              |
|-------------------------------------------|---------------------|
| Approximation number `aₙ`                 | ✅ proved (S1–S5'); strict |
| Bernstein number `bₙ`                     | ✅ proved (S1–S5'); strict |
| Gelfand number `cₙ`                       | ✅ proved (S1–S5'); strict + injective |
| Kolmogorov number `dₙ`                    | ✅ proved (S1–S5'); strict + surjective |
|       ↳ Pietsch identity `dₙ S = aₙ(S∘Q_X)` (canonical dₙ = lifting form) | ✅ proved (for Banach spaces) |
| Hilbert number `hₙ`                       | ✅ proved (S1)–(S5) |

### Inequalities between s-numbers

| Inequality                                | Status              |
|-------------------------------------------|---------------------|
| Sandwich theorem `hₙ ≤ sₙ ≤ aₙ`         | ✅ proved |
| `bₙ ≤ cₙ` via `bₙ` = smallest injective strict s-number | ✅ proved |
| Hilbert-space uniqueness: `sₙ = aₙ` for all bounded `S` on Hilbert spaces | ✅ proved | 
| `aₙ ≤ (1+√n)·min(cₙ,dₙ)`                  | ✅ proved |
| `max(cₙ,dₙ) ≤ ((n+1)^{n+1}/nⁿ)·hₙ ≤ e·(n+1)·hₙ` (maximal difference thm) | ✅ proved |
| `max(cₙ,dₙ) ≤ e·(n+1)·sₙ` for every s-number sequence, in particular `≤ e·(n+1)·bₙ` (Mityagin–Henkin up to `e`) | ✅ proved |
| factor `n+1` is order-optimal (via example `I : ℓ₁ → ℓ_∞`, see Worked examples) | ⏳ needs `hₙ(I) ≤ 1/(n+1)` |
| Determinant quantities `Δₖ(S)`: growth lemma + `Δₙ₊₁ ≤ hₙ·Δₙ` | ✅ proved |
| `aₙ(B∘S∘A) ≤ ‖B‖‖A‖·hₙ(S)` | ✅ proved |

### Singular values, SVD and determinants

| Result                                    | Status              |
|-------------------------------------------|---------------------|
| `sₙ(S) = σₙ(S)` (fin-dim: all s-numbers = Mathlib singular numbers) | ✅ proved |
| Singular-value uniqueness `project σ = Mathlib σ` (`project_singularValues_eq`) | ✅ proved |
| `norm_isSingularValue` (compact attains norm) | ✅ proved        |
| Compact SVD `IsCompactOperator.SVD` `S = Σ aₖ⟨uₖ,·⟩vₖ` | ✅ proved |
| Eckart–Young `‖S - Sₙ‖ = aₙ(S)`           | ✅ proved |
| Diagonal factorisation `B∘S∘A = diag(aₖ)` (top `n+1` pairs) | ✅ proved |
| Scalar factorisation `B∘S∘A = c·id` (`c < aₙ`, general `S`) | ✅ proved |
| `det T* = conj(det T)` | ✅ proved |
| `‖det T‖ = ∏ₖ σₖ(T)` (singular values) | ✅ proved |
| `∏ aₖ(T) = ‖det T‖` (fin-dim) | ✅ proved |

### Worked examples

| Result                                    | Status              |
|-------------------------------------------|---------------------|
| Diagonal operator `D_σ : ℓ^p_m → ℓ^p_m` and its norm `‖D_σ‖ = ⨆ᵢ‖σᵢ‖` | ✅ proved |
| `sₙ(D_σ) = ‖σ_n‖` for every **strict** s-number (`aₙ, cₙ, dₙ, bₙ`) | ✅ proved |
| Hilbert numbers `hₙ(D_σ) ≤ ‖σ_n‖` (equality fails for `p ≠ 2`) | ✅ proved |
| Unit diagonal = identity, `sₙ(id_{ℓ^p_m}) = 1` for `n < m` | ✅ proved |
| Identity embedding `id : ℓ^q_m → ℓ^p_m` (`p ≤ q`), `‖id‖ = m^{1/p-1/q}` | ✅ proved |
| `aₙ(id : ℓ^q_m → ℓ^p_m) ≤ (m-n)^{1/p-1/q}` (all s-numbers) | ✅ proved |
| `aₙ(id : ℓ^q_m → ℓ^p_m) = (m-n)^{1/p-1/q}` (`p ≤ q`, `n < m`) | ✅ proved |
| Mixed-exponent diagonal `D_σ : ℓ^q_m → ℓ^p_m` (`p < q`), `‖D_σ‖ = ‖σ‖_{ℓ^r}` (`1/r = 1/p-1/q`) | ✅ proved |
| `aₙ(D_σ : ℓ^q_m → ℓ^p_m) = (∑_{k≥n}‖σ_k‖^r)^{1/r}` (`p < q`, `σ` antitone, `n < m`) | ✅ proved |
| `sₙ(D_σ : ℓ^q_m → ℓ^p_m) ≤ (∑_{k≥n}‖σ_k‖^r)^{1/r}` (all s-numbers) | ✅ proved |
| Reverse regime `q ≤ p` (incl. `p = ∞`): `‖D_σ : ℓ^q_m → ℓ^p_m‖ = maxᵢ‖σᵢ‖` | ✅ proved |
| `sₙ(D_σ : ℓ^q_m → ℓ^p_m) ≤ ‖σ_n‖` (all s-numbers, `q ≤ p`, `σ` antitone) | ✅ proved |
| Inclusion `I : ℓ₁ → ℓ_∞`: `½ ≤ cₙ(I) ≤ 1` | ✅ proved |
| Inclusion `I : ℓ₁ → ℓ_∞`: `hₙ(I) ≥ 1/(n+1)` | ✅ proved |
| Inclusion `I : ℓ₁ → ℓ_∞`: `hₙ(I) ≤ 1/(n+1)` (little Grothendieck / Hilbert–Schmidt) | ⏳ missing |

### Add ons

| Result                                    | Status              |
|-------------------------------------------|---------------------|
| Approximable operators (`SVD.IsApproximable`) | ✅ defined; closure properties proved |
| Compact ⇔ approximable on Hilbert         | ✅ proved           |

## Completeness

The whole project builds **`sorry`-free**, so every result listed above is
verified by the Lean kernel.

One note on provenance. The deepest classical ingredient is the **John
decomposition of identity** `John.john_decomposition` in `BasicResults/John.lean`:
in John position, `id = ∑ᵢ cᵢ · ⟨uᵢ,·⟩ uᵢ` over contact points `uᵢ`, with
`cᵢ ≥ 0` and `∑ᵢ cᵢ = k`. Its Lean proof was produced with substantial AI
assistance and the author has not reviewed the proof script line by line; what
guarantees it is the kernel check, not a human reading. The argument it follows
is the classical variational one (Hahn–Banach separation of `k⁻¹·id` from the
compact convex hull of the contact projections, trace duality, the first-order
perturbation `(1−ρ)⁻¹·(id + tH)` against maximality of the determinant, and
Carathéodory). Its general-purpose ingredients live in
`BasicResults/JohnAux.lean` and are future candidates for Mathlib:

* the convex hull of a compact set in a finite-dimensional real normed space is
  compact (`IsCompact.convexHull`);
* Hahn–Banach dominated by a *seminorm* on an inner product space over `RCLike`
  (`Seminorm.exists_inner_le_of_apply`);
* trace duality: every functional on the endomorphisms is `A ↦ tr (A ∘ G)`
  (`ContinuousLinearMap.exists_trace_repr`);
* the product bound `∏(1+aᵢ) ≥ 1 − 2∑aᵢ²` for `∑aᵢ = 0`, `|aᵢ| ≤ 1/2`
  (`one_sub_two_mul_sum_sq_le_prod_one_add`).

The John development (`BasicResults/John.lean`, `BasicResults/JohnAux.lean`) is a
self-contained subtree. It yields the Kadets–Snobar and Garling–Gordon projection
theorems (`John.exists_projection`, `John.exists_projection_ker`), and its sole
consumer is the sharp forward bound `aₙ ≤ (1+√n)·min(cₙ,dₙ)` — the `√n` is exactly
what John's ellipsoid provides (projections exist more cheaply, e.g. from an
Auerbach basis, but with a weaker constant). Nothing else in the project depends
on it.

## Building

Requires [`elan`](https://github.com/leanprover/elan); the Lean version is
pinned in `lean-toolchain` and Mathlib in `lake-manifest.json`, so a clone
builds against exactly the tested revisions:

```bash
lake exe cache get   # downloads the prebuilt Mathlib oleans
lake build           # builds the project
```

## Building the blueprint

The blueprint follows the [leanblueprint](https://github.com/PatrickMassot/leanblueprint)
convention. With `leanblueprint` installed:

```bash
leanblueprint pdf      # produces blueprint/print/blueprint.pdf
leanblueprint web      # produces blueprint/web/index.html
leanblueprint checkdecls   # checks that every \lean{Decl} resolves
```

The workflow at `.github/workflows/blueprint.yml` builds the blueprint on every
push to `main` and uploads `blueprint-web` and `blueprint-pdf` as downloadable
run artifacts.

## License

Apache 2.0 — same as Mathlib. See [LICENSE](LICENSE).

## References

* A. Pietsch, *s-Numbers of operators in Banach spaces*, Studia Math. 51
  (1974), 201–223.
* A. Pietsch, *Eigenvalues and s-numbers*, Cambridge studies in advanced
  mathematics 13, Cambridge University Press, 1987.
* M. Ullrich, *Inequalities between s-numbers*, Advances in Operator Theory **9** (2024), no. 4, article no. 82. <https://doi.org/10.1007/s43036-024-00386-x> (preprint: arXiv:2405.05509).
* M. Ullrich, *On bounds between s-numbers and widths of convex sets*, preprint, 2026 (the maximal difference theorem).
