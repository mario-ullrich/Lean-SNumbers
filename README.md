# s-Numbers — Lean 4 / Mathlib formalisation

A Lean 4 / Mathlib formalisation of the **Pietsch axiomatic theory of
s-numbers** for bounded linear operators between Banach spaces.

**Repository** (private): <https://github.com/mario-ullrich/Lean-SNumbers>

**Blueprint**: built by GitHub Actions, available as a downloadable
artifact under *Actions → latest run → blueprint-web*.

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
│   ├── PiLpCoordinates.lean    ← coordinate projection/embedding contractions
│   │                              projFin / padFin between ℓ^p_n and ℓ^p_m
│   ├── Approximation.lean      ← approximationNumber + (S1)–(S5')
│   │                              + sₙ ≤ aₙ (aₙ is the largest s-number)
│   ├── Bernstein.lean          ← bernsteinNumber  + (S1)–(S5')
│   │                              + bₙ = smallest injective strict s-number
│   ├── Gelfand.lean            ← gelfandNumber    + (S1)–(S5')
│   ├── Kolmogorov.lean         ← kolmogorovNumber + (S1)–(S5')
│   ├── KolmogorovLifting.lean  ← Pietsch identity dₙ S = aₙ(S∘Q_X)
│   │                              (Banach-only variant; SNumbers.Lifting)
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
│       ├── DiagonalMatrices.lean ← worked example: s-numbers of a diagonal
│       │                          operator D_σ : ℓ^p_m → ℓ^p_m (sₙ = ‖σ_n‖)
│       └── IdentityEmbedding.lean ← identity id : ℓ^q_m → ℓ^p_m (p ≤ q):
│                                  ‖id‖ = m^{1/p-1/q}, aₙ = (m-n)^{1/p-1/q}
├── BasicResults.lean           ← library entry point
├── BasicResults/
│   ├── Auerbach.lean           ← Auerbach's lemma (full proof, ℝ-only)
│   ├── SVD.lean                ← compact SVD via singular-value iteration:
│   │                              norm_isSingularValue, `SVD` (Schmidt decomp.),
│   │                              Eckart–Young, diagonal factorisation, and
│   │                              the scalar factorisation `B∘S∘A = c·id`
│   │                              (input to uniqueness) — all proved
│   ├── Determinant.lean        ← det facts: det T* = conj det T, and
│   │                              ‖det T‖ = ∏ₖ σₖ (singular values); ingredient
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
│   │                              det from an eigenbasis, ∏(1+aᵢ) ≥ 1−2∑aᵢ²
│   └── Spectral/               ← spectral projection of S*S for any RCLike 𝕜
│                                  (cfc over ℂ + complexification for ℝ); the
│                                  input to s-number uniqueness for bounded ops
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

A green check means fully proved (no `sorry`).

### Axioms and framework

| Axiom / Object                            | Status              |
|-------------------------------------------|---------------------|
| `IsSNumberSequence` (S1–S5)               | ✅ defined          |
| `IsStrictSNumberSequence` (adds S5')      | ✅ defined          |
| `rank` of `X →L[𝕜] Y`                     | ✅ defined          |
| Metric injection / surjection classes     | ✅ defined          |
| Homogeneity `sₙ(c•T) = ‖c‖·sₙ(T)`         | ✅ proved           |
| Auerbach's lemma                          | ✅ proved (ℝ)       |
| Garling–Gordon projection (`‖P‖ ≤ √n + ε`, ker `P` = `M`) | ✅ proved (RCLike, ε-form) |
| Kadets–Snobar projection (`‖P‖ ≤ √n`, range `P` = `V`) | ✅ proved (RCLike) |
| John's ellipsoid: max-volume position (`exists_maxVolume`) | ✅ proved (RCLike) |
| Kadets–Snobar via John (`John.exists_projection`, `‖P‖ ≤ √dim`) | ✅ proved (RCLike) |
| John decomposition of identity (`john_decomposition`) | ✅ proved (RCLike) |

### The classical s-numbers

| Object                                    | Status              |
|-------------------------------------------|---------------------|
| Approximation number `aₙ`                 | ✅ proved (S1–S5'); strict |
| Bernstein number `bₙ`                     | ✅ proved (S1–S5'); strict |
| Gelfand number `cₙ`                       | ✅ proved (S1–S5'); strict + injective |
| Kolmogorov number `dₙ`                    | ✅ proved (S1–S5'); strict + surjective |
|       ↳ alternative definition `dₙ S = aₙ(S∘Q_X)` | ✅ proved (for Banach spaces) |
| Hilbert number `hₙ`                       | ✅ proved (S1)–(S5) |

### Inequalities between s-numbers

| Inequality                                | Status              |
|-------------------------------------------|---------------------|
| Sandwich theorem `hₙ ≤ sₙ ≤ aₙ`         | ✅ proved |
| `bₙ ≤ cₙ` via `bₙ` = smallest injective strict s-number | ✅ proved |
| Hilbert-space uniqueness: `sₙ = aₙ` for all bounded `S` on Hilbert spaces | ✅ proved (over ℝ and ℂ) | 
| `aₙ ≤ (1+√n)·min(cₙ,dₙ)`                  | ✅ proved |
| `max(cₙ,dₙ) ≤ ((n+1)^{n+1}/nⁿ)·hₙ ≤ e·(n+1)·hₙ` (maximal difference thm) | ✅ proved |
| `max(cₙ,dₙ) ≤ e·(n+1)·sₙ` for every s-number sequence, in particular `≤ e·(n+1)·bₙ` (Mityagin–Henkin up to `e`) | ✅ proved |
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

### Add ons

| Result                                    | Status              |
|-------------------------------------------|---------------------|
| Approximable operators (`SVD.IsApproximable`) | ✅ defined; closure properties proved |
| Compact ⇔ approximable on Hilbert         | ✅ proved           |

## Completeness

The whole project builds **`sorry`-free**. The last classical core,
`John.john_decomposition` in `BasicResults/John.lean` — the **John decomposition
of identity**: in John position, `id = ∑ᵢ cᵢ · ⟨uᵢ,·⟩ uᵢ` over contact points
`uᵢ`, with `cᵢ ≥ 0` and `∑ᵢ cᵢ = k` — is proved by the classical variational
argument (Hahn–Banach separation of `k⁻¹·id` from the compact convex hull of the
contact projections, trace duality, the first-order perturbation
`(1−ρ)⁻¹·(id + tH)` against maximality of the determinant, and Carathéodory).
Its general-purpose ingredients live in `BasicResults/JohnAux.lean` and are
candidates for upstreaming to Mathlib:

* the convex hull of a compact set in a finite-dimensional real normed space is
  compact (`IsCompact.convexHull`);
* Hahn–Banach dominated by a *seminorm* on an inner product space over `RCLike`
  (`Seminorm.exists_inner_le_of_apply`);
* trace duality: every functional on the endomorphisms is `A ↦ tr (A ∘ G)`
  (`ContinuousLinearMap.exists_trace_repr`);
* the determinant of an endomorphism diagonal in a basis
  (`LinearMap.det_eq_prod_of_apply_eq_smul`);
* the product bound `∏(1+aᵢ) ≥ 1 − 2∑aᵢ²` for `∑aᵢ = 0`, `|aᵢ| ≤ 1/2`
  (`one_sub_two_mul_sum_sq_le_prod_one_add`).

On top of it sit the Garling–Gordon and Kadets–Snobar projection theorems and
hence `aₙ ≤ (1+√n)·min(cₙ,dₙ)`; independent of it are the maximal difference
theorem `max(cₙ,dₙ) ≤ e·(n+1)·hₙ` (via the determinant quantities `Δₖ`) and the
Gelfand-width lower bound `exists_norm_ratio_ge_idEmbed` (Pietsch [Pie87,
§11.11]) behind the identity embedding's exact approximation numbers, proved by
a flatness / extreme-point argument (an extreme point of the `ℓ^∞`-ball inside
the subspace saturates `≥ dim` coordinates).

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
* M. Ullrich, *On bounds between s-numbers and widths of convex sets*, preprint, 2026 (the maximal difference theorem).
