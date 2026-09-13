# s-Numbers in Lean 4 / Mathlib

A Lean 4 / Mathlib formalisation of the **Pietsch axiomatic theory of s-numbers**
for bounded linear operators between Banach spaces: the five classical s-number
sequences, the inequalities between them, the singular value decomposition of
compact operators on Hilbert spaces, John's ellipsoid, and entropy numbers. The
project builds without `sorry`, and every theorem uses only the three axioms
Mathlib relies on throughout (`propext`, `Classical.choice`, `Quot.sound`).

* **Blueprint** (the mathematics, with the Lean name at every statement):
  <https://mario-ullrich.github.io/Lean-SNumbers/>
* **Blueprint as PDF**: <https://mario-ullrich.github.io/Lean-SNumbers/blueprint.pdf>
* **Dependency graph**:
  <https://mario-ullrich.github.io/Lean-SNumbers/dep_graph_document.html>
* **Palomar registry**: the maximal difference theorem is registered as
  [PALOMAR-2026-09-07-000008](https://palomar-registry.org/entry?id=PALOMAR-2026-09-07-000008&version=1).
  The registry re-ran the proof at commit
  [`085b299`](https://github.com/mario-ullrich/Lean-SNumbers/tree/085b29905f46bc4e61e19be642699153bdb99c2d)
  against Lean `v4.33.0` and Mathlib `db584cd`, and verified the declarations
  `SNumbers.approximationNumber_le_mul_hilbertNumber` and
  `SNumbers.approximationNumber_le_e_mul_hilbertNumber`.

## What are s-numbers?

**s-numbers are a generalisation of singular values** to bounded linear operators
`T : X → Y` between arbitrary Banach (or normed) spaces, while singular values are
only defined for operators between Hilbert spaces.

Following Pietsch's axiomatic approach, an **s-number sequence** is a rule `s`
assigning to each operator `T` a non-increasing sequence of non-negative reals
`s₀(T) ≥ s₁(T) ≥ ⋯ ≥ 0` (indexing starts at `0`) satisfying

* **(S1) norm + monotonicity:** `s₀(T) = ‖T‖` and `s₀(T) ≥ s₁(T) ≥ ⋯ ≥ 0`;
* **(S2) subadditivity:** `sₙ(S + T) ≤ sₙ(S) + ‖T‖`;
* **(S3) ideal property:** `sₙ(B ∘ T ∘ A) ≤ ‖B‖ · sₙ(T) · ‖A‖`;
* **(S4) rank:** `sₙ(T) = 0` whenever `rank T ≤ n`;
* **(S5) norming:** `sₙ(id : ℓ₂ⁿ⁺¹ → ℓ₂ⁿ⁺¹) = 1`.

A *strict* s-number sequence strengthens (S5) to **(S5')** `sₙ(id_X) = 1` for
every space `X` with `dim X > n`, not just `ℓ₂ⁿ⁺¹`. The classical examples are
the **approximation** `aₙ`, **Gelfand** `cₙ`, **Kolmogorov** `dₙ`, **Bernstein**
`bₙ`, and **Hilbert** `hₙ` numbers. In Lean, `SNumbers.IsSNumberSequence` and
`SNumbers.IsStrictSNumberSequence` state the axioms, and each classical example
is proved to satisfy them.

## Main results

Throughout, `T : X → Y` is a bounded operator between normed spaces over `ℝ` or
`ℂ`, and `s`, `t` are s-number sequences.

* **Sandwich theorem.** `hₙ(T) ≤ sₙ(T) ≤ aₙ(T)`: the Hilbert numbers are the
  smallest and the approximation numbers the largest s-numbers
  (`SNumbers.hilbertNumber_le_sn_le_approximationNumber`).
* **Uniqueness on Hilbert spaces.** If `X` and `Y` are Hilbert spaces, then
  `sₙ(T) = aₙ(T)` for every s-number sequence `s` and every bounded `T`
  (`SNumbers.allSNumbers_eq_on_HilbertSpace`). In finite dimension these are
  Mathlib's singular values, `sₙ(T) = σₙ(T)`
  (`SNumbers.sn_eq_singularValues_of_finiteDimensional`).
* **Gelfand and Kolmogorov numbers against approximation numbers.** The classical
  bound `aₙ(T) ≤ (1 + √n) · min(cₙ(T), dₙ(T))`, via the Kadets–Snobar and
  Garling–Gordon projection theorems
  (`SNumbers.approximationNumber_le_sqrt_mul_min`).
* **Maximal difference theorem.**
  `aₙ(T) ≤ ((n+1)^{n+1} / nⁿ) · hₙ(T) ≤ e · (n+1) · hₙ(T)`
  (`SNumbers.approximationNumber_le_mul_hilbertNumber`,
  `SNumbers.approximationNumber_le_e_mul_hilbertNumber`). Hence
  `sₙ(T) ≤ e · (n+1) · tₙ(T)` for any two s-number sequences `s`, `t`
  (`SNumbers.sn_le_e_mul_tn`), which solves the Mityagin–Henkin conjecture up to
  the constant `e`, i.e., `dₙ(T) ≤ e · (n+1) · bₙ(T)`
  (`SNumbers.max_gelfandNumber_kolmogorovNumber_le_e_mul_bernsteinNumber`).
* **The factor `n+1` is order-optimal.** For the inclusion `I : ℓ₁ → ℓ_∞`,
  `hₙ(I) = 1/(n+1)` and `((n+1)/2) · hₙ(I) ≤ cₙ(I)`
  (`SNumbers.L1Linf.hilbertNumber_eq_one_div`,
  `SNumbers.L1Linf.mul_hilbertNumber_le_gelfandNumber`).
* **Schmidt representation.** A compact operator `S : H₁ → H₂` between Hilbert
  spaces is `S = ∑ₖ σₖ · ⟨uₖ, ·⟩ vₖ` with `σₖ = aₖ(S)` decreasing to `0` and
  orthonormal systems `(uₖ)`, `(vₖ)` (`SVD.IsCompactOperator.SVD`).
* **John's ellipsoid.** In John position, `id = ∑ᵢ cᵢ · ⟨uᵢ, ·⟩ uᵢ` over contact
  points `uᵢ` with `cᵢ ≥ 0` and `∑ᵢ cᵢ = dim` (`John.john_decomposition`). Hence
  the Kadets–Snobar theorem: every `n`-dimensional subspace of a normed space is
  the range of a projection `P` with `‖P‖ ≤ √n` (`John.exists_projection`).
* **Entropy numbers.** `max(cₙ(S), dₙ(S)) ≤ (n+1) · eₙ(S)`
  (`SNumbers.max_gelfandNumber_kolmogorovNumber_le_succ_mul_entropyNumber`), and
  for complete `Y` the operator `S` is compact if and only if `eₙ(S) → 0`
  (`SNumbers.isCompactOperator_iff_tendsto_entropyNumber`).

Everything else, including the s-numbers of diagonal operators between `ℓ^p_m`
spaces and the characterisations of compactness by `cₙ`, `dₙ` and, on Hilbert
spaces, by every s-number sequence, is in the blueprint with its Lean name at
every statement.

## Organisation

Three libraries. `SNumbers` holds the theory: the axioms, the five classical
sequences, the inequalities between them, entropy numbers, and the examples.
`BasicResults` holds general functional analysis the theory consumes and Mathlib
lacks: the SVD of compact operators, determinant identities, John's ellipsoid,
Auerbach's lemma, and a spectral toolkit; [MathlibCandidates.md](MathlibCandidates.md)
lists what could be upstreamed. `AddOns` measures compactness by s-numbers.

`PalomarChallenges` and `PalomarSolutions` are the submission surfaces for the
Palomar registry: a Challenge states the registered theorems with Mathlib imports
only, and a Solution proves them from the development. Both sit outside
`defaultTargets`; build them with `lake build PalomarChallenges PalomarSolutions`.

## Building

Requires [`elan`](https://github.com/leanprover/elan). The Lean version is pinned
in `lean-toolchain` and Mathlib in `lake-manifest.json`, so a clone builds against
Lean / Mathlib `v4.33.0`:

```bash
lake exe cache get   # downloads the prebuilt Mathlib oleans
lake build           # builds the project
```

The blueprint follows the
[leanblueprint](https://github.com/PatrickMassot/leanblueprint) convention. With
`leanblueprint` installed:

```bash
leanblueprint pdf          # blueprint/print/print.pdf
leanblueprint web          # blueprint/web/index.html and the dependency graph
leanblueprint checkdecls   # checks that every \lean{Decl} resolves
```

GitHub Actions builds the project and the blueprint on every push to `main` and
deploys the blueprint to GitHub Pages.

## AI assistance

This project started out written by hand, and as it grew I used AI assistance
more and more. By now, most of the Lean proofs were produced this way. What I did
throughout: design the structure of the development, and check and revise the
statements of all definitions and results. The proofs themselves are guaranteed
by the Lean kernel. The proof script of the John decomposition
(`John.john_decomposition`) I have not reviewed line by line; it follows the
classical variational argument and is checked by the kernel like everything else.

## License

Apache 2.0, the same as Mathlib. See [LICENSE](LICENSE).

## References

* A. Pietsch, *s-Numbers of operators in Banach spaces*, Studia Math. 51
  (1974), 201–223.
* A. Pietsch, *Operator ideals*, North-Holland Mathematical Library 20,
  North-Holland, 1980.
* A. Pietsch, *Eigenvalues and s-numbers*, Cambridge Studies in Advanced
  Mathematics 13, Cambridge University Press, 1987.
* M. Ullrich, *Inequalities between s-numbers*, Advances in Operator Theory **9**
  (2024), no. 4, article no. 82. <https://doi.org/10.1007/s43036-024-00386-x>
  (preprint: arXiv:2405.05509). A simple proof and a slight improvement of
  Pietsch's bound `max(cₙ, dₙ) ≤ (n+1) · (h₀ ⋯ hₙ)^{1/(n+1)}`, which the maximal
  difference theorem sharpens.
* M. Ullrich, *On bounds between all s-numbers and widths of convex sets*,
  preprint, 2026. <https://arxiv.org/abs/2608.05024>. Source of the maximal
  difference theorem `aₙ ≤ e · (n+1) · hₙ`.
