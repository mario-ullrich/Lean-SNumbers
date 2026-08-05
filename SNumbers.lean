/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
import SNumbers.Basic
import SNumbers.Helpers
import SNumbers.PiLpCoordinates
import SNumbers.Approximation
import SNumbers.Bernstein
import SNumbers.Gelfand
import SNumbers.Kolmogorov
import SNumbers.KolmogorovLifting
import SNumbers.Hilbert
import SNumbers.Inequalities
import SNumbers.MaxDifference
import SNumbers.Uniqueness
import SNumbers.SingularValuesFinDim
import SNumbers.Injectivity
import SNumbers.Entropy
import SNumbers.Examples.ExHelpers
import SNumbers.Examples.Identity
import SNumbers.Examples.DiagonalMatrices
import SNumbers.Examples.IdentityL1Linfty

/-!
# s-Numbers of bounded linear operators between Banach spaces

The Pietsch axiomatic theory of s-numbers, formalised in Lean 4 / Mathlib.

## Main contents

* `SNumbers.Basic`: the `rank` of a continuous linear map and the Pietsch
  axioms (S1)–(S5), packaged as `IsSNumberSequence`; the (S5')
  strengthening and `IsStrictSNumberSequence`; and absolute homogeneity
  `sₙ(c • T) = ‖c‖ · sₙ(T)`.
* `SNumbers.Helpers`: small generic facts shared across the development —
  rank lemmas for continuous linear maps (`rank_zero`,
  `eq_zero_of_rank_le_zero`, `rank_comp_comp_le`) and operator-norm bounds
  for Mathlib's quotient CLMs `Submodule.mkQL` / `Submodule.liftQL`
  (`norm_mkQL_le`, `norm_liftQL_le`, `liftQL_mkQL`).
* `SNumbers.PiLpCoordinates`: the coordinate projection/embedding
  contractions `projFin` / `padFin` between `ℓ^p_n` and `ℓ^p_m`.
* `SNumbers.Approximation`: the approximation numbers `aₙ`, proved to form a
  strict s-number sequence (S1)–(S5)+(S5'), and to be the *largest*
  s-number sequence (`sₙ(S) ≤ aₙ(S)`).
* `SNumbers.Bernstein`, `SNumbers.Gelfand`, `SNumbers.Kolmogorov`,
  `SNumbers.Hilbert`: the further canonical examples `bₙ`, `cₙ`, `dₙ`, `hₙ`,
  one file each, all proved to form s-number sequences (Bernstein, Gelfand,
  Kolmogorov strict). The Hilbert numbers are developed over any `RCLike`
  field; their (S5) normalisation rests on the singular value decomposition,
  formalised via `exists_l2_section` and `approximationNumber_id_euclidean`.
* `SNumbers.KolmogorovLifting`: an alternative development of the
  Kolmogorov numbers via Pietsch's identity `d_n S = a_n(S ∘ Q_X)`,
  where `Q_X : ℓ¹(B_X) →L[𝕜] X` is the canonical summation surjection.
  Many axioms become one-liners over `a_n`, but the construction needs
  `[CompleteSpace X]` (an infinite series in `X`), so it is restricted to
  Banach spaces. Lives in the sub-namespace `SNumbers.Lifting`.
* `SNumbers.Uniqueness`: on Hilbert spaces every s-number sequence coincides
  with the approximation numbers, `sₙ(S) = aₙ(S)` (Pietsch 2.11.9), via the
  scalar factorisation `SVD.exists_scalar_factorisation` in `BasicResults.SVD`.
* `SNumbers.Inequalities`: the general-space comparison results — the lower
  bound `hₙ ≤ sₙ`, the sandwich theorem `hₙ ≤ sₙ ≤ aₙ`, the bound
  `aₙ ≤ (1+√n)·min(cₙ,dₙ)`, the determinant ingredients
  (`∏ aₖ(T) = ‖det T‖`, `aₖ(B∘S∘A) ≤ ‖B‖‖A‖·hₖ(S)`) for the maximal
  difference theorem, and point selection below the Gelfand / Kolmogorov
  numbers.
* `SNumbers.MaxDifference`: the **maximal difference theorem**
  `aₙ ≤ e·(n+1)·hₙ` (sharp constant `(n+1)^{n+1}/nⁿ`), hence
  `sₙ ≤ e·(n+1)·tₙ` for any two s-number sequences — the conjecture of Carl
  and Pietsch up to the constant `e`. Proved via the determinant quantities
  `Δₖ(S) = sup{|det(B∘S∘A)| : ‖A‖, ‖B‖ ≤ 1}`, whose decay is bounded below
  through the explicit rank-`n` approximant `L = SA(BSA)⁻¹BS` and a bordered
  determinant. Corollary for every s-number sequence `s`:
  `max(cₙ,dₙ) ≤ e·(n+1)·sₙ`, hence in particular `max(cₙ,dₙ) ≤ e·(n+1)·hₙ`
  and the Mityagin–Henkin conjecture `max(cₙ,dₙ) ≤ e·(n+1)·bₙ` up to the
  constant `e`.
* `SNumbers.SingularValuesFinDim`: in finite dimension, Mathlib's singular
  numbers coincide with every s-number sequence
  (`sn_eq_singularValues_of_finiteDimensional`, `sₙ = σₙ`), via uniqueness
  and Eckart–Young (`aₙ = σₙ`). The bridge to Mathlib's eigenvalue-defined
  `σ` (`project_singularValues_eq`) is fully proved: the `uₖ` diagonalise
  `S* ∘ S` with eigenvalues `σₖ²`, and matching eigenvalue multiplicities
  (`card_filter_eigenvalues_eq`) identifies them with Mathlib's. The whole
  file rests only on the SVD existence theorem in `BasicResults.SVD`.
* `SNumbers.Injectivity`: injective and surjective s-number sequences; the
  Gelfand numbers `cₙ` are injective and the Kolmogorov numbers `dₙ` are
  surjective.
* `SNumbers.Entropy`: the entropy numbers
  `eₙ(S) = inf{ε > 0 : S(B_X) is covered by 2ⁿ balls of radius ε}`, with the two
  inequalities that govern them: additivity `e_{n+m}(S+T) ≤ eₙ(S) + e_m(T)` and,
  over a densely normed scalar field, multiplicativity
  `e_{n+m}(B∘S) ≤ eₙ(B)·e_m(S)`; the axioms (S2) and (S3) are corollaries of
  these. They are *not* s-numbers — the rank axiom (S4) fails, since
  `eₙ(S) > 0` for every `S ≠ 0`, and the norming axiom (S5) fails from `n = 2`
  on; such a sequence is called a *pseudo-s-number* sequence. What they measure
  is compactness: `S` is a compact operator if and only if `eₙ(S) → 0`
  (`isCompactOperator_iff_tendsto_entropyNumber`, for complete target spaces;
  the forward implication needs no completeness).
* `SNumbers.Examples.ExHelpers`: the geometric and rank ingredients shared by the
  worked examples — the coordinate pigeonhole and the (weighted) flatness lemmas
  behind the Gelfand-width lower bounds.
* `SNumbers.Examples.Identity`: the **identity embedding**
  `id : ℓ^q_m → ℓ^p_m` between different exponents (`p ≤ q`): the operator norm
  `‖id‖ = m^{1/p-1/q}`, the universal upper bound `aₙ(id) ≤ (m-n)^{1/p-1/q}`, and
  the exact approximation numbers `aₙ(id) = (m-n)^{1/p-1/q}` (via the classical
  Gelfand-width lower bound, proved there). This is the unit-diagonal case, kept
  self-contained.
* `SNumbers.Examples.DiagonalMatrices`: a worked example computing the s-numbers
  of the **diagonal operators**, for all pairs of exponents. Same exponent
  (`D_σ : ℓ^p_m → ℓ^p_m`): for every strict s-number sequence
  `sₙ(D_σ) = ‖σ_n‖` (the `(n+1)`-th largest entry), the Hilbert numbers being
  only bounded above, plus the operator norm `‖D_σ‖ = ⨆ i, ‖σ i‖`. Mixed
  exponents (`D_σ : ℓ^q_m → ℓ^p_m`, `p < q < ∞`): the approximation numbers are the
  `ℓ^r`-norm of the tail of the diagonal,
  `aₙ(D_σ) = (∑_{k≥n} ‖σ_k‖^r)^{1/r}` with `1/r = 1/p - 1/q`, and the operator
  norm is `‖D_σ‖ = ‖σ‖_{ℓ^r}`; for `q ≤ p` the `r = ∞` bounds are recorded.
* `SNumbers.Examples.IdentityL1Linfty`: the inclusion `I : ℓ₁ → ℓ_∞`, the witness for
  order-optimality of the factor `n+1` in the maximal difference theorem: `½ ≤ cₙ(I) ≤ 1`
  and `hₙ(I) = 1/(n+1)`, hence `((n+1)/2)·hₙ(I) ≤ cₙ(I)` while `cₙ ≤ e·(n+1)·hₙ` in
  general. The upper bound `hₙ(I) ≤ 1/(n+1)` factors `I` through `ℓ₂` and estimates the
  two Hilbert–Schmidt factors of `B I A` by sign averaging
  (`BasicResults.LittleGrothendieck`), then sums the singular values of the compact
  operator `B I A` via Bessel and Cauchy–Schwarz.

A companion library `BasicResults` collects supporting material: Auerbach's
lemma (fully proved), the singular value decomposition `BasicResults.SVD` (the
compact SVD, the scalar factorisation for the uniqueness theorem, and the bound
`(n+1)·aₙ(T₂T₁) ≤ ‖T₁‖_HS·‖T₂‖_HS` for a compact product), and
`BasicResults.LittleGrothendieck` (sign averaging and the little Grothendieck
bounds behind the `ℓ₁ → ℓ_∞` example). Auxiliary material on approximable
operators lives in the `AddOns` library.

## References

* A. Pietsch, *s-Numbers of operators in Banach spaces*, Studia Math. 51
  (1974), 201–223.
* A. Pietsch, *Operator ideals*, North-Holland Mathematical Library 20,
  North-Holland, 1980.
* A. Pietsch, *Eigenvalues and s-numbers*, Cambridge studies in advanced
  mathematics 13, Cambridge University Press, 1987.
* M. Ullrich, *Inequalities between s-numbers*, Advances in Operator
  Theory **9** (2024), no. 4, article no. 82.
  <https://doi.org/10.1007/s43036-024-00386-x> (preprint: arXiv:2405.05509).
* M. Ullrich, *On bounds between all s-numbers and widths of convex sets*,
  preprint, 2026 (the maximal difference theorem).
-/
