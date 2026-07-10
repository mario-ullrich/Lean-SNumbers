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
import SNumbers.Examples.DiagonalMatrices
import SNumbers.Examples.IdentityEmbedding

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
* `SNumbers.Approximation`: the approximation numbers `aₙ`, proved to form a
  strict s-number sequence (S1)–(S5)+(S5'), and to be the *largest*
  s-number sequence (`sₙ(S) ≤ aₙ(S)`).
* `SNumbers.Bernstein`, `SNumbers.Gelfand`, `SNumbers.Kolmogorov`,
  `SNumbers.Hilbert`: the further canonical examples `bₙ`, `cₙ`, `dₙ`, `hₙ`,
  one file each, all proved to form s-number sequences (Bernstein, Gelfand,
  Kolmogorov strict). The Hilbert numbers are developed over any `RCLike`
  field; their (S5) normalisation rests on the singular value decomposition
  (see `BasicResults.SVD`).
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
  `aₙ ≤ (1+√n)·min(cₙ,dₙ)`, and the determinant ingredients
  (`∏ aₖ(T) = ‖det T‖`, point selection) for the reverse bound below.
* `SNumbers.MaxDifference`: the **maximal difference theorem**
  `max(cₙ,dₙ) ≤ e·(n+1)·hₙ`, proved via the determinant quantities
  `Δₖ(S) = sup{|det(B∘S∘A)| : ‖A‖, ‖B‖ ≤ 1}` — hence
  `max(cₙ,dₙ) ≤ e·(n+1)·sₙ` for every s-number sequence, in particular the
  Mityagin–Henkin conjecture `max(cₙ,dₙ) ≤ e·(n+1)·bₙ` up to the constant `e`.
  (The sharp constant is `(n+1)^{n+1}/nⁿ`; by telescoping it recovers the
  former product bound `∏cₖ ≤ (n+1)^{n+1}∏hₖ` and the earlier geometric-mean
  bound, which were removed as superseded.)
* `SNumbers.PiLpCoordinates`: the coordinate projection/embedding
  contractions `projFin` / `padFin` between `ℓ^p_n` and `ℓ^p_m`.
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
* `SNumbers.Examples.DiagonalMatrices`: a worked example computing the s-numbers
  of a **diagonal operator** `D_σ : ℓ^p_m → ℓ^p_m`. For every strict s-number
  sequence `sₙ(D_σ) = ‖σ_n‖` (the `(n+1)`-th largest entry); the Hilbert numbers
  are only bounded above. Includes the operator norm `‖D_σ‖ = ⨆ i, ‖σ i‖`.
* `SNumbers.Examples.IdentityEmbedding`: the **identity embedding**
  `id : ℓ^q_m → ℓ^p_m` between different exponents (`p ≤ q`): the operator norm
  `‖id‖ = m^{1/p-1/q}`, the universal upper bound `aₙ(id) ≤ (m-n)^{1/p-1/q}`, and
  the exact approximation numbers `aₙ(id) = (m-n)^{1/p-1/q}` (modulo the classical
  Gelfand-width lower bound).

A companion library `BasicResults` collects supporting material: Auerbach's
lemma (fully proved) and the singular value decomposition `BasicResults.SVD`
(the compact SVD plus the scalar factorisation for the uniqueness theorem).
Auxiliary material on approximable operators lives in the
`AddOns` library.

## References

* A. Pietsch, *s-Numbers of operators in Banach spaces*, Studia Math. 51
  (1974), 201–223.
* A. Pietsch, *Eigenvalues and s-numbers*, Cambridge studies in advanced
  mathematics 13, Cambridge University Press, 1987.
* M. Ullrich, *Inequalities between s-numbers*, Advances in Operator
  Theory **9** (2024), no. 4, article no. 82.
  <https://doi.org/10.1007/s43036-024-00386-x> (preprint: arXiv:2405.05509).
-/
