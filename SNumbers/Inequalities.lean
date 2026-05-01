/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
import SNumbers.Approximation
import SNumbers.Hilbert

/-!
# Comparison of `s`-number sequences

Pietsch's classical extremality result: among all `s`-number sequences,
the **Hilbert numbers** `hₙ` are the smallest and the **approximation
numbers** `aₙ` are the largest.

## Main results

* `allSNumbers_eq_on_HilbertSpace` — on a Hilbert space, every `s`-number
  sequence agrees with the approximation numbers (`sorry`).
* `sn_le_approximationNumber` — upper bound `sₙ(S) ≤ aₙ(S)` (proved).
* `hilbertNumber_le_sn` — lower bound `hₙ(S) ≤ sₙ(S)` over `ℝ` (`sorry`).
* `hilbertNumber_le_sn_le_approximationNumber` — Pietsch's sandwich
  theorem `hₙ(S) ≤ sₙ(S) ≤ aₙ(S)` (proved, modulo the two `sorry`s above).

## Proof strategies

* **Hilbert coincidence.** Sketch: use the SVD of `S*S` to identify each
  `s_n S` with the `(n+1)`-th singular value of `S`, which equals
  `a_n S` by the Eckart–Young theorem. Left to a follow-up.
* **Upper bound `sₙ ≤ aₙ`.** For any `A` with `rank A ≤ n` decompose
  `S = A + (S - A)` and apply (S2): `sₙ(S) ≤ sₙ(A) + ‖S - A‖ = ‖S - A‖`
  (the second equality by (S4)). Take the infimum over `A`.
* **Lower bound `hₙ ≤ sₙ`.** For any contractions `A : ℓ₂ → X`, `B : Y → ℓ₂`
  use (S3) to get `sₙ(BSA) ≤ sₙ(S)`. The Hilbert coincidence then gives
  `aₙ(BSA) = sₙ(BSA) ≤ sₙ(S)`; supremum over `(A, B)` produces `hₙ(S)`.
* **Sandwich.** Direct combination of the upper and lower bounds.
-/

namespace SNumbers

open ContinuousLinearMap

/-! ### Hilbert-space coincidence theorem -/

/-- On a Hilbert space, every `s`-number sequence agrees with the
approximation numbers: `s S n = aₙ S` for every continuous linear map `S`
between Hilbert spaces. -/
theorem allSNumbers_eq_on_HilbertSpace
    {𝕜 : Type u} [RCLike 𝕜]
    {H₁ H₂ : Type u}
    [NormedAddCommGroup H₁] [InnerProductSpace 𝕜 H₁] [CompleteSpace H₁]
    [NormedAddCommGroup H₂] [InnerProductSpace 𝕜 H₂] [CompleteSpace H₂]
    {s : Family 𝕜} (_hs : IsSNumberSequence s) (S : H₁ →L[𝕜] H₂) (n : ℕ) :
    s S n = approximationNumber S n := by
  sorry

/-! ### Upper bound: `sₙ ≤ aₙ` -/

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]
variable {X : Type u} [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
variable {Y : Type u} [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] [CompleteSpace Y]

omit [CompleteSpace X] [CompleteSpace Y] in
/-- For every `s`-number sequence and every operator `S : X → Y`,
`sₙ(S) ≤ aₙ(S)`. The easy half of Pietsch's sandwich theorem; uses only
axioms (S2) and (S4) of `IsSNumberSequence`. -/
theorem sn_le_approximationNumber
    {s : Family 𝕜} (hs : IsSNumberSequence s) (S : X →L[𝕜] Y) (n : ℕ) :
    s S n ≤ approximationNumber S n := by
  refine le_csInf (approximationSet_nonempty S n) ?_
  rintro r ⟨A, hA, rfl⟩
  have hS_eq : S = A + (S - A) := by abel
  have h_low : s A n = 0 := hs.vanishes_on_low_rank A n hA
  calc s S n
      = s (A + (S - A)) n := by rw [← hS_eq]
    _ ≤ s A n + ‖S - A‖ := hs.subadditive A (S - A) n
    _ = ‖S - A‖ := by rw [h_low, zero_add]

/-! ### Lower bound: `hₙ ≤ sₙ` (over `ℝ`)

The Hilbert numbers were introduced for **real** Banach spaces in
`SNumbers.Hilbert`, so the lower bound is stated only in that setting. -/

variable {Xℝ : Type} [NormedAddCommGroup Xℝ] [NormedSpace ℝ Xℝ] [CompleteSpace Xℝ]
variable {Yℝ : Type} [NormedAddCommGroup Yℝ] [NormedSpace ℝ Yℝ] [CompleteSpace Yℝ]

/-- For every `s`-number sequence on real Banach spaces and every operator
`S : Xℝ → Yℝ`, `hₙ(S) ≤ sₙ(S)`. -/
theorem hilbertNumber_le_sn
    {s : Family ℝ} (_hs : IsSNumberSequence s) (S : Xℝ →L[ℝ] Yℝ) (n : ℕ) :
    hilbertNumber S n ≤ s S n := by
  sorry

/-! ### Pietsch's sandwich theorem -/

/-- **Pietsch's sandwich theorem.** For every `s`-number sequence `s` on
real Banach spaces and every bounded operator `S : Xℝ → Yℝ`:
`hₙ(S) ≤ sₙ(S) ≤ aₙ(S)`. -/
theorem hilbertNumber_le_sn_le_approximationNumber
    {s : Family ℝ} (hs : IsSNumberSequence s) (S : Xℝ →L[ℝ] Yℝ) (n : ℕ) :
    hilbertNumber S n ≤ s S n ∧ s S n ≤ approximationNumber S n :=
  ⟨hilbertNumber_le_sn hs S n, sn_le_approximationNumber hs S n⟩

end SNumbers
