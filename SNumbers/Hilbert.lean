/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
import SNumbers.Approximation
import Mathlib.Analysis.InnerProductSpace.l2Space

/-!
# Hilbert numbers `h_n` (real case)

The Hilbert numbers are defined via `ℓ₂` as a Hilbert space. We follow the
convention that the scalar field is `ℝ`; the complex case is analogous.

`h_n S = sup { a_n (B ∘ S ∘ A) / (‖B‖ * ‖A‖) :
                 A : ℓ_2 →L X, B : Y →L ℓ_2, A ≠ 0, B ≠ 0 }`.
-/

universe u

open scoped Cardinal
open ContinuousLinearMap

namespace SNumbers

variable {X Y : Type u}
variable [NormedAddCommGroup X] [NormedSpace ℝ X]
variable [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- A model of `ℓ₂` over `ℝ`: the space `lp` with exponent 2 over `ℕ`. -/
abbrev L2 : Type _ := lp (fun _ : ℕ => ℝ) 2

/-- The `n`-th **Hilbert number** of a continuous linear map between real
Banach spaces.

`h_n S = sup { a_n (B ∘ S ∘ A) / (‖B‖ * ‖A‖) :
                  A : ℓ_2 →L X, B : Y →L ℓ_2, A ≠ 0, B ≠ 0 }`. -/
noncomputable def hilbertNumber (S : X →L[ℝ] Y) (n : ℕ) : ℝ :=
  sSup {r | ∃ (A : L2 →L[ℝ] X) (B : Y →L[ℝ] L2),
      A ≠ 0 ∧ B ≠ 0 ∧
      r = approximationNumber (B.comp (S.comp A)) n / (‖B‖ * ‖A‖)}

/-- Hilbert numbers form an s-number sequence (statement; proof TBD). -/
theorem isSNumberSequence_hilbertNumber :
    IsSNumberSequence (𝕜 := ℝ) (fun {_X _Y} _ _ _ _ S n => hilbertNumber S n) := by
  sorry

end SNumbers
