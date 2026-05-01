/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
import SNumbers.Approximation

/-!
# Gelfand numbers `c_n`

`c_n S = inf_{M ⊆ X closed, codim M ≤ n} ‖S|_M‖`.
-/

universe u

open scoped Cardinal
open ContinuousLinearMap

namespace SNumbers

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]
variable {X Y : Type u}
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]

/-- The `n`-th **Gelfand number** of a continuous linear map.

`c_n S = inf_{M ⊆ X closed, codim M ≤ n} ‖S|_M‖`. -/
noncomputable def gelfandNumber (S : X →L[𝕜] Y) (n : ℕ) : ℝ :=
  sInf {r | ∃ M : Submodule 𝕜 X,
      IsClosed (M : Set X) ∧
      Module.rank 𝕜 (X ⧸ M) ≤ (n : Cardinal) ∧
      r = ‖S.comp M.subtypeL‖}

/-- Gelfand numbers form an s-number sequence (statement; proof TBD). -/
theorem isSNumberSequence_gelfandNumber :
    IsSNumberSequence (𝕜 := 𝕜) (fun {_X _Y} _ _ _ _ S n => gelfandNumber S n) := by
  sorry

end SNumbers
