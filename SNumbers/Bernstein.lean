/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
import SNumbers.Approximation

/-!
# Bernstein numbers `b_n`

`b_n S = sup_{M ⊆ X, dim M = n + 1} inf_{x ∈ M, x ≠ 0} ‖S x‖ / ‖x‖`.
-/

universe u

open scoped Cardinal
open ContinuousLinearMap

namespace SNumbers

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]
variable {X Y : Type u}
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]

/-- The smallest gain `inf_{x ∈ M, x ≠ 0} ‖S x‖ / ‖x‖` of an operator `S` on
a non-zero subspace `M`. -/
noncomputable def gainOnSubspace (S : X →L[𝕜] Y) (M : Submodule 𝕜 X) : ℝ :=
  sInf {r | ∃ x : X, x ∈ M ∧ x ≠ 0 ∧ r = ‖S x‖ / ‖x‖}

/-- The `n`-th **Bernstein number** of a continuous linear map.

`b_n S = sup_{M ⊆ X, dim M = n + 1} gainOnSubspace S M`. -/
noncomputable def bernsteinNumber (S : X →L[𝕜] Y) (n : ℕ) : ℝ :=
  sSup {r | ∃ M : Submodule 𝕜 X,
      Module.rank 𝕜 M = (n + 1 : ℕ) ∧ r = gainOnSubspace S M}

/-- The Bernstein numbers form an s-number sequence (statement; proof TBD).

The full proof of all five axioms is non-trivial — in particular (S2)
requires care because the suprema range over different subspaces `M`.
By Pietsch's *sandwich* theorem the Bernstein numbers are
sandwiched between the Hilbert and approximation numbers. -/
theorem isSNumberSequence_bernsteinNumber :
    IsSNumberSequence (𝕜 := 𝕜) (fun {_X _Y} _ _ _ _ S n => bernsteinNumber S n) := by
  sorry

end SNumbers
