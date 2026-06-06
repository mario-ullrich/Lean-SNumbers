/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# The Garling–Gordon projection theorem

A closed subspace of a Banach space whose codimension is at most `n` is the
kernel of a bounded projection of norm at most `√n`. This is a classical fact of
Banach-space geometry (Garling–Gordon 1971; Pietsch, *Eigenvalues and s-numbers*
1.7.17).

The statement is `sorry`.
-/

universe u

open ContinuousLinearMap

namespace SNumbers

variable {𝕜 : Type u} [RCLike 𝕜]
variable {X : Type u} [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]

/-- **Garling–Gordon theorem.** For a closed subspace `M` of a Banach space `X`
of codimension at most `n`, there is a bounded projection `P : X →L[𝕜] X`
(`P ∘ P = P`) with kernel exactly `M` and operator norm `‖P‖ ≤ √n`. The range of
`P` is a complement of `M` of dimension `codim M ≤ n`, and the Garling–Gordon
bound on the projection constant of an `n`-dimensional space gives `‖P‖ ≤ √n`. -/
theorem exists_projection_ker_eq_of_codim_le
    {M : Submodule 𝕜 X} (hM_closed : IsClosed (M : Set X)) {n : ℕ}
    (hM_codim : Module.rank 𝕜 (X ⧸ M) ≤ (n : Cardinal)) :
    ∃ P : X →L[𝕜] X, P.comp P = P ∧
      LinearMap.ker (P : X →ₗ[𝕜] X) = M ∧ ‖P‖ ≤ Real.sqrt n := by
  sorry

end SNumbers
