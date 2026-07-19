/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
import SNumbers.Basic
import Mathlib.Analysis.Normed.Group.Quotient

/-!
# Helpers shared across s-number constructions

A small library of utilities used by more than one s-number construction.
None of the content here is specific to a particular `s`-number sequence.

* Rank facts about continuous linear maps:
  `ContinuousLinearMap.rank_zero`, `eq_zero_of_rank_le_zero`,
  `rank_comp_comp_le`. The bare definition `ContinuousLinearMap.rank` lives
  in `SNumbers.Basic`.
* `Submodule.norm_mkQL_le` — operator-norm bound `‖V.mkQL‖ ≤ 1` for the
  quotient projection `Submodule.mkQL`.
* `Submodule.norm_liftQL_le` — operator-norm bound `‖V.liftQL f h‖ ≤ ‖f‖`
  for the universal lift `Submodule.liftQL`, plus the computation rule
  `Submodule.liftQL_mkQL`.
* `SNumbers.finrank_euclideanSpace_fin'` — `finrank 𝕜 (EuclideanSpace 𝕜 (Fin n)) = n`
  over any `NontriviallyNormedField` (Mathlib's `finrank_euclideanSpace_fin`
  needs `RCLike`), used by the `(S5)` normalisations of every s-number.

Mathlib ships the `ContinuousLinearMap` wrappers `Submodule.mkQL` and
`Submodule.liftQL` (in
`Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient`) for general
topological modules but without operator-norm information; the lemmas here
add the missing norm bounds in the normed setting.
-/

universe u

open scoped Cardinal

namespace ContinuousLinearMap

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]

section Rank
variable {X Y : Type*}
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]

@[simp] lemma rank_zero : (0 : X →L[𝕜] Y).rank = 0 := by simp

/-- The only continuous linear map of rank `0` is the zero map. -/
lemma eq_zero_of_rank_le_zero {L : X →L[𝕜] Y}
    (hL : L.rank ≤ (0 : Cardinal)) : L = 0 := by
  have hbot : LinearMap.range (L : X →ₗ[𝕜] Y) = ⊥ :=
    Submodule.rank_eq_zero.mp (le_antisymm hL zero_le)
  exact ContinuousLinearMap.coe_injective (LinearMap.range_eq_bot.mp hbot)

end Rank

section CompRank
-- Comparing the ranks of operators with different domain/codomain forces a
-- single universe for `Cardinal` to be well-defined.
variable {W X Y Z : Type u}
variable [NormedAddCommGroup W] [NormedSpace 𝕜 W]
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
variable [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]

/-- The rank of a composition is bounded by the rank of the middle factor. -/
lemma rank_comp_comp_le (A : W →L[𝕜] X) (L : X →L[𝕜] Y) (B : Y →L[𝕜] Z) :
    (B.comp (L.comp A)).rank ≤ L.rank := by
  have hsub :
      LinearMap.range (B.comp (L.comp A) : W →ₗ[𝕜] Z) ≤
        Submodule.map (B : Y →ₗ[𝕜] Z) (LinearMap.range (L : X →ₗ[𝕜] Y)) := by
    intro z hz
    obtain ⟨w, hw⟩ := hz
    exact ⟨L (A w), ⟨A w, rfl⟩, by simpa using hw⟩
  calc Module.rank 𝕜 (LinearMap.range (B.comp (L.comp A) : W →ₗ[𝕜] Z))
      ≤ Module.rank 𝕜
          (Submodule.map (B : Y →ₗ[𝕜] Z) (LinearMap.range (L : X →ₗ[𝕜] Y))) :=
        Submodule.rank_mono hsub
    _ ≤ Module.rank 𝕜 (LinearMap.range (L : X →ₗ[𝕜] Y)) :=
        rank_map_le _ _

end CompRank

end ContinuousLinearMap

/-! ## Operator-norm bounds for the quotient CLMs `Submodule.mkQL` / `liftQL`

Mathlib (`Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient`)
provides `Submodule.mkQL` — the quotient projection `Y →L[𝕜] (Y ⧸ V)` — and
`Submodule.liftQL` — the universal lift of a continuous linear map through
that quotient — for general *topological* modules, but without any
operator-norm information. In the normed setting the projection is a
contraction (`‖V.mkQL‖ ≤ 1`) and the lift does not increase the norm
(`‖V.liftQL f h‖ ≤ ‖f‖`). We record those two bounds here, together with the
computation rule `V.liftQL f h (V.mkQL y) = f y`. -/

namespace Submodule

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {Y Z : Type*}
variable [SeminormedAddCommGroup Y] [NormedSpace 𝕜 Y]
variable [SeminormedAddCommGroup Z] [NormedSpace 𝕜 Z]

/-- The quotient projection `V.mkQL : Y →L[𝕜] (Y ⧸ V)` is a contraction. -/
lemma norm_mkQL_le (V : Submodule 𝕜 Y) : ‖V.mkQL‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => by
    rw [one_mul, V.mkQL_apply, mkQ_apply]
    exact _root_.Submodule.Quotient.norm_mk_le (S := V) x

/-- Lifting `f` and then precomposing with the quotient projection recovers
`f`: `V.liftQL f h (V.mkQL y) = f y`. -/
@[simp] lemma liftQL_mkQL (V : Submodule 𝕜 Y) (f : Y →L[𝕜] Z)
    (h : V ≤ LinearMap.ker (f : Y →ₗ[𝕜] Z)) (y : Y) :
    V.liftQL f h (V.mkQL y) = f y := by
  rw [V.liftQL_apply, V.mkQL_apply]
  exact V.liftQ_apply (f : Y →ₗ[𝕜] Z) y

/-- The lift `V.liftQL f h : (Y ⧸ V) →L[𝕜] Z` does not increase the operator
norm: `‖V.liftQL f h‖ ≤ ‖f‖`. -/
lemma norm_liftQL_le (V : Submodule 𝕜 Y) (f : Y →L[𝕜] Z)
    (h : V ≤ LinearMap.ker (f : Y →ₗ[𝕜] Z)) :
    ‖V.liftQL f h‖ ≤ ‖f‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun x => by
    -- For each `x : Y ⧸ V`, take a representative `y` with `‖y‖ ≤ ‖x‖ + ε`.
    -- Then `liftQL f h x = f y`, so `‖liftQL f h x‖ ≤ ‖f‖ * ‖y‖ ≤ ‖f‖ * (‖x‖ + ε)`,
    -- and `ε → 0`.
    refine le_of_forall_pos_le_add fun ε hε => ?_
    have hf_pos : (0 : ℝ) < ‖f‖ + 1 := by positivity
    obtain ⟨y, hy_eq, hy_norm⟩ :=
      Submodule.Quotient.norm_mk_lt x (div_pos hε hf_pos)
    have h_eq : V.liftQL f h x = f y := by
      rw [V.liftQL_apply, ← hy_eq]
      exact V.liftQ_apply (f : Y →ₗ[𝕜] Z) y
    rw [h_eq]
    calc ‖f y‖
        ≤ ‖f‖ * ‖y‖ := f.le_opNorm y
      _ ≤ ‖f‖ * (‖x‖ + ε / (‖f‖ + 1)) :=
          mul_le_mul_of_nonneg_left hy_norm.le (norm_nonneg _)
      _ = ‖f‖ * ‖x‖ + ‖f‖ / (‖f‖ + 1) * ε := by ring
      _ ≤ ‖f‖ * ‖x‖ + 1 * ε := by
          gcongr
          rw [div_le_one hf_pos]; linarith [norm_nonneg f]
      _ = ‖f‖ * ‖x‖ + ε := by ring

end Submodule

namespace SNumbers

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]

/-- The dimension of `ℓ₂ⁿ = EuclideanSpace 𝕜 (Fin n)` is `n`, over any
`NontriviallyNormedField`. Mathlib's `finrank_euclideanSpace_fin` proves the
same, but only for `RCLike` fields; the s-number axioms are stated over a general
field, so this variant is what the `(S5)` normalisations `_id_euclidean` need. -/
lemma finrank_euclideanSpace_fin' (n : ℕ) :
    Module.finrank 𝕜 (EuclideanSpace 𝕜 (Fin n)) = n := by
  rw [(WithLp.linearEquiv 2 𝕜 (Fin n → 𝕜)).finrank_eq, Module.finrank_pi 𝕜]
  exact Fintype.card_fin _

end SNumbers
