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
* `Submodule.mkQL` — the `ContinuousLinearMap` form of the quotient
  projection `Submodule.mkQ`, with operator-norm bound `‖V.mkQL‖ ≤ 1`.
* `Submodule.liftQL` — the `ContinuousLinearMap` form of the universal
  lift `Submodule.liftQ` (a CLM `f : Y →L[𝕜] Z` with kernel containing
  `V` lifts to `Y ⧸ V →L[𝕜] Z`), with operator-norm bound
  `‖V.liftQL f h‖ ≤ ‖f‖`.

Mathlib ships `Submodule.mkQ` and `Submodule.liftQ` as `LinearMap`s and
the corresponding `NormedAddGroupHom`s in
`Mathlib.Analysis.Normed.Group.Quotient`, but no `ContinuousLinearMap`
wrappers — `Submodule.mkQL` and `Submodule.liftQL` close that gap.
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
    Submodule.rank_eq_zero.mp (le_antisymm hL (Cardinal.zero_le _))
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

/-! ## Continuous-linear-map versions of `Submodule.mkQ` and `Submodule.liftQ` -/

namespace Submodule

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {Y Z : Type*}
variable [SeminormedAddCommGroup Y] [NormedSpace 𝕜 Y]
variable [SeminormedAddCommGroup Z] [NormedSpace 𝕜 Z]

/-- The quotient map `Y →L[𝕜] (Y ⧸ V)` as a continuous linear map.
The `L` suffix follows the mathlib convention `Submodule.subtype` (a
`LinearMap`) → `Submodule.subtypeL` (a `ContinuousLinearMap`). -/
noncomputable def mkQL (V : Submodule 𝕜 Y) : Y →L[𝕜] (Y ⧸ V) :=
  V.mkQ.mkContinuous 1 fun x => by
    rw [one_mul, mkQ_apply]
    exact _root_.Submodule.Quotient.norm_mk_le (S := V) x

@[simp] lemma mkQL_apply (V : Submodule 𝕜 Y) (x : Y) :
    V.mkQL x = V.mkQ x := rfl

lemma norm_mkQL_le (V : Submodule 𝕜 Y) : ‖V.mkQL‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

/-- Lift a continuous linear map `f : Y →L[𝕜] Z` whose kernel contains `V`
to a continuous linear map `(Y ⧸ V) →L[𝕜] Z`. The norm bound
`‖V.liftQL f h‖ ≤ ‖f‖` is `Submodule.norm_liftQL_le`. -/
noncomputable def liftQL (V : Submodule 𝕜 Y) (f : Y →L[𝕜] Z)
    (h : V ≤ LinearMap.ker (f : Y →ₗ[𝕜] Z)) : (Y ⧸ V) →L[𝕜] Z :=
  (V.liftQ (f : Y →ₗ[𝕜] Z) h).mkContinuous ‖f‖ <| by
    -- For each `x : Y ⧸ V`, take a representative `y` with `‖y‖ ≤ ‖x‖ + ε`.
    -- Then `liftQ f h x = f y`, so `‖liftQ f h x‖ ≤ ‖f‖ * ‖y‖ ≤ ‖f‖ * (‖x‖ + ε)`,
    -- and `ε → 0`.
    intro x
    refine le_of_forall_pos_le_add fun ε hε => ?_
    have hf_pos : (0 : ℝ) < ‖f‖ + 1 := by positivity
    obtain ⟨y, hy_eq, hy_norm⟩ :=
      Submodule.Quotient.norm_mk_lt x (div_pos hε hf_pos)
    have h_eq : (V.liftQ (f : Y →ₗ[𝕜] Z) h) x = f y := by
      rw [← hy_eq]; exact V.liftQ_apply (f : Y →ₗ[𝕜] Z) y
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

@[simp] lemma liftQL_mkQL (V : Submodule 𝕜 Y) (f : Y →L[𝕜] Z)
    (h : V ≤ LinearMap.ker (f : Y →ₗ[𝕜] Z)) (y : Y) :
    V.liftQL f h (V.mkQL y) = f y :=
  V.liftQ_apply (f : Y →ₗ[𝕜] Z) y

lemma norm_liftQL_le (V : Submodule 𝕜 Y) (f : Y →L[𝕜] Z)
    (h : V ≤ LinearMap.ker (f : Y →ₗ[𝕜] Z)) :
    ‖V.liftQL f h‖ ≤ ‖f‖ :=
  LinearMap.mkContinuous_norm_le _ (norm_nonneg _) _

end Submodule
