/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
import SNumbers.Basic

/-!
# Helpers shared across s-number constructions

A small library of utilities used by more than one s-number construction.
None of the content here is specific to a particular `s`-number sequence.

* Rank facts about continuous linear maps:
  `ContinuousLinearMap.rank_zero`, `eq_zero_of_rank_le_zero`,
  `rank_comp_comp_le`. The bare definition `ContinuousLinearMap.rank` lives
  in `SNumbers.Basic`.
* `SNumbers.le_of_mul_one_sub_le_of_nonneg` — a packaging of the limit
  `α * (1 - ε) ≤ b` for all `ε ∈ (0, 1)` ⇒ `α ≤ b`. Mathlib provides
  `le_of_forall_lt_one_mul_le` for ordered multiplicative groups
  (`Algebra.Order.Group.DenselyOrdered`) and bespoke standalone copies for
  `ℝ≥0` and `ℝ≥0∞`, but no direct ℝ version — `ℝ` is not a multiplicative
  group (zero), and `ℝ≥0`/`ℝ≥0∞` are not groups either. Our lemma is a thin
  wrapper around the additive `le_of_forall_pos_le_add` and is used in the
  (S3) and (S5') arguments for Kolmogorov numbers and the (S5') argument
  for approximation numbers.
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

namespace SNumbers

/-- If `0 ≤ α` and `α * (1 - ε) ≤ b` for every `ε ∈ (0, 1)`, then `α ≤ b`.

Useful as the closing step of proofs that bound `α` from above via a
density argument that delivers `α * (1 - ε) ≤ b` for arbitrarily small
positive `ε`. -/
lemma le_of_mul_one_sub_le_of_nonneg {α b : ℝ} (hα : 0 ≤ α)
    (h : ∀ ε : ℝ, 0 < ε → ε < 1 → α * (1 - ε) ≤ b) : α ≤ b := by
  rcases hα.lt_or_eq with hα_pos | hα_eq
  · refine le_of_forall_pos_le_add fun δ hδ => ?_
    set ε := min (δ / α) (1 / 2) with hε_def
    have hε_pos : 0 < ε := lt_min (div_pos hδ hα_pos) (by norm_num)
    have hε_lt1 : ε < 1 := (min_le_right _ _).trans_lt (by norm_num)
    have hαε_le : α * ε ≤ δ :=
      calc α * ε
          ≤ α * (δ / α) := mul_le_mul_of_nonneg_left (min_le_left _ _) hα_pos.le
        _ = δ := mul_div_cancel₀ _ hα_pos.ne'
    have h_at_ε := h ε hε_pos hε_lt1
    linarith
  · -- `α = 0`: every `ε ∈ (0, 1)` gives `0 ≤ b`, hence `α ≤ b`.
    have h0 := h (1 / 2) (by norm_num) (by norm_num)
    linarith [hα_eq.symm]

end SNumbers
