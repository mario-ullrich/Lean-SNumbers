/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Seminorm
import Mathlib.Topology.Order.Compact

/-!
# John's ellipsoid — the maximal-volume position

This is the first step towards the Kadets–Snobar and Garling–Gordon projection
theorems (`BasicResults/KadetsSnobar.lean`, `BasicResults/GarlingGordon.lean`),
whose sharp `‖P‖ ≤ √n` bounds rest on John's ellipsoid theorem (absent from
Mathlib).

We model an ellipsoid inside a symmetric convex body as the image `T (B₂)` of the
Euclidean unit ball under a continuous linear map `T : ℝ^k →L ℝ^k`; its volume is
proportional to `|det T|`. The body is described by a norm, given here as a
`Seminorm ℝ (EuclideanSpace ℝ (Fin k))` `p` that is equivalent to the Euclidean
norm (`c‖x‖ ≤ p x ≤ C‖x‖`, `c > 0`). The ellipsoid `T (B₂)` lies in the body
`{p ≤ 1}` exactly when `T` is *feasible*: `p (T u) ≤ ‖u‖` for all `u`.

## Main result

* `John.exists_maxVolume` — among the feasible operators there is one, `T₀`, of
  maximal `|det|`; it is invertible (`det ≠ 0`). This is the maximal-volume
  inscribed ellipsoid. The John decomposition of identity from its first-order
  optimality (the next step) is not yet formalised.
-/

universe u

namespace John

variable {k : ℕ}

/-- An operator `T : ℝ^k →L ℝ^k` is *feasible* for the body seminorm `p` when the
image `T (B₂)` of the Euclidean unit ball lies in `{p ≤ 1}`, i.e. `p (T u) ≤ ‖u‖`
for every `u`. -/
def Feasible (p : Seminorm ℝ (EuclideanSpace ℝ (Fin k))) :
    Set (EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin k)) :=
  {T | ∀ u, p (T u) ≤ ‖u‖}

/-- The feasible set is closed: for each `u`, `T ↦ p (T u)` is continuous. -/
lemma isClosed_feasible (p : Seminorm ℝ (EuclideanSpace ℝ (Fin k)))
    (hp : Continuous p) : IsClosed (Feasible p) := by
  rw [Feasible, Set.setOf_forall]
  refine isClosed_iInter fun u => isClosed_le ?_ continuous_const
  exact hp.comp (continuous_id.clm_apply continuous_const)

/-- The feasible set is bounded: `c‖x‖ ≤ p x` forces `‖T‖ ≤ 1/c`. -/
lemma feasible_subset_closedBall (p : Seminorm ℝ (EuclideanSpace ℝ (Fin k)))
    {c : ℝ} (hc : 0 < c) (hlo : ∀ x, c * ‖x‖ ≤ p x) :
    Feasible p ⊆ Metric.closedBall 0 (1 / c) := by
  intro T hT
  simp only [Metric.mem_closedBall, dist_zero_right]
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun u => ?_
  have h1 : c * ‖T u‖ ≤ ‖u‖ := le_trans (hlo (T u)) (hT u)
  have h2 : ‖T u‖ ≤ ‖u‖ / c := by rw [le_div_iff₀ hc]; linarith
  exact h2.trans_eq (by rw [one_div, inv_mul_eq_div])

/-- **Maximal-volume inscribed ellipsoid.** For a body seminorm `p` equivalent to
the Euclidean norm (`c‖x‖ ≤ p x ≤ C‖x‖`, `c > 0`), among the feasible operators
there is one of maximal `|det|`, and it is invertible. -/
theorem exists_maxVolume (p : Seminorm ℝ (EuclideanSpace ℝ (Fin k)))
    (hp : Continuous p) {c : ℝ} (hc : 0 < c) (hlo : ∀ x, c * ‖x‖ ≤ p x)
    {C : ℝ} (hup : ∀ x, p x ≤ C * ‖x‖) :
    ∃ T ∈ Feasible p, T.det ≠ 0 ∧ ∀ S ∈ Feasible p, |S.det| ≤ |T.det| := by
  classical
  set C' : ℝ := max C 0 with hC'
  have hC'0 : 0 ≤ C' := le_max_right _ _
  have hup' : ∀ x, p x ≤ C' * ‖x‖ := fun x =>
    (hup x).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
  -- A small multiple of the identity is feasible: gives nonemptiness.
  set δ : ℝ := 1 / (C' + 1) with hδ
  have hδpos : 0 < δ := by positivity
  have hδ1 : δ * C' ≤ 1 := by
    rw [hδ, div_mul_eq_mul_div, div_le_one (by positivity)]; linarith
  set T₀ : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin k) :=
    δ • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin k)) with hT₀
  have hT₀feas : T₀ ∈ Feasible p := by
    intro u
    have : p (T₀ u) = δ * p u := by
      rw [hT₀]; simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply,
        map_smul_eq_mul, Real.norm_eq_abs, abs_of_pos hδpos]
    rw [this]
    calc δ * p u ≤ δ * (C' * ‖u‖) :=
          mul_le_mul_of_nonneg_left (hup' u) hδpos.le
      _ = (δ * C') * ‖u‖ := by ring
      _ ≤ 1 * ‖u‖ := mul_le_mul_of_nonneg_right hδ1 (norm_nonneg _)
      _ = ‖u‖ := one_mul _
  -- The determinant is continuous and the feasible set is compact.
  have hcompact : IsCompact (Feasible p) :=
    Metric.isCompact_of_isClosed_isBounded (isClosed_feasible p hp)
      (Metric.isBounded_closedBall.subset (feasible_subset_closedBall p hc hlo))
  obtain ⟨T, hTfeas, hTmax⟩ :=
    hcompact.exists_isMaxOn ⟨T₀, hT₀feas⟩
      (continuous_abs.comp ContinuousLinearMap.continuous_det).continuousOn
  refine ⟨T, hTfeas, ?_, fun S hS => hTmax hS⟩
  -- `det T₀ = δ ^ (finrank) ≠ 0`, and `|det T| ≥ |det T₀| > 0`, so `det T ≠ 0`.
  have hcoe : (T₀ : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin k))
      = δ • LinearMap.id := by rw [hT₀]; ext x; simp
  have hval : T₀.det = δ ^ Module.finrank ℝ (EuclideanSpace ℝ (Fin k)) := by
    simp only [ContinuousLinearMap.det, hcoe, LinearMap.det_smul, LinearMap.det_id, mul_one]
  have hdet₀ne : T₀.det ≠ 0 := by rw [hval]; exact pow_ne_zero _ (ne_of_gt hδpos)
  have hpos : 0 < |T.det| := lt_of_lt_of_le (abs_pos.mpr hdet₀ne) (hTmax hT₀feas)
  exact fun h => by simp [h] at hpos

end John
