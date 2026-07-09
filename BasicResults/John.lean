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

open scoped RealInnerProductSpace

/-- **John position.** Replacing the body seminorm `p` by `q = p ∘ T₀` for the
maximiser `T₀` normalises the maximal-volume ellipsoid to the Euclidean unit
ball: the identity is feasible for `q`, and every feasible operator has
`|det| ≤ 1`. -/
theorem exists_johnPosition (p : Seminorm ℝ (EuclideanSpace ℝ (Fin k)))
    (hp : Continuous p) {c : ℝ} (hc : 0 < c) (hlo : ∀ x, c * ‖x‖ ≤ p x)
    {C : ℝ} (hup : ∀ x, p x ≤ C * ‖x‖) :
    ∃ q : Seminorm ℝ (EuclideanSpace ℝ (Fin k)), Continuous q ∧
      (∀ u, q u ≤ ‖u‖) ∧ ∀ S ∈ Feasible q, |S.det| ≤ 1 := by
  obtain ⟨T₀, hfeas, hdet, hmax⟩ := exists_maxVolume p hp hc hlo hup
  refine ⟨p.comp T₀.toLinearMap, ?_, ?_, fun S hS => ?_⟩
  · show Continuous (fun u => (p.comp T₀.toLinearMap) u)
    simp only [Seminorm.comp_apply]
    exact hp.comp T₀.continuous
  · intro u; simpa [Seminorm.comp_apply] using hfeas u
  have hTS : T₀.comp S ∈ Feasible p := fun u => by
    simpa [Seminorm.comp_apply, ContinuousLinearMap.comp_apply] using hS u
  have hdc : (T₀.comp S).det = T₀.det * S.det := by
    simp only [ContinuousLinearMap.det, ContinuousLinearMap.coe_comp, LinearMap.det_comp]
  have hle := hmax (T₀.comp S) hTS
  rw [hdc, abs_mul] at hle
  exact (mul_le_iff_le_one_right (abs_pos.mpr hdet)).mp hle

/-- The **contact set** of a body seminorm `q`: unit vectors `u` whose associated
linear functional `⟪·, u⟫` is dominated by `q`. These are the points where the
Euclidean unit sphere touches the boundary `{q = 1}` with a shared supporting
hyperplane; the John decomposition of identity is supported on this set. -/
def Contact (q : Seminorm ℝ (EuclideanSpace ℝ (Fin k))) :
    Set (EuclideanSpace ℝ (Fin k)) :=
  {u | ‖u‖ = 1 ∧ ∀ x, ⟪x, u⟫ ≤ q x}

/-- A contact point has `q u = 1`: `1 = ⟪u,u⟫ ≤ q u`, and `q u ≤ ‖u‖ = 1` when
`q` is feasible for the identity. -/
lemma contact_apply_eq_one {q : Seminorm ℝ (EuclideanSpace ℝ (Fin k))}
    (hq1 : ∀ u, q u ≤ ‖u‖) {u : EuclideanSpace ℝ (Fin k)} (hu : u ∈ Contact q) :
    q u = 1 := by
  refine le_antisymm (by simpa [hu.1] using hq1 u) ?_
  have := hu.2 u
  rwa [real_inner_self_eq_norm_sq, hu.1, one_pow] at this

/-- The contact set is compact: it is a closed subset of the (compact) unit
sphere. -/
lemma isCompact_contact (q : Seminorm ℝ (EuclideanSpace ℝ (Fin k))) :
    IsCompact (Contact q) := by
  have hsub : Contact q ⊆ Metric.sphere 0 1 := fun u hu => by
    simpa using hu.1
  have hcl : IsClosed (Contact q) := by
    have heq : Contact q = {u : EuclideanSpace ℝ (Fin k) | ‖u‖ = 1} ∩ ⋂ x, {u | ⟪x, u⟫ ≤ q x} := by
      ext u
      simp only [Contact, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter]
    rw [heq]
    exact (isClosed_eq continuous_norm continuous_const).inter
      (isClosed_iInter fun x => isClosed_le (continuous_const.inner continuous_id) continuous_const)
  exact (isCompact_sphere 0 1).of_isClosed_subset hcl hsub

/-- The self-adjoint **rank-one operator** `u ⊗ u : x ↦ ⟪u, x⟫ • u`. The John
decomposition of identity expresses `id` as a positive combination of these over
contact points. -/
noncomputable def rankOneSA (u : EuclideanSpace ℝ (Fin k)) :
    EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin k) :=
  (innerSL ℝ u).smulRight u

@[simp] lemma rankOneSA_apply (u x : EuclideanSpace ℝ (Fin k)) :
    rankOneSA u x = ⟪u, x⟫ • u := rfl

/-- **Contact support (both signs).** A contact point `u` has `|⟪x, u⟫| ≤ q x`
for all `x`. -/
lemma abs_inner_le_of_contact {q : Seminorm ℝ (EuclideanSpace ℝ (Fin k))}
    {u : EuclideanSpace ℝ (Fin k)} (hu : u ∈ Contact q) (x : EuclideanSpace ℝ (Fin k)) :
    |⟪x, u⟫| ≤ q x := by
  rw [abs_le]
  refine ⟨?_, hu.2 x⟩
  have h := hu.2 (-x)
  rw [inner_neg_left, map_neg_eq_map] at h
  linarith

/-- **Quadratic form of a decomposition of identity.** If
`∑ᵢ (cᵢ · ⟪uᵢ, x⟫) • uᵢ = x` for all `x`, then `∑ᵢ cᵢ · ⟪uᵢ, z⟫² = ‖z‖²`. -/
lemma sum_weight_inner_sq {N : ℕ} (c : Fin N → ℝ) (u : Fin N → EuclideanSpace ℝ (Fin k))
    (hdec : ∀ x, ∑ i, (c i * ⟪u i, x⟫) • u i = x) (z : EuclideanSpace ℝ (Fin k)) :
    ∑ i, c i * ⟪u i, z⟫ ^ 2 = ‖z‖ ^ 2 := by
  have h := congrArg (fun w => ⟪w, z⟫) (hdec z)
  simp only [sum_inner, real_inner_smul_left, real_inner_self_eq_norm_sq] at h
  rw [← h]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- Parseval on the standard basis: `∑ⱼ ⟪w, eⱼ⟫² = ‖w‖²`. -/
private lemma sum_inner_single_sq (w : EuclideanSpace ℝ (Fin k)) :
    ∑ j, ⟪w, EuclideanSpace.single j (1 : ℝ)⟫ ^ 2 = ‖w‖ ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [EuclideanSpace.inner_single_right]
  simp [Real.norm_eq_abs, sq_abs]

/-- **Weights of a decomposition of identity sum to the dimension.** If
`∑ᵢ (cᵢ · ⟪uᵢ, x⟫) • uᵢ = x` and each `‖uᵢ‖ = 1`, then `∑ᵢ cᵢ = k`. -/
lemma sum_weight_eq {N : ℕ} (c : Fin N → ℝ) (u : Fin N → EuclideanSpace ℝ (Fin k))
    (hdec : ∀ x, ∑ i, (c i * ⟪u i, x⟫) • u i = x) (hu : ∀ i, ‖u i‖ = 1) :
    ∑ i, c i = (k : ℝ) := by
  have hpars : ∀ i, ∑ j, ⟪u i, EuclideanSpace.single j (1 : ℝ)⟫ ^ 2 = 1 := fun i => by
    rw [sum_inner_single_sq, hu i, one_pow]
  have hone : ∀ j : Fin k, ∑ i, c i * ⟪u i, EuclideanSpace.single j (1 : ℝ)⟫ ^ 2 = 1 := fun j => by
    rw [sum_weight_inner_sq c u hdec (EuclideanSpace.single j (1 : ℝ)), PiLp.norm_single]
    simp
  calc ∑ i, c i = ∑ i, c i * ∑ j, ⟪u i, EuclideanSpace.single j (1 : ℝ)⟫ ^ 2 := by
        refine Finset.sum_congr rfl fun i _ => ?_; rw [hpars i, mul_one]
    _ = ∑ i, ∑ j, c i * ⟪u i, EuclideanSpace.single j (1 : ℝ)⟫ ^ 2 := by
        refine Finset.sum_congr rfl fun i _ => Finset.mul_sum _ _ _
    _ = ∑ j, ∑ i, c i * ⟪u i, EuclideanSpace.single j (1 : ℝ)⟫ ^ 2 := Finset.sum_comm
    _ = ∑ _j : Fin k, (1 : ℝ) := Finset.sum_congr rfl fun j _ => hone j
    _ = (k : ℝ) := by simp

/-- **John decomposition of identity** — the classical core of John's ellipsoid
theorem (stated here as `sorry`; the remaining hard input).

In John position — the identity is a maximal-volume feasible operator for the body
seminorm `q` (`q u ≤ ‖u‖`, and `|det S| ≤ 1` for every feasible `S`) — the identity
is a positive combination of the rank-one projections onto contact points, with
weights summing to the dimension `k`:
`∑ᵢ (cᵢ · ⟪uᵢ, x⟫) • uᵢ = x`, with `uᵢ ∈ Contact q`, `cᵢ ≥ 0`, `∑ᵢ cᵢ = k`.

Classical proof (not yet formalised — no Mathlib scaffolding for the analytic
step): were `k⁻¹ • id ∉ convexHull ℝ {rankOneSA u : u ∈ Contact q}` — a compact
convex set of operators — `geometric_hahn_banach` would produce a symmetric `H`
with `⟪H u, u⟫ ≤ tr H` violated on all contacts; then `id ↝ id + t·H` stays
feasible for small `t > 0` (the delicate compactness / subdifferential argument)
while `det(id + tH) > 1`, contradicting maximality. `Carathéodory` finally turns
membership of the convex hull into the finite positive combination. -/
theorem john_decomposition (q : Seminorm ℝ (EuclideanSpace ℝ (Fin k)))
    (hq : Continuous q) (hq1 : ∀ u, q u ≤ ‖u‖)
    (hmax : ∀ S ∈ Feasible q, |S.det| ≤ 1) :
    ∃ (N : ℕ) (u : Fin N → EuclideanSpace ℝ (Fin k)) (c : Fin N → ℝ),
      (∀ i, u i ∈ Contact q) ∧ (∀ i, 0 ≤ c i) ∧ (∑ i, c i = (k : ℝ)) ∧
      (∀ x, ∑ i, (c i * ⟪u i, x⟫) • u i = x) := by
  sorry

end John
