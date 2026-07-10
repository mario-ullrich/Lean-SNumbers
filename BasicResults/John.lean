/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.HahnBanach
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

## Main results

* `John.exists_maxVolume` — among the feasible operators there is one, `T₀`, of
  maximal `|det|`; it is invertible (`det ≠ 0`). This is the maximal-volume
  inscribed ellipsoid.
* `John.exists_johnPosition` — normalising by `T₀` puts the maximal ellipsoid at
  the Euclidean unit ball (`q u ≤ ‖u‖`, and `|det S| ≤ 1` for every feasible `S`).
* `John.john_decomposition` — the **decomposition of identity** in John position,
  `∑ᵢ cᵢ uᵢ⊗uᵢ = id` over contact points with `∑ᵢ cᵢ = dim`. This is the one
  classical analytic input still stated as `sorry` (its first-order-optimality
  proof has no Mathlib scaffolding yet); everything downstream is proved from it.
* `John.exists_projection_real` — **Kadets–Snobar over `ℝ`** modulo the above:
  every finite-dimensional subspace of a real normed space is the range of a
  projection `P` with `‖P‖ ≤ √(dim)`. Its analytic core is the weighted
  Cauchy–Schwarz bound `John.norm_sum_weight_smul_le`.
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

/-- **Weighted Cauchy–Schwarz for a decomposition of identity** (the analytic
heart of the Kadets–Snobar estimate). If `∑ᵢ (cᵢ·⟪uᵢ,x⟫)•uᵢ = x` and `cᵢ ≥ 0`,
then for any scalars `aᵢ`, `‖∑ᵢ (cᵢ·aᵢ)•uᵢ‖ ≤ √(∑ᵢ cᵢ·aᵢ²)`. -/
lemma norm_sum_weight_smul_le {N : ℕ} (c : Fin N → ℝ)
    (u : Fin N → EuclideanSpace ℝ (Fin k)) (hdec : ∀ x, ∑ i, (c i * ⟪u i, x⟫) • u i = x)
    (hc : ∀ i, 0 ≤ c i) (a : Fin N → ℝ) :
    ‖∑ i, (c i * a i) • u i‖ ≤ Real.sqrt (∑ i, c i * a i ^ 2) := by
  set w := ∑ i, (c i * a i) • u i with hw
  have hB : 0 ≤ ∑ i, c i * a i ^ 2 := Finset.sum_nonneg fun i _ => mul_nonneg (hc i) (sq_nonneg _)
  have hww : ‖w‖ ^ 2 = ∑ i, c i * a i * ⟪u i, w⟫ := by
    rw [← real_inner_self_eq_norm_sq]
    nth_rewrite 1 [hw]
    rw [sum_inner]
    exact Finset.sum_congr rfl fun i _ => real_inner_smul_left _ _ _
  have hCS : (∑ i, c i * a i * ⟪u i, w⟫) ^ 2
      ≤ (∑ i, c i * a i ^ 2) * (∑ i, c i * ⟪u i, w⟫ ^ 2) := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
      (fun i => Real.sqrt (c i) * a i) (fun i => Real.sqrt (c i) * ⟪u i, w⟫)
    have e1 : ∀ i, Real.sqrt (c i) * a i * (Real.sqrt (c i) * ⟪u i, w⟫)
        = c i * a i * ⟪u i, w⟫ := fun i => by
      rw [mul_mul_mul_comm, Real.mul_self_sqrt (hc i)]; ring
    have e2 : ∀ i, (Real.sqrt (c i) * a i) ^ 2 = c i * a i ^ 2 := fun i => by
      rw [mul_pow, Real.sq_sqrt (hc i)]
    have e3 : ∀ i, (Real.sqrt (c i) * ⟪u i, w⟫) ^ 2 = c i * ⟪u i, w⟫ ^ 2 := fun i => by
      rw [mul_pow, Real.sq_sqrt (hc i)]
    simpa only [e1, e2, e3] using h
  rw [sum_weight_inner_sq c u hdec w, ← hww] at hCS
  rcases eq_or_lt_of_le (norm_nonneg w) with h0 | hpos
  · rw [← h0]; exact Real.sqrt_nonneg _
  · have ht : (0 : ℝ) < ‖w‖ ^ 2 := by positivity
    have hle : ‖w‖ ^ 2 ≤ ∑ i, c i * a i ^ 2 := by
      refine le_of_mul_le_mul_right ?_ ht
      calc ‖w‖ ^ 2 * ‖w‖ ^ 2 = (‖w‖ ^ 2) ^ 2 := (pow_two _).symm
        _ ≤ (∑ i, c i * a i ^ 2) * ‖w‖ ^ 2 := hCS
    calc ‖w‖ = Real.sqrt (‖w‖ ^ 2) := (Real.sqrt_sq (norm_nonneg w)).symm
      _ ≤ Real.sqrt (∑ i, c i * a i ^ 2) := Real.sqrt_le_sqrt hle

/-- **Kadets–Snobar over `ℝ`** (modulo `john_decomposition`). Every
finite-dimensional subspace `V` of a real normed space `Y` is the range of a
bounded projection `P : Y →L[ℝ] Y` with `‖P‖ ≤ √(dim V)`.

The proof puts `V` in John position: transport the Euclidean structure of
`ℝ^{dim V}` to `V` through the maximal-volume ellipsoid `M` (built from the John
decomposition of identity `∑ᵢ cᵢ uᵢ⊗uᵢ = id`). The contact points `uᵢ` give unit
vectors `vᵢ = M uᵢ ∈ V` and functionals `φᵢ = ⟪uᵢ, M⁻¹ ·⟫ ∈ V*` of norm `≤ 1`,
which Hahn–Banach (`exists_extension_norm_eq`) extends to `gᵢ ∈ Y*` without
increasing the norm. Then `P = ∑ᵢ cᵢ · gᵢ ⊗ vᵢ` is the identity on `V` (so it is
a projection onto `V`), and the weighted Cauchy–Schwarz estimate
`norm_sum_weight_smul_le` together with `∑ᵢ cᵢ = dim V` yields `‖P‖ ≤ √(dim V)`. -/
theorem exists_projection_real {Y : Type u} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (V : Submodule ℝ Y) [FiniteDimensional ℝ V] :
    ∃ P : Y →L[ℝ] Y, P.comp P = P ∧
      LinearMap.range (P : Y →ₗ[ℝ] Y) = V ∧ ‖P‖ ≤ Real.sqrt (Module.finrank ℝ V) := by
  classical
  set k := Module.finrank ℝ V with hk
  rcases Nat.eq_zero_or_pos k with hk0 | hkpos
  · -- `V = ⊥`: the zero map works.
    refine ⟨0, by simp, ?_, ?_⟩
    · have hV : V = ⊥ := Submodule.finrank_eq_zero.mp (hk.symm.trans hk0)
      rw [hV]; simp
    · rw [hk0]; simp
  -- From now on `0 < k`.
  -- A continuous linear equivalence `ℝ^k ≃L V` (both have dimension `k`).
  have hEfin : Module.finrank ℝ (EuclideanSpace ℝ (Fin k)) = k := by
    rw [(WithLp.linearEquiv 2 ℝ (Fin k → ℝ)).finrank_eq, Module.finrank_pi ℝ, Fintype.card_fin]
  set L : EuclideanSpace ℝ (Fin k) ≃L[ℝ] V :=
    ContinuousLinearEquiv.ofFinrankEq (hEfin.trans hk) with hLdef
  -- The body seminorm on `ℝ^k`: `p x = ‖L x‖`, equivalent to the Euclidean norm.
  set p : Seminorm ℝ (EuclideanSpace ℝ (Fin k)) :=
    (normSeminorm ℝ Y).comp (V.subtypeL.comp (L : EuclideanSpace ℝ (Fin k) →L[ℝ] V)).toLinearMap
    with hpdef
  have hp_apply : ∀ x, p x = ‖((L x : V) : Y)‖ := fun x => by
    simp only [hpdef, Seminorm.comp_apply, coe_normSeminorm, ContinuousLinearMap.coe_coe,
      ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply, ContinuousLinearEquiv.coe_coe]
  have hpc : Continuous p := by
    have hcont : Continuous fun x => V.subtypeL (L x) := V.subtypeL.continuous.comp L.continuous
    refine (continuous_norm.comp hcont).congr fun x => ?_
    show ‖V.subtypeL (L x)‖ = p x
    rw [Submodule.subtypeL_apply]
    exact (hp_apply x).symm
  -- Upper bound `p x ≤ ‖L‖ ‖x‖`.
  set C : ℝ := ‖(L : EuclideanSpace ℝ (Fin k) →L[ℝ] V)‖ with hC
  have hup : ∀ x, p x ≤ C * ‖x‖ := fun x => by
    rw [hp_apply]
    exact (L : EuclideanSpace ℝ (Fin k) →L[ℝ] V).le_opNorm x
  -- Lower bound `‖L.symm‖⁻¹ ‖x‖ ≤ p x`; the constant is positive since `0 < k`.
  set D : ℝ := ‖(L.symm : V →L[ℝ] EuclideanSpace ℝ (Fin k))‖ with hD
  have hDpos : 0 < D := by
    have hne : (L.symm : V →L[ℝ] EuclideanSpace ℝ (Fin k)) ≠ 0 := by
      intro hzero
      have he1 : ‖(EuclideanSpace.single (⟨0, hkpos⟩ : Fin k) (1 : ℝ))‖ = 1 := by
        rw [PiLp.norm_single, norm_one]
      have hcontra : (EuclideanSpace.single (⟨0, hkpos⟩ : Fin k) (1 : ℝ)) = 0 := by
        have h2 : (L.symm : V →L[ℝ] EuclideanSpace ℝ (Fin k))
            (L (EuclideanSpace.single (⟨0, hkpos⟩ : Fin k) (1 : ℝ))) = 0 := by
          rw [hzero]; rfl
        rwa [ContinuousLinearEquiv.coe_coe, L.symm_apply_apply] at h2
      rw [hcontra, norm_zero] at he1
      exact one_ne_zero he1.symm
    rw [hD]
    rcases eq_or_lt_of_le (norm_nonneg (L.symm : V →L[ℝ] EuclideanSpace ℝ (Fin k))) with h | h
    · exact absurd ((ContinuousLinearMap.opNorm_zero_iff _).mp h.symm) hne
    · exact h
  have hlo : ∀ x, D⁻¹ * ‖x‖ ≤ p x := fun x => by
    have hbound : ‖x‖ ≤ D * p x := by
      rw [hp_apply]
      have e : ‖x‖ = ‖(L.symm : V →L[ℝ] EuclideanSpace ℝ (Fin k)) (L x)‖ := by
        rw [ContinuousLinearEquiv.coe_coe, L.symm_apply_apply]
      rw [e]
      calc ‖(L.symm : V →L[ℝ] EuclideanSpace ℝ (Fin k)) (L x)‖
          ≤ D * ‖L x‖ := (L.symm : V →L[ℝ] EuclideanSpace ℝ (Fin k)).le_opNorm (L x)
        _ = D * ‖((L x : V) : Y)‖ := by rw [Submodule.norm_coe]
    have := mul_le_mul_of_nonneg_left hbound (le_of_lt (inv_pos.mpr hDpos))
    rwa [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hDpos), one_mul] at this
  -- The maximal-volume ellipsoid `T₀` and the John-position seminorm `q = p ∘ T₀`.
  obtain ⟨T₀, hT₀feas, hT₀det, hT₀max⟩ :=
    exists_maxVolume p hpc (inv_pos.mpr hDpos) hlo hup
  set q : Seminorm ℝ (EuclideanSpace ℝ (Fin k)) := p.comp T₀.toLinearMap with hqdef
  have hq1 : ∀ u, q u ≤ ‖u‖ := fun u => by
    rw [hqdef, Seminorm.comp_apply]; exact hT₀feas u
  have hqc : Continuous q := by
    rw [hqdef]; exact hpc.comp T₀.continuous
  have hqmax : ∀ S ∈ Feasible q, |S.det| ≤ 1 := fun S hS => by
    have hTS : T₀.comp S ∈ Feasible p := fun u => by
      have h := hS u
      rw [hqdef, Seminorm.comp_apply, ContinuousLinearMap.coe_coe] at h
      simpa [ContinuousLinearMap.comp_apply] using h
    have hdc : (T₀.comp S).det = T₀.det * S.det := by
      simp only [ContinuousLinearMap.det, ContinuousLinearMap.coe_comp, LinearMap.det_comp]
    have hle := hT₀max (T₀.comp S) hTS
    rw [hdc, abs_mul] at hle
    exact (mul_le_iff_le_one_right (abs_pos.mpr hT₀det)).mp hle
  -- The composite equivalence `M = L ∘ T₀ : ℝ^k ≃L V`; `‖M z‖ = q z`.
  set T₀e : EuclideanSpace ℝ (Fin k) ≃L[ℝ] EuclideanSpace ℝ (Fin k) :=
    T₀.toContinuousLinearEquivOfDetNeZero hT₀det with hT₀e
  set M : EuclideanSpace ℝ (Fin k) ≃L[ℝ] V := T₀e.trans L with hMdef
  have hMapply : ∀ z, M z = L (T₀ z) := fun z => by
    rw [hMdef, ContinuousLinearEquiv.trans_apply, hT₀e,
      ContinuousLinearMap.toContinuousLinearEquivOfDetNeZero_apply]
  have hqM : ∀ z, ‖(M z : Y)‖ = q z := fun z => by
    rw [hMapply, hqdef, Seminorm.comp_apply, ContinuousLinearMap.coe_coe, hp_apply]
  -- The John decomposition of identity in John position.
  obtain ⟨N, u, c, hcontact, hcnn, hcsum, hdec⟩ := john_decomposition q hqc hq1 hqmax
  -- Functionals `φ i = ⟪u i, M.symm ·⟫` on `V`, of norm `≤ 1`.
  set φ : Fin N → (V →L[ℝ] ℝ) :=
    fun i => (innerSL ℝ (u i)).comp (M.symm : V →L[ℝ] EuclideanSpace ℝ (Fin k)) with hφ
  have hφapply : ∀ i (w : V), φ i w = ⟪u i, M.symm w⟫ := fun i w => by
    simp only [hφ, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      innerSL_apply_apply]
  have hφnorm : ∀ i, ‖φ i‖ ≤ 1 := fun i => by
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun w => ?_
    rw [one_mul, hφapply, Real.norm_eq_abs, real_inner_comm]
    calc |⟪M.symm w, u i⟫| ≤ q (M.symm w) := abs_inner_le_of_contact (hcontact i) (M.symm w)
      _ = ‖(M (M.symm w) : Y)‖ := (hqM (M.symm w)).symm
      _ = ‖w‖ := by rw [M.apply_symm_apply, Submodule.norm_coe]
  -- Hahn–Banach: extend each `φ i` to `g i ∈ Y*` without increasing the norm.
  choose g hg_ext hg_norm using fun i => exists_extension_norm_eq V (φ i)
  have hgnorm1 : ∀ i, ‖g i‖ ≤ 1 := fun i => (hg_norm i).trans_le (hφnorm i)
  -- The projection `P = ∑ᵢ cᵢ · g i ⊗ (M (u i))`.
  set P : Y →L[ℝ] Y := ∑ i, (c i) • ((g i).smulRight ((M (u i) : V) : Y)) with hP
  have hPapply : ∀ y, P y = ∑ i, (c i * g i y) • ((M (u i) : Y)) := fun y => by
    rw [hP]
    simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.smulRight_apply, smul_smul]
  have hPmem : ∀ y, P y ∈ V := fun y => by
    rw [hPapply]
    exact V.sum_mem fun i _ => V.smul_mem _ (M (u i)).2
  -- `P` is the identity on `V`.
  have hPV : ∀ w : V, P (w : Y) = (w : Y) := fun w => by
    rw [hPapply]
    have hgi : ∀ i, g i (w : Y) = ⟪u i, M.symm w⟫ := fun i => by rw [hg_ext i w, hφapply i w]
    simp only [hgi]
    have hpull : ((M (∑ i, (c i * ⟪u i, M.symm w⟫) • u i) : V) : Y)
        = ∑ i, (c i * ⟪u i, M.symm w⟫) • ((M (u i) : V) : Y) := by
      rw [map_sum, Submodule.coe_sum]
      exact Finset.sum_congr rfl fun i _ => by rw [map_smul, Submodule.coe_smul]
    rw [← hpull, hdec (M.symm w), M.apply_symm_apply]
  refine ⟨P, ?_, ?_, ?_⟩
  · -- `P ∘ P = P`, since `P` fixes its range `⊆ V`.
    ext y
    simpa [ContinuousLinearMap.comp_apply] using hPV ⟨P y, hPmem y⟩
  · -- `range P = V`.
    apply le_antisymm
    · rintro x hx
      rw [LinearMap.mem_range] at hx
      obtain ⟨y, rfl⟩ := hx
      exact hPmem y
    · intro w hw
      rw [LinearMap.mem_range]
      exact ⟨w, by simpa using hPV ⟨w, hw⟩⟩
  · -- `‖P‖ ≤ √k`.
    refine ContinuousLinearMap.opNorm_le_bound P (Real.sqrt_nonneg _) fun y => ?_
    have hpull : ((M (∑ i, (c i * g i y) • u i) : V) : Y)
        = ∑ i, (c i * g i y) • ((M (u i) : V) : Y) := by
      rw [map_sum, Submodule.coe_sum]
      exact Finset.sum_congr rfl fun i _ => by rw [map_smul, Submodule.coe_smul]
    have hPyeq : P y = ((M (∑ i, (c i * g i y) • u i) : V) : Y) := by rw [hPapply, hpull]
    have hb : ∑ i, c i * (g i y) ^ 2 ≤ (k : ℝ) * ‖y‖ ^ 2 := by
      have hstep : ∀ i, c i * (g i y) ^ 2 ≤ c i * ‖y‖ ^ 2 := fun i => by
        apply mul_le_mul_of_nonneg_left _ (hcnn i)
        calc (g i y) ^ 2 = ‖g i y‖ ^ 2 := by rw [Real.norm_eq_abs, sq_abs]
          _ ≤ (‖g i‖ * ‖y‖) ^ 2 := by
              apply pow_le_pow_left₀ (norm_nonneg _) ((g i).le_opNorm y)
          _ ≤ (1 * ‖y‖) ^ 2 := by
              apply pow_le_pow_left₀ (by positivity)
              exact mul_le_mul_of_nonneg_right (hgnorm1 i) (norm_nonneg _)
          _ = ‖y‖ ^ 2 := by rw [one_mul]
      calc ∑ i, c i * (g i y) ^ 2 ≤ ∑ i, c i * ‖y‖ ^ 2 := Finset.sum_le_sum fun i _ => hstep i
        _ = (∑ i, c i) * ‖y‖ ^ 2 := (Finset.sum_mul _ _ _).symm
        _ = (k : ℝ) * ‖y‖ ^ 2 := by rw [hcsum]
    calc ‖P y‖ = q (∑ i, (c i * g i y) • u i) := by rw [hPyeq, hqM]
      _ ≤ ‖∑ i, (c i * g i y) • u i‖ := hq1 _
      _ ≤ Real.sqrt (∑ i, c i * (g i y) ^ 2) :=
          norm_sum_weight_smul_le c u hdec hcnn (fun i => g i y)
      _ ≤ Real.sqrt ((k : ℝ) * ‖y‖ ^ 2) := Real.sqrt_le_sqrt hb
      _ = Real.sqrt (k : ℝ) * ‖y‖ := by
          rw [Real.sqrt_mul (Nat.cast_nonneg k), Real.sqrt_sq (norm_nonneg _)]

end John

