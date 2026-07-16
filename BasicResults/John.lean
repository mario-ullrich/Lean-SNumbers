/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Group.Quotient
import Mathlib.Analysis.Normed.Module.DoubleDual
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.Seminorm
import Mathlib.Topology.Order.Compact

/-!
# John's ellipsoid — the maximal-volume position

This is the first step towards the Kadets–Snobar and Garling–Gordon projection
theorems (`BasicResults/KadetsSnobar.lean`, `BasicResults/GarlingGordon.lean`),
whose sharp `‖P‖ ≤ √n` bounds rest on John's ellipsoid theorem (absent from
Mathlib). Everything is done over an arbitrary `RCLike` field `𝕜` (so both the
real and complex cases are covered at once).

We model an ellipsoid inside a symmetric convex body as the image `T (B₂)` of the
Euclidean unit ball under a continuous linear map `T : 𝕜^k →L 𝕜^k`; its volume is
proportional to `‖det T‖`. The body is described by a norm, given here as a
`Seminorm 𝕜 (EuclideanSpace 𝕜 (Fin k))` `p` that is equivalent to the Euclidean
norm (`c‖x‖ ≤ p x ≤ C‖x‖`, `c > 0`). The ellipsoid `T (B₂)` lies in the body
`{p ≤ 1}` exactly when `T` is *feasible*: `p (T u) ≤ ‖u‖` for all `u`.

## Main results

* `John.exists_maxVolume` — among the feasible operators there is one, `T₀`, of
  maximal `‖det‖`; it is invertible (`det ≠ 0`). This is the maximal-volume
  inscribed ellipsoid.
* `John.exists_johnPosition` — normalising by `T₀` puts the maximal ellipsoid at
  the Euclidean unit ball (`q u ≤ ‖u‖`, and `‖det S‖ ≤ 1` for every feasible `S`).
* `John.john_decomposition` — the **decomposition of identity** in John position,
  `∑ᵢ cᵢ uᵢ⊗uᵢ = id` over contact points with `∑ᵢ cᵢ = dim`. This is the one
  classical analytic input still stated as `sorry` (its first-order-optimality
  proof has no Mathlib scaffolding yet); everything downstream is proved from it.
* `John.exists_projection` — **Kadets–Snobar** modulo the above: every
  finite-dimensional subspace of a normed `𝕜`-space is the range of a projection
  `P` with `‖P‖ ≤ √(dim)`. Its analytic core is the weighted Cauchy–Schwarz
  bound `John.norm_sum_weight_smul_le`.
* `John.exists_projection_ker` — **Garling–Gordon** (ε-form) modulo the above,
  dual to Kadets–Snobar: every closed subspace `M` with finite-dimensional
  quotient is the kernel of a projection `P` with `‖P‖ ≤ √(codim M) + ε`, for
  every `ε > 0`. Built on the dual `(X ⧸ M)*`, representing contact points via
  `Φ.flip` (avoiding the topological double dual).
-/

universe u

open scoped InnerProductSpace ComplexConjugate

open RCLike (re)

namespace John

variable {𝕜 : Type u} [RCLike 𝕜] {k : ℕ}

/-- An operator `T : 𝕜^k →L 𝕜^k` is *feasible* for the body seminorm `p` when the
image `T (B₂)` of the Euclidean unit ball lies in `{p ≤ 1}`, i.e. `p (T u) ≤ ‖u‖`
for every `u`. -/
def Feasible (p : Seminorm 𝕜 (EuclideanSpace 𝕜 (Fin k))) :
    Set (EuclideanSpace 𝕜 (Fin k) →L[𝕜] EuclideanSpace 𝕜 (Fin k)) :=
  {T | ∀ u, p (T u) ≤ ‖u‖}

/-- The feasible set is closed: for each `u`, `T ↦ p (T u)` is continuous. -/
lemma isClosed_feasible (p : Seminorm 𝕜 (EuclideanSpace 𝕜 (Fin k)))
    (hp : Continuous p) : IsClosed (Feasible p) := by
  rw [Feasible, Set.setOf_forall]
  refine isClosed_iInter fun u => isClosed_le ?_ continuous_const
  exact hp.comp (continuous_id.clm_apply continuous_const)

/-- The feasible set is bounded: `c‖x‖ ≤ p x` forces `‖T‖ ≤ 1/c`. -/
lemma feasible_subset_closedBall (p : Seminorm 𝕜 (EuclideanSpace 𝕜 (Fin k)))
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
there is one of maximal `‖det‖`, and it is invertible. -/
theorem exists_maxVolume (p : Seminorm 𝕜 (EuclideanSpace 𝕜 (Fin k)))
    (hp : Continuous p) {c : ℝ} (hc : 0 < c) (hlo : ∀ x, c * ‖x‖ ≤ p x)
    {C : ℝ} (hup : ∀ x, p x ≤ C * ‖x‖) :
    ∃ T ∈ Feasible p, T.det ≠ 0 ∧ ∀ S ∈ Feasible p, ‖S.det‖ ≤ ‖T.det‖ := by
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
  set T₀ : EuclideanSpace 𝕜 (Fin k) →L[𝕜] EuclideanSpace 𝕜 (Fin k) :=
    (δ : 𝕜) • ContinuousLinearMap.id 𝕜 (EuclideanSpace 𝕜 (Fin k)) with hT₀
  have hT₀feas : T₀ ∈ Feasible p := by
    intro u
    have hpu : p (T₀ u) = δ * p u := by
      rw [hT₀]
      simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply,
        map_smul_eq_mul, RCLike.norm_ofReal, abs_of_pos hδpos]
    rw [hpu]
    calc δ * p u ≤ δ * (C' * ‖u‖) :=
          mul_le_mul_of_nonneg_left (hup' u) hδpos.le
      _ = (δ * C') * ‖u‖ := by ring
      _ ≤ 1 * ‖u‖ := mul_le_mul_of_nonneg_right hδ1 (norm_nonneg _)
      _ = ‖u‖ := one_mul _
  -- The determinant is continuous and the feasible set is compact.
  haveI : ProperSpace (EuclideanSpace 𝕜 (Fin k) →L[𝕜] EuclideanSpace 𝕜 (Fin k)) :=
    FiniteDimensional.proper_rclike 𝕜 _
  have hcompact : IsCompact (Feasible p) :=
    Metric.isCompact_of_isClosed_isBounded (isClosed_feasible p hp)
      (Metric.isBounded_closedBall.subset (feasible_subset_closedBall p hc hlo))
  obtain ⟨T, hTfeas, hTmax⟩ :=
    hcompact.exists_isMaxOn ⟨T₀, hT₀feas⟩
      (continuous_norm.comp ContinuousLinearMap.continuous_det).continuousOn
  refine ⟨T, hTfeas, ?_, fun S hS => hTmax hS⟩
  -- `det T₀ = δ ^ (finrank) ≠ 0`, and `‖det T‖ ≥ ‖det T₀‖ > 0`, so `det T ≠ 0`.
  have hcoe : (T₀ : EuclideanSpace 𝕜 (Fin k) →ₗ[𝕜] EuclideanSpace 𝕜 (Fin k))
      = (δ : 𝕜) • LinearMap.id := by rw [hT₀]; ext x; simp
  have hval : T₀.det = (δ : 𝕜) ^ Module.finrank 𝕜 (EuclideanSpace 𝕜 (Fin k)) := by
    simp only [ContinuousLinearMap.det, hcoe, LinearMap.det_smul, LinearMap.det_id, mul_one]
  have hdet₀ne : T₀.det ≠ 0 := by
    rw [hval]; exact pow_ne_zero _ (by exact_mod_cast ne_of_gt hδpos)
  have hpos : 0 < ‖T.det‖ :=
    lt_of_lt_of_le (norm_pos_iff.mpr hdet₀ne) (hTmax hT₀feas)
  exact fun h => by simp [h] at hpos

/-- **John position.** Replacing the body seminorm `p` by `q = p ∘ T₀` for the
maximiser `T₀` normalises the maximal-volume ellipsoid to the Euclidean unit
ball: the identity is feasible for `q`, and every feasible operator has
`‖det‖ ≤ 1`. -/
theorem exists_johnPosition (p : Seminorm 𝕜 (EuclideanSpace 𝕜 (Fin k)))
    (hp : Continuous p) {c : ℝ} (hc : 0 < c) (hlo : ∀ x, c * ‖x‖ ≤ p x)
    {C : ℝ} (hup : ∀ x, p x ≤ C * ‖x‖) :
    ∃ q : Seminorm 𝕜 (EuclideanSpace 𝕜 (Fin k)), Continuous q ∧
      (∀ u, q u ≤ ‖u‖) ∧ ∀ S ∈ Feasible q, ‖S.det‖ ≤ 1 := by
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
  rw [hdc, norm_mul] at hle
  exact (mul_le_iff_le_one_right (norm_pos_iff.mpr hdet)).mp hle

/-- The **contact set** of a body seminorm `q`: unit vectors `u` whose associated
linear functional `x ↦ re ⟪x, u⟫` is dominated by `q`. These are the points where
the Euclidean unit sphere touches the boundary `{q = 1}` with a shared supporting
hyperplane; the John decomposition of identity is supported on this set. -/
def Contact (q : Seminorm 𝕜 (EuclideanSpace 𝕜 (Fin k))) :
    Set (EuclideanSpace 𝕜 (Fin k)) :=
  {u | ‖u‖ = 1 ∧ ∀ x, re ⟪x, u⟫_𝕜 ≤ q x}

/-- A contact point has `q u = 1`: `1 = re ⟪u,u⟫ ≤ q u`, and `q u ≤ ‖u‖ = 1` when
`q` is feasible for the identity. -/
lemma contact_apply_eq_one {q : Seminorm 𝕜 (EuclideanSpace 𝕜 (Fin k))}
    (hq1 : ∀ u, q u ≤ ‖u‖) {u : EuclideanSpace 𝕜 (Fin k)} (hu : u ∈ Contact q) :
    q u = 1 := by
  refine le_antisymm (by simpa [hu.1] using hq1 u) ?_
  have := hu.2 u
  rwa [inner_self_eq_norm_sq, hu.1, one_pow] at this

/-- The contact set is compact: it is a closed subset of the (compact) unit
sphere. -/
lemma isCompact_contact (q : Seminorm 𝕜 (EuclideanSpace 𝕜 (Fin k))) :
    IsCompact (Contact q) := by
  have hsub : Contact q ⊆ Metric.sphere 0 1 := fun u hu => by
    simpa using hu.1
  have hcl : IsClosed (Contact q) := by
    have heq : Contact q =
        {u : EuclideanSpace 𝕜 (Fin k) | ‖u‖ = 1} ∩ ⋂ x, {u | re ⟪x, u⟫_𝕜 ≤ q x} := by
      ext u
      simp only [Contact, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter]
    rw [heq]
    refine (isClosed_eq continuous_norm continuous_const).inter
      (isClosed_iInter fun x => isClosed_le ?_ continuous_const)
    exact RCLike.continuous_re.comp (continuous_const.inner continuous_id)
  exact (isCompact_sphere 0 1).of_isClosed_subset hcl hsub

/-- The self-adjoint **rank-one operator** `u ⊗ u : x ↦ ⟪u, x⟫ • u`. The John
decomposition of identity expresses `id` as a positive combination of these over
contact points. -/
noncomputable def rankOneSA (u : EuclideanSpace 𝕜 (Fin k)) :
    EuclideanSpace 𝕜 (Fin k) →L[𝕜] EuclideanSpace 𝕜 (Fin k) :=
  (innerSL 𝕜 u).smulRight u

@[simp] lemma rankOneSA_apply (u x : EuclideanSpace 𝕜 (Fin k)) :
    rankOneSA u x = ⟪u, x⟫_𝕜 • u := rfl

/-- **Contact support.** A contact point `u` has `‖⟪x, u⟫‖ ≤ q x` for all `x`:
choosing a unit phase `a` with `re ⟪a • x, u⟫ = ‖⟪x, u⟫‖`, the contact bound and
`𝕜`-homogeneity of `q` give the claim. -/
lemma norm_inner_le_of_contact {q : Seminorm 𝕜 (EuclideanSpace 𝕜 (Fin k))}
    {u : EuclideanSpace 𝕜 (Fin k)} (hu : u ∈ Contact q) (x : EuclideanSpace 𝕜 (Fin k)) :
    ‖⟪x, u⟫_𝕜‖ ≤ q x := by
  rcases eq_or_ne (⟪x, u⟫_𝕜) 0 with h | h
  · rw [h, norm_zero]; exact apply_nonneg q x
  · set c := ⟪x, u⟫_𝕜 with hcdef
    have hcnorm : ‖c‖ ≠ 0 := norm_ne_zero_iff.mpr h
    have hkey : re ⟪(c / (‖c‖ : 𝕜)) • x, u⟫_𝕜 = ‖c‖ := by
      rw [inner_smul_left, map_div₀, RCLike.conj_ofReal, div_mul_eq_mul_div,
        RCLike.conj_mul, ← RCLike.ofReal_pow, ← RCLike.ofReal_div, RCLike.ofReal_re,
        pow_two, mul_div_assoc, div_self hcnorm, mul_one]
    have hle := hu.2 ((c / (‖c‖ : 𝕜)) • x)
    rw [hkey, map_smul_eq_mul, norm_div, RCLike.norm_ofReal,
      abs_of_nonneg (norm_nonneg c), div_self hcnorm, one_mul] at hle
    exact hle

/-- **Quadratic form of a decomposition of identity.** If
`∑ᵢ ((cᵢ:𝕜) · ⟪uᵢ, x⟫) • uᵢ = x` for all `x`, then `∑ᵢ cᵢ · ‖⟪uᵢ, z⟫‖² = ‖z‖²`. -/
lemma sum_weight_inner_sq {N : ℕ} (c : Fin N → ℝ) (u : Fin N → EuclideanSpace 𝕜 (Fin k))
    (hdec : ∀ x, ∑ i, ((c i : 𝕜) * ⟪u i, x⟫_𝕜) • u i = x) (z : EuclideanSpace 𝕜 (Fin k)) :
    ∑ i, c i * ‖⟪u i, z⟫_𝕜‖ ^ 2 = ‖z‖ ^ 2 := by
  have h : re ⟪(∑ i, ((c i : 𝕜) * ⟪u i, z⟫_𝕜) • u i), z⟫_𝕜 = re ⟪z, z⟫_𝕜 := by
    rw [hdec z]
  rw [sum_inner, map_sum, inner_self_eq_norm_sq] at h
  rw [← h]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [inner_smul_left, map_mul (starRingEnd 𝕜), RCLike.conj_ofReal, mul_assoc, RCLike.conj_mul,
    ← RCLike.ofReal_pow, RCLike.re_ofReal_mul, RCLike.ofReal_re]

/-- Parseval on the standard basis: `∑ⱼ ‖⟪w, eⱼ⟫‖² = ‖w‖²`. -/
private lemma sum_inner_single_sq (w : EuclideanSpace 𝕜 (Fin k)) :
    ∑ j, ‖⟪w, EuclideanSpace.single j (1 : 𝕜)⟫_𝕜‖ ^ 2 = ‖w‖ ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [EuclideanSpace.inner_single_right, one_mul, RCLike.norm_conj]

/-- **Weights of a decomposition of identity sum to the dimension.** If
`∑ᵢ ((cᵢ:𝕜) · ⟪uᵢ, x⟫) • uᵢ = x` and each `‖uᵢ‖ = 1`, then `∑ᵢ cᵢ = k`. -/
lemma sum_weight_eq {N : ℕ} (c : Fin N → ℝ) (u : Fin N → EuclideanSpace 𝕜 (Fin k))
    (hdec : ∀ x, ∑ i, ((c i : 𝕜) * ⟪u i, x⟫_𝕜) • u i = x) (hu : ∀ i, ‖u i‖ = 1) :
    ∑ i, c i = (k : ℝ) := by
  have hpars : ∀ i, ∑ j, ‖⟪u i, EuclideanSpace.single j (1 : 𝕜)⟫_𝕜‖ ^ 2 = 1 := fun i => by
    rw [sum_inner_single_sq, hu i, one_pow]
  have hone : ∀ j : Fin k, ∑ i, c i * ‖⟪u i, EuclideanSpace.single j (1 : 𝕜)⟫_𝕜‖ ^ 2 = 1 :=
    fun j => by
      rw [sum_weight_inner_sq c u hdec (EuclideanSpace.single j (1 : 𝕜)), PiLp.norm_single]
      simp
  calc ∑ i, c i = ∑ i, c i * ∑ j, ‖⟪u i, EuclideanSpace.single j (1 : 𝕜)⟫_𝕜‖ ^ 2 := by
        refine Finset.sum_congr rfl fun i _ => ?_; rw [hpars i, mul_one]
    _ = ∑ i, ∑ j, c i * ‖⟪u i, EuclideanSpace.single j (1 : 𝕜)⟫_𝕜‖ ^ 2 := by
        refine Finset.sum_congr rfl fun i _ => Finset.mul_sum _ _ _
    _ = ∑ j, ∑ i, c i * ‖⟪u i, EuclideanSpace.single j (1 : 𝕜)⟫_𝕜‖ ^ 2 := Finset.sum_comm
    _ = ∑ _j : Fin k, (1 : ℝ) := Finset.sum_congr rfl fun j _ => hone j
    _ = (k : ℝ) := by simp

/-- **John decomposition of identity** — the classical core of John's ellipsoid
theorem (stated here as `sorry`; the remaining hard input).

In John position — the identity is a maximal-volume feasible operator for the body
seminorm `q` (`q u ≤ ‖u‖`, and `‖det S‖ ≤ 1` for every feasible `S`) — the
identity is a positive combination of the rank-one projections onto contact
points, with weights summing to the dimension `k`:
`∑ᵢ ((cᵢ:𝕜) · ⟪uᵢ, x⟫) • uᵢ = x`, with `uᵢ ∈ Contact q`, `cᵢ ≥ 0`, `∑ᵢ cᵢ = k`.

Classical proof (not yet formalised — no Mathlib scaffolding for the analytic
step): were `k⁻¹ • id ∉ convexHull 𝕜 {rankOneSA u : u ∈ Contact q}` — a compact
convex set of operators — `geometric_hahn_banach` would produce a self-adjoint `H`
with `re ⟪H u, u⟫ ≤ tr H` violated on all contacts; then `id ↝ id + t·H` stays
feasible for small `t > 0` (the delicate compactness / subdifferential argument)
while `‖det (id + tH)‖ > 1`, contradicting maximality. `Carathéodory` finally
turns membership of the convex hull into the finite positive combination. -/
theorem john_decomposition (q : Seminorm 𝕜 (EuclideanSpace 𝕜 (Fin k)))
    (hq : Continuous q) (hq1 : ∀ u, q u ≤ ‖u‖)
    (hmax : ∀ S ∈ Feasible q, ‖S.det‖ ≤ 1) :
    ∃ (N : ℕ) (u : Fin N → EuclideanSpace 𝕜 (Fin k)) (c : Fin N → ℝ),
      (∀ i, u i ∈ Contact q) ∧ (∀ i, 0 ≤ c i) ∧ (∑ i, c i = (k : ℝ)) ∧
      (∀ x, ∑ i, ((c i : 𝕜) * ⟪u i, x⟫_𝕜) • u i = x) := by
  sorry

/-- **Weighted Cauchy–Schwarz for a decomposition of identity** (the analytic
heart of the Kadets–Snobar estimate). If `∑ᵢ ((cᵢ:𝕜)·⟪uᵢ,x⟫)•uᵢ = x` and
`cᵢ ≥ 0`, then for any scalars `aᵢ`, `‖∑ᵢ ((cᵢ:𝕜)·aᵢ)•uᵢ‖ ≤ √(∑ᵢ cᵢ·‖aᵢ‖²)`. -/
lemma norm_sum_weight_smul_le {N : ℕ} (c : Fin N → ℝ)
    (u : Fin N → EuclideanSpace 𝕜 (Fin k))
    (hdec : ∀ x, ∑ i, ((c i : 𝕜) * ⟪u i, x⟫_𝕜) • u i = x)
    (hc : ∀ i, 0 ≤ c i) (a : Fin N → 𝕜) :
    ‖∑ i, ((c i : 𝕜) * a i) • u i‖ ≤ Real.sqrt (∑ i, c i * ‖a i‖ ^ 2) := by
  set w := ∑ i, ((c i : 𝕜) * a i) • u i with hw
  have hB : 0 ≤ ∑ i, c i * ‖a i‖ ^ 2 :=
    Finset.sum_nonneg fun i _ => mul_nonneg (hc i) (sq_nonneg _)
  -- `‖w‖² = re ⟪w, w⟫ ≤ ∑ᵢ cᵢ ‖aᵢ‖ ‖⟪uᵢ, w⟫‖`.
  have hww : ‖w‖ ^ 2 ≤ ∑ i, c i * (‖a i‖ * ‖⟪u i, w⟫_𝕜‖) := by
    rw [← inner_self_eq_norm_sq (𝕜 := 𝕜) w]
    nth_rewrite 1 [hw]
    rw [sum_inner, map_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [inner_smul_left, map_mul (starRingEnd 𝕜), RCLike.conj_ofReal, mul_assoc,
      RCLike.re_ofReal_mul]
    refine mul_le_mul_of_nonneg_left ?_ (hc i)
    calc re (conj (a i) * ⟪u i, w⟫_𝕜) ≤ ‖conj (a i) * ⟪u i, w⟫_𝕜‖ := RCLike.re_le_norm _
      _ = ‖a i‖ * ‖⟪u i, w⟫_𝕜‖ := by rw [norm_mul, RCLike.norm_conj]
  -- Weighted Cauchy–Schwarz on the reals, then `∑ᵢ cᵢ ‖⟪uᵢ,w⟫‖² = ‖w‖²`.
  have hCS : (∑ i, c i * (‖a i‖ * ‖⟪u i, w⟫_𝕜‖)) ^ 2
      ≤ (∑ i, c i * ‖a i‖ ^ 2) * (∑ i, c i * ‖⟪u i, w⟫_𝕜‖ ^ 2) := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
      (fun i => Real.sqrt (c i) * ‖a i‖) (fun i => Real.sqrt (c i) * ‖⟪u i, w⟫_𝕜‖)
    have e1 : ∀ i, Real.sqrt (c i) * ‖a i‖ * (Real.sqrt (c i) * ‖⟪u i, w⟫_𝕜‖)
        = c i * (‖a i‖ * ‖⟪u i, w⟫_𝕜‖) := fun i => by
      rw [mul_mul_mul_comm, Real.mul_self_sqrt (hc i)]
    have e2 : ∀ i, (Real.sqrt (c i) * ‖a i‖) ^ 2 = c i * ‖a i‖ ^ 2 := fun i => by
      rw [mul_pow, Real.sq_sqrt (hc i)]
    have e3 : ∀ i, (Real.sqrt (c i) * ‖⟪u i, w⟫_𝕜‖) ^ 2 = c i * ‖⟪u i, w⟫_𝕜‖ ^ 2 := fun i => by
      rw [mul_pow, Real.sq_sqrt (hc i)]
    simpa only [e1, e2, e3] using h
  rw [sum_weight_inner_sq c u hdec w] at hCS
  rcases eq_or_lt_of_le (norm_nonneg w) with h0 | hpos
  · rw [← h0]; exact Real.sqrt_nonneg _
  · have ht : (0 : ℝ) < ‖w‖ ^ 2 := by positivity
    have hle : ‖w‖ ^ 2 ≤ ∑ i, c i * ‖a i‖ ^ 2 := by
      refine le_of_mul_le_mul_right ?_ ht
      calc ‖w‖ ^ 2 * ‖w‖ ^ 2 = (‖w‖ ^ 2) ^ 2 := (pow_two _).symm
        _ ≤ (∑ i, c i * (‖a i‖ * ‖⟪u i, w⟫_𝕜‖)) ^ 2 := by
            apply pow_le_pow_left₀ (by positivity) hww
        _ ≤ (∑ i, c i * ‖a i‖ ^ 2) * ‖w‖ ^ 2 := hCS
    calc ‖w‖ = Real.sqrt (‖w‖ ^ 2) := (Real.sqrt_sq (norm_nonneg w)).symm
      _ ≤ Real.sqrt (∑ i, c i * ‖a i‖ ^ 2) := Real.sqrt_le_sqrt hle

/-- **Kadets–Snobar** (modulo `john_decomposition`). Every finite-dimensional
subspace `V` of a normed `𝕜`-space `Y` is the range of a bounded projection
`P : Y →L[𝕜] Y` with `‖P‖ ≤ √(dim V)`.

The proof puts `V` in John position: transport the Euclidean structure of
`𝕜^{dim V}` to `V` through the maximal-volume ellipsoid `M` (built from the John
decomposition of identity `∑ᵢ cᵢ uᵢ⊗uᵢ = id`). The contact points `uᵢ` give unit
vectors `vᵢ = M uᵢ ∈ V` and functionals `φᵢ = ⟪uᵢ, M⁻¹ ·⟫ ∈ V*` of norm `≤ 1`,
which Hahn–Banach (`exists_extension_norm_eq`) extends to `gᵢ ∈ Y*` without
increasing the norm. Then `P = ∑ᵢ cᵢ · gᵢ ⊗ vᵢ` is the identity on `V` (so it is
a projection onto `V`), and the weighted Cauchy–Schwarz estimate
`norm_sum_weight_smul_le` together with `∑ᵢ cᵢ = dim V` yields `‖P‖ ≤ √(dim V)`. -/
theorem exists_projection {Y : Type u} [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    (V : Submodule 𝕜 Y) [FiniteDimensional 𝕜 V] :
    ∃ P : Y →L[𝕜] Y, P.comp P = P ∧
      LinearMap.range (P : Y →ₗ[𝕜] Y) = V ∧ ‖P‖ ≤ Real.sqrt (Module.finrank 𝕜 V) := by
  classical
  set k := Module.finrank 𝕜 V with hk
  rcases Nat.eq_zero_or_pos k with hk0 | hkpos
  · -- `V = ⊥`: the zero map works.
    refine ⟨0, by simp, ?_, ?_⟩
    · have hV : V = ⊥ := Submodule.finrank_eq_zero.mp (hk.symm.trans hk0)
      rw [hV]; simp
    · rw [hk0]; simp
  -- From now on `0 < k`.
  -- A continuous linear equivalence `𝕜^k ≃L V` (both have dimension `k`).
  have hEfin : Module.finrank 𝕜 (EuclideanSpace 𝕜 (Fin k)) = k := by
    rw [(WithLp.linearEquiv 2 𝕜 (Fin k → 𝕜)).finrank_eq, Module.finrank_pi 𝕜, Fintype.card_fin]
  set L : EuclideanSpace 𝕜 (Fin k) ≃L[𝕜] V :=
    ContinuousLinearEquiv.ofFinrankEq (hEfin.trans hk) with hLdef
  -- The body seminorm on `𝕜^k`: `p x = ‖L x‖`, equivalent to the Euclidean norm.
  set p : Seminorm 𝕜 (EuclideanSpace 𝕜 (Fin k)) :=
    (normSeminorm 𝕜 Y).comp (V.subtypeL.comp (L : EuclideanSpace 𝕜 (Fin k) →L[𝕜] V)).toLinearMap
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
  set C : ℝ := ‖(L : EuclideanSpace 𝕜 (Fin k) →L[𝕜] V)‖ with hC
  have hup : ∀ x, p x ≤ C * ‖x‖ := fun x => by
    rw [hp_apply]
    exact (L : EuclideanSpace 𝕜 (Fin k) →L[𝕜] V).le_opNorm x
  -- Lower bound `‖L.symm‖⁻¹ ‖x‖ ≤ p x`; the constant is positive since `0 < k`.
  set D : ℝ := ‖(L.symm : V →L[𝕜] EuclideanSpace 𝕜 (Fin k))‖ with hD
  have hDpos : 0 < D := by
    have hne : (L.symm : V →L[𝕜] EuclideanSpace 𝕜 (Fin k)) ≠ 0 := by
      intro hzero
      have he1 : ‖(EuclideanSpace.single (⟨0, hkpos⟩ : Fin k) (1 : 𝕜))‖ = 1 := by
        rw [PiLp.norm_single, norm_one]
      have hcontra : (EuclideanSpace.single (⟨0, hkpos⟩ : Fin k) (1 : 𝕜)) = 0 := by
        have h2 : (L.symm : V →L[𝕜] EuclideanSpace 𝕜 (Fin k))
            (L (EuclideanSpace.single (⟨0, hkpos⟩ : Fin k) (1 : 𝕜))) = 0 := by
          rw [hzero]; rfl
        rwa [ContinuousLinearEquiv.coe_coe, L.symm_apply_apply] at h2
      rw [hcontra, norm_zero] at he1
      exact one_ne_zero he1.symm
    rw [hD]
    rcases eq_or_lt_of_le (norm_nonneg (L.symm : V →L[𝕜] EuclideanSpace 𝕜 (Fin k))) with h | h
    · exact absurd ((ContinuousLinearMap.opNorm_zero_iff _).mp h.symm) hne
    · exact h
  have hlo : ∀ x, D⁻¹ * ‖x‖ ≤ p x := fun x => by
    have hbound : ‖x‖ ≤ D * p x := by
      rw [hp_apply]
      have e : ‖x‖ = ‖(L.symm : V →L[𝕜] EuclideanSpace 𝕜 (Fin k)) (L x)‖ := by
        rw [ContinuousLinearEquiv.coe_coe, L.symm_apply_apply]
      rw [e]
      calc ‖(L.symm : V →L[𝕜] EuclideanSpace 𝕜 (Fin k)) (L x)‖
          ≤ D * ‖L x‖ := (L.symm : V →L[𝕜] EuclideanSpace 𝕜 (Fin k)).le_opNorm (L x)
        _ = D * ‖((L x : V) : Y)‖ := by rw [Submodule.norm_coe]
    have := mul_le_mul_of_nonneg_left hbound (le_of_lt (inv_pos.mpr hDpos))
    rwa [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hDpos), one_mul] at this
  -- The maximal-volume ellipsoid `T₀` and the John-position seminorm `q = p ∘ T₀`.
  obtain ⟨T₀, hT₀feas, hT₀det, hT₀max⟩ :=
    exists_maxVolume p hpc (inv_pos.mpr hDpos) hlo hup
  set q : Seminorm 𝕜 (EuclideanSpace 𝕜 (Fin k)) := p.comp T₀.toLinearMap with hqdef
  have hq1 : ∀ u, q u ≤ ‖u‖ := fun u => by
    rw [hqdef, Seminorm.comp_apply]; exact hT₀feas u
  have hqc : Continuous q := by
    rw [hqdef]; exact hpc.comp T₀.continuous
  have hqmax : ∀ S ∈ Feasible q, ‖S.det‖ ≤ 1 := fun S hS => by
    have hTS : T₀.comp S ∈ Feasible p := fun u => by
      have h := hS u
      rw [hqdef, Seminorm.comp_apply, ContinuousLinearMap.coe_coe] at h
      simpa [ContinuousLinearMap.comp_apply] using h
    have hdc : (T₀.comp S).det = T₀.det * S.det := by
      simp only [ContinuousLinearMap.det, ContinuousLinearMap.coe_comp, LinearMap.det_comp]
    have hle := hT₀max (T₀.comp S) hTS
    rw [hdc, norm_mul] at hle
    exact (mul_le_iff_le_one_right (norm_pos_iff.mpr hT₀det)).mp hle
  -- The composite equivalence `M = L ∘ T₀ : 𝕜^k ≃L V`; `‖M z‖ = q z`.
  set T₀e : EuclideanSpace 𝕜 (Fin k) ≃L[𝕜] EuclideanSpace 𝕜 (Fin k) :=
    T₀.toContinuousLinearEquivOfDetNeZero hT₀det with hT₀e
  set M : EuclideanSpace 𝕜 (Fin k) ≃L[𝕜] V := T₀e.trans L with hMdef
  have hMapply : ∀ z, M z = L (T₀ z) := fun z => by
    rw [hMdef, ContinuousLinearEquiv.trans_apply, hT₀e,
      ContinuousLinearMap.toContinuousLinearEquivOfDetNeZero_apply]
  have hqM : ∀ z, ‖(M z : Y)‖ = q z := fun z => by
    rw [hMapply, hqdef, Seminorm.comp_apply, ContinuousLinearMap.coe_coe, hp_apply]
  -- The John decomposition of identity in John position.
  obtain ⟨N, u, c, hcontact, hcnn, hcsum, hdec⟩ := john_decomposition q hqc hq1 hqmax
  -- Functionals `φ i = ⟪u i, M.symm ·⟫` on `V`, of norm `≤ 1`.
  set φ : Fin N → (V →L[𝕜] 𝕜) :=
    fun i => (innerSL 𝕜 (u i)).comp (M.symm : V →L[𝕜] EuclideanSpace 𝕜 (Fin k)) with hφ
  have hφapply : ∀ i (w : V), φ i w = ⟪u i, M.symm w⟫_𝕜 := fun i w => by
    simp only [hφ, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      innerSL_apply_apply]
  have hφnorm : ∀ i, ‖φ i‖ ≤ 1 := fun i => by
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun w => ?_
    rw [one_mul, hφapply]
    calc ‖⟪u i, M.symm w⟫_𝕜‖ = ‖⟪M.symm w, u i⟫_𝕜‖ := by
          rw [← inner_conj_symm (M.symm w) (u i), RCLike.norm_conj]
      _ ≤ q (M.symm w) := norm_inner_le_of_contact (hcontact i) (M.symm w)
      _ = ‖(M (M.symm w) : Y)‖ := (hqM (M.symm w)).symm
      _ = ‖w‖ := by rw [M.apply_symm_apply, Submodule.norm_coe]
  -- Hahn–Banach: extend each `φ i` to `g i ∈ Y*` without increasing the norm.
  choose g hg_ext hg_norm using fun i => exists_extension_norm_eq V (φ i)
  have hgnorm1 : ∀ i, ‖g i‖ ≤ 1 := fun i => (hg_norm i).trans_le (hφnorm i)
  -- The projection `P = ∑ᵢ cᵢ · g i ⊗ (M (u i))`.
  set P : Y →L[𝕜] Y := ∑ i, (c i : 𝕜) • ((g i).smulRight ((M (u i) : V) : Y)) with hP
  have hPapply : ∀ y, P y = ∑ i, ((c i : 𝕜) * g i y) • ((M (u i) : Y)) := fun y => by
    rw [hP]
    simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.smulRight_apply, smul_smul]
  have hPmem : ∀ y, P y ∈ V := fun y => by
    rw [hPapply]
    exact V.sum_mem fun i _ => V.smul_mem _ (M (u i)).2
  -- `P` is the identity on `V`.
  have hPV : ∀ w : V, P (w : Y) = (w : Y) := fun w => by
    rw [hPapply]
    have hgi : ∀ i, g i (w : Y) = ⟪u i, M.symm w⟫_𝕜 := fun i => by rw [hg_ext i w, hφapply i w]
    simp only [hgi]
    have hpull : ((M (∑ i, ((c i : 𝕜) * ⟪u i, M.symm w⟫_𝕜) • u i) : V) : Y)
        = ∑ i, ((c i : 𝕜) * ⟪u i, M.symm w⟫_𝕜) • ((M (u i) : V) : Y) := by
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
    have hpull : ((M (∑ i, ((c i : 𝕜) * g i y) • u i) : V) : Y)
        = ∑ i, ((c i : 𝕜) * g i y) • ((M (u i) : V) : Y) := by
      rw [map_sum, Submodule.coe_sum]
      exact Finset.sum_congr rfl fun i _ => by rw [map_smul, Submodule.coe_smul]
    have hPyeq : P y = ((M (∑ i, ((c i : 𝕜) * g i y) • u i) : V) : Y) := by rw [hPapply, hpull]
    have hb : ∑ i, c i * ‖g i y‖ ^ 2 ≤ (k : ℝ) * ‖y‖ ^ 2 := by
      have hstep : ∀ i, c i * ‖g i y‖ ^ 2 ≤ c i * ‖y‖ ^ 2 := fun i => by
        apply mul_le_mul_of_nonneg_left _ (hcnn i)
        calc ‖g i y‖ ^ 2 ≤ (‖g i‖ * ‖y‖) ^ 2 := by
              apply pow_le_pow_left₀ (norm_nonneg _) ((g i).le_opNorm y)
          _ ≤ (1 * ‖y‖) ^ 2 := by
              apply pow_le_pow_left₀ (by positivity)
              exact mul_le_mul_of_nonneg_right (hgnorm1 i) (norm_nonneg _)
          _ = ‖y‖ ^ 2 := by rw [one_mul]
      calc ∑ i, c i * ‖g i y‖ ^ 2 ≤ ∑ i, c i * ‖y‖ ^ 2 := Finset.sum_le_sum fun i _ => hstep i
        _ = (∑ i, c i) * ‖y‖ ^ 2 := (Finset.sum_mul _ _ _).symm
        _ = (k : ℝ) * ‖y‖ ^ 2 := by rw [hcsum]
    calc ‖P y‖ = q (∑ i, ((c i : 𝕜) * g i y) • u i) := by rw [hPyeq, hqM]
      _ ≤ ‖∑ i, ((c i : 𝕜) * g i y) • u i‖ := hq1 _
      _ ≤ Real.sqrt (∑ i, c i * ‖g i y‖ ^ 2) :=
          norm_sum_weight_smul_le c u hdec hcnn (fun i => g i y)
      _ ≤ Real.sqrt ((k : ℝ) * ‖y‖ ^ 2) := Real.sqrt_le_sqrt hb
      _ = Real.sqrt (k : ℝ) * ‖y‖ := by
          rw [Real.sqrt_mul (Nat.cast_nonneg k), Real.sqrt_sq (norm_nonneg _)]

set_option maxHeartbeats 1000000 in
/-- **Garling–Gordon, ε-form** (modulo `john_decomposition`). Every closed
subspace `M` of a normed `𝕜`-space `X` with finite-dimensional quotient is the
kernel of a bounded projection `P : X →L[𝕜] X` with
`‖P‖ ≤ √(codim M) + ε`, for every `ε > 0`.

This is the dual of `exists_projection`, run in the finite-dimensional dual
`D = (X ⧸ M)*` (so no dual of `X` is needed). John position of the unit ball of
`D` gives contact points `uᵢ` and weights `cᵢ` with `∑ᵢ cᵢ = codim M`; the
`uᵢ` become unit functionals `fᵢ = Φ uᵢ ∈ D` on the quotient, and the contact
supports become norm-`≤ 1` functionals on `D`, i.e. — since `X ⧸ M` is
finite-dimensional, hence isometrically reflexive
(`NormedSpace.inclusionInDoubleDualLi`) — vectors `wᵢ ∈ X ⧸ M` with `‖wᵢ‖ ≤ 1`.
Lifting each `wᵢ` to a representative `xᵢ ∈ X` with `‖xᵢ‖ < 1 + ε'`
(`Submodule.Quotient.norm_mk_lt` — the quotient norm is an infimum; this is the
sole source of the `ε`), the operator `P y = ∑ᵢ cᵢ · fᵢ(π y) · xᵢ` satisfies
`π ∘ P = π` (via the decomposition of identity and the Riesz representation on
the Euclidean model), hence is a projection with kernel `M`; Cauchy–Schwarz and
the quadratic identity `sum_weight_inner_sq` give `‖P‖ ≤ (1 + ε')·√(codim M)`. -/
theorem exists_projection_ker {X : Type u} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    (M : Submodule 𝕜 X) [IsClosed (M : Set X)] [FiniteDimensional 𝕜 (X ⧸ M)]
    {ε : ℝ} (hε : 0 < ε) :
    ∃ P : X →L[𝕜] X, P.comp P = P ∧ LinearMap.ker (P : X →ₗ[𝕜] X) = M ∧
      ‖P‖ ≤ Real.sqrt (Module.finrank 𝕜 (X ⧸ M)) + ε := by
  classical
  set k := Module.finrank 𝕜 (X ⧸ M) with hk
  rcases Nat.eq_zero_or_pos k with hk0 | hkpos
  · -- `codim M = 0`: the quotient is trivial, `M = ⊤`, and `P = 0` works.
    have hsub : Subsingleton (X ⧸ M) :=
      Module.finrank_zero_iff.mp (hk.symm.trans hk0)
    have hM : M = ⊤ := by
      ext x0
      simp only [Submodule.mem_top, iff_true]
      have := Subsingleton.elim (Submodule.Quotient.mk x0 : X ⧸ M) 0
      exact (Submodule.Quotient.mk_eq_zero M).mp this
    refine ⟨0, by simp, ?_, ?_⟩
    · rw [hM]; simp [LinearMap.ker_zero]
    · simp only [norm_zero]; positivity
  -- From now on `0 < k`. The finite-dimensional dual `D := (X ⧸ M)*`.
  have hEfin : Module.finrank 𝕜 (EuclideanSpace 𝕜 (Fin k)) = k := by
    rw [(WithLp.linearEquiv 2 𝕜 (Fin k → 𝕜)).finrank_eq, Module.finrank_pi 𝕜, Fintype.card_fin]
  haveI hDfin : FiniteDimensional 𝕜 (StrongDual 𝕜 (X ⧸ M)) :=
    Module.Finite.equiv
      (LinearMap.toContinuousLinearMap : ((X ⧸ M) →ₗ[𝕜] 𝕜) ≃ₗ[𝕜] ((X ⧸ M) →L[𝕜] 𝕜))
  have hkD : Module.finrank 𝕜 (StrongDual 𝕜 (X ⧸ M)) = k := by
    rw [← (LinearMap.toContinuousLinearMap :
          ((X ⧸ M) →ₗ[𝕜] 𝕜) ≃ₗ[𝕜] ((X ⧸ M) →L[𝕜] 𝕜)).finrank_eq]
    exact (Subspace.dual_finrank_eq (K := 𝕜) (V := X ⧸ M)).trans hk.symm
  -- A continuous linear equivalence `𝕜^k ≃L D`.
  set L : EuclideanSpace 𝕜 (Fin k) ≃L[𝕜] StrongDual 𝕜 (X ⧸ M) :=
    ContinuousLinearEquiv.ofFinrankEq (hEfin.trans hkD.symm) with hLdef
  -- The body seminorm on `𝕜^k`: `p x = ‖L x‖`, equivalent to the Euclidean norm.
  set p : Seminorm 𝕜 (EuclideanSpace 𝕜 (Fin k)) :=
    (normSeminorm 𝕜 (StrongDual 𝕜 (X ⧸ M))).comp
      (L : EuclideanSpace 𝕜 (Fin k) →L[𝕜] StrongDual 𝕜 (X ⧸ M)).toLinearMap with hpdef
  have hp_apply : ∀ x, p x = ‖L x‖ := fun x => by
    simp only [hpdef, Seminorm.comp_apply, coe_normSeminorm, ContinuousLinearMap.coe_coe,
      ContinuousLinearEquiv.coe_coe]
  have hpc : Continuous p := by
    refine (continuous_norm.comp L.continuous).congr fun x => ?_
    exact (hp_apply x).symm
  -- Norm equivalence constants, as for `exists_projection`.
  set C : ℝ := ‖(L : EuclideanSpace 𝕜 (Fin k) →L[𝕜] StrongDual 𝕜 (X ⧸ M))‖ with hC
  have hup : ∀ x, p x ≤ C * ‖x‖ := fun x => by
    rw [hp_apply]
    exact (L : EuclideanSpace 𝕜 (Fin k) →L[𝕜] StrongDual 𝕜 (X ⧸ M)).le_opNorm x
  set D0 : ℝ := ‖(L.symm : StrongDual 𝕜 (X ⧸ M) →L[𝕜] EuclideanSpace 𝕜 (Fin k))‖ with hD0
  have hD0pos : 0 < D0 := by
    have hne : (L.symm : StrongDual 𝕜 (X ⧸ M) →L[𝕜] EuclideanSpace 𝕜 (Fin k)) ≠ 0 := by
      intro hzero
      have he1 : ‖(EuclideanSpace.single (⟨0, hkpos⟩ : Fin k) (1 : 𝕜))‖ = 1 := by
        rw [PiLp.norm_single, norm_one]
      have hcontra : (EuclideanSpace.single (⟨0, hkpos⟩ : Fin k) (1 : 𝕜)) = 0 := by
        have h2 : (L.symm : StrongDual 𝕜 (X ⧸ M) →L[𝕜] EuclideanSpace 𝕜 (Fin k))
            (L (EuclideanSpace.single (⟨0, hkpos⟩ : Fin k) (1 : 𝕜))) = 0 := by
          rw [hzero]; rfl
        rwa [ContinuousLinearEquiv.coe_coe, L.symm_apply_apply] at h2
      rw [hcontra, norm_zero] at he1
      exact one_ne_zero he1.symm
    rw [hD0]
    rcases eq_or_lt_of_le (norm_nonneg
        (L.symm : StrongDual 𝕜 (X ⧸ M) →L[𝕜] EuclideanSpace 𝕜 (Fin k))) with h | h
    · exact absurd ((ContinuousLinearMap.opNorm_zero_iff _).mp h.symm) hne
    · exact h
  have hlo : ∀ x, D0⁻¹ * ‖x‖ ≤ p x := fun x => by
    have hbound : ‖x‖ ≤ D0 * p x := by
      rw [hp_apply]
      have e : ‖x‖ = ‖(L.symm : StrongDual 𝕜 (X ⧸ M) →L[𝕜] EuclideanSpace 𝕜 (Fin k)) (L x)‖ := by
        rw [ContinuousLinearEquiv.coe_coe, L.symm_apply_apply]
      rw [e]
      exact (L.symm : StrongDual 𝕜 (X ⧸ M) →L[𝕜] EuclideanSpace 𝕜 (Fin k)).le_opNorm (L x)
    have := mul_le_mul_of_nonneg_left hbound (le_of_lt (inv_pos.mpr hD0pos))
    rwa [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hD0pos), one_mul] at this
  -- The maximal-volume ellipsoid `T₀` and the John-position seminorm `q = p ∘ T₀`.
  obtain ⟨T₀, hT₀feas, hT₀det, hT₀max⟩ :=
    exists_maxVolume p hpc (inv_pos.mpr hD0pos) hlo hup
  set q : Seminorm 𝕜 (EuclideanSpace 𝕜 (Fin k)) := p.comp T₀.toLinearMap with hqdef
  have hq1 : ∀ u, q u ≤ ‖u‖ := fun u => by
    rw [hqdef, Seminorm.comp_apply]; exact hT₀feas u
  have hqc : Continuous q := by
    rw [hqdef]; exact hpc.comp T₀.continuous
  have hqmax : ∀ S ∈ Feasible q, ‖S.det‖ ≤ 1 := fun S hS => by
    have hTS : T₀.comp S ∈ Feasible p := fun u => by
      have h := hS u
      rw [hqdef, Seminorm.comp_apply, ContinuousLinearMap.coe_coe] at h
      simpa [ContinuousLinearMap.comp_apply] using h
    have hdc : (T₀.comp S).det = T₀.det * S.det := by
      simp only [ContinuousLinearMap.det, ContinuousLinearMap.coe_comp, LinearMap.det_comp]
    have hle := hT₀max (T₀.comp S) hTS
    rw [hdc, norm_mul] at hle
    exact (mul_le_iff_le_one_right (norm_pos_iff.mpr hT₀det)).mp hle
  -- The composite equivalence `Φ = L ∘ T₀ : 𝕜^k ≃L D`; `‖Φ z‖ = q z`.
  set T₀e : EuclideanSpace 𝕜 (Fin k) ≃L[𝕜] EuclideanSpace 𝕜 (Fin k) :=
    T₀.toContinuousLinearEquivOfDetNeZero hT₀det with hT₀e
  set Φ : EuclideanSpace 𝕜 (Fin k) ≃L[𝕜] StrongDual 𝕜 (X ⧸ M) := T₀e.trans L with hΦdef
  have hΦapply : ∀ z, Φ z = L (T₀ z) := fun z => by
    rw [hΦdef, ContinuousLinearEquiv.trans_apply, hT₀e,
      ContinuousLinearMap.toContinuousLinearEquivOfDetNeZero_apply]
  have hqΦ : ∀ z, ‖Φ z‖ = q z := fun z => by
    rw [hΦapply, hqdef, Seminorm.comp_apply, ContinuousLinearMap.coe_coe, hp_apply]
  -- The John decomposition of identity in John position.
  obtain ⟨N, u, c, hcontact, hcnn, hcsum, hdec⟩ := john_decomposition q hqc hq1 hqmax
  -- Riesz representation: for `v ∈ X ⧸ M`, evaluation at `v` pulls back through
  -- `Φ` to an inner product against a vector `r` with `‖r‖ ≤ ‖v‖`.
  have hRiesz : ∀ v : X ⧸ M, ∃ r : EuclideanSpace 𝕜 (Fin k),
      (∀ z, ⟪r, z⟫_𝕜 = (Φ z) v) ∧ ‖r‖ ≤ ‖v‖ := by
    intro v
    set ℓ : EuclideanSpace 𝕜 (Fin k) →L[𝕜] 𝕜 :=
      ((NormedSpace.inclusionInDoubleDual 𝕜 (X ⧸ M)) v).comp
        (Φ : EuclideanSpace 𝕜 (Fin k) →L[𝕜] StrongDual 𝕜 (X ⧸ M)) with hℓ
    have hℓapply : ∀ z, ℓ z = (Φ z) v := fun z => rfl
    have hℓnorm : ‖ℓ‖ ≤ ‖v‖ := by
      refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg v) fun z => ?_
      rw [hℓapply z]
      calc ‖(Φ z) v‖ ≤ ‖Φ z‖ * ‖v‖ := (Φ z).le_opNorm v
        _ = q z * ‖v‖ := by rw [hqΦ]
        _ ≤ ‖z‖ * ‖v‖ := mul_le_mul_of_nonneg_right (hq1 z) (norm_nonneg v)
        _ = ‖v‖ * ‖z‖ := mul_comm _ _
    refine ⟨(InnerProductSpace.toDual 𝕜 (EuclideanSpace 𝕜 (Fin k))).symm ℓ, fun z => ?_, ?_⟩
    · rw [InnerProductSpace.toDual_symm_apply]
      exact hℓapply z
    · rw [LinearIsometryEquiv.norm_map]
      exact hℓnorm
  -- Represent each contact point `u i` by a vector `w i ∈ X ⧸ M`, solving the
  -- *single*-dual equation `Φ.flip (w i) = toDual (u i)`. `Φ.flip` is a linear
  -- isomorphism `X ⧸ M ≃ (𝕜^k)*` (all dimensions stay `k`), so this avoids the
  -- topological double dual entirely.
  set T : (X ⧸ M) →L[𝕜] StrongDual 𝕜 (EuclideanSpace 𝕜 (Fin k)) :=
    (Φ : EuclideanSpace 𝕜 (Fin k) →L[𝕜] StrongDual 𝕜 (X ⧸ M)).flip with hT
  have hTapply : ∀ (v : X ⧸ M) (z : EuclideanSpace 𝕜 (Fin k)), T v z = Φ z v :=
    fun v z => ContinuousLinearMap.flip_apply _ z v
  haveI : FiniteDimensional 𝕜 (StrongDual 𝕜 (EuclideanSpace 𝕜 (Fin k))) :=
    Module.Finite.equiv
      (LinearMap.toContinuousLinearMap :
        ((EuclideanSpace 𝕜 (Fin k)) →ₗ[𝕜] 𝕜) ≃ₗ[𝕜] ((EuclideanSpace 𝕜 (Fin k)) →L[𝕜] 𝕜))
  have hkSD : Module.finrank 𝕜 (StrongDual 𝕜 (EuclideanSpace 𝕜 (Fin k))) = k := by
    rw [← (LinearMap.toContinuousLinearMap :
          ((EuclideanSpace 𝕜 (Fin k)) →ₗ[𝕜] 𝕜) ≃ₗ[𝕜]
            ((EuclideanSpace 𝕜 (Fin k)) →L[𝕜] 𝕜)).finrank_eq,
        Subspace.dual_finrank_eq, hEfin]
  have hTinj : Function.Injective
      (T : (X ⧸ M) →ₗ[𝕜] StrongDual 𝕜 (EuclideanSpace 𝕜 (Fin k))) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    refine norm_le_zero_iff.mp (NormedSpace.norm_le_dual_bound 𝕜 v le_rfl fun g => ?_)
    have hgv : g v = 0 := by
      have h2 := hTapply v (Φ.symm g)
      rw [Φ.apply_symm_apply] at h2
      rw [← h2, show T v = 0 from hv]; rfl
    simp [hgv]
  have hTsurj : Function.Surjective
      (T : (X ⧸ M) →ₗ[𝕜] StrongDual 𝕜 (EuclideanSpace 𝕜 (Fin k))) := by
    have hrank : Module.finrank 𝕜 (LinearMap.range
        (T : (X ⧸ M) →ₗ[𝕜] StrongDual 𝕜 (EuclideanSpace 𝕜 (Fin k))))
        = Module.finrank 𝕜 (StrongDual 𝕜 (EuclideanSpace 𝕜 (Fin k))) := by
      rw [LinearMap.finrank_range_of_inj hTinj, hkSD, ← hk]
    rw [← LinearMap.range_eq_top]
    exact Submodule.eq_top_of_finrank_eq hrank
  choose w hw using fun i =>
    hTsurj (InnerProductSpace.toDual 𝕜 (EuclideanSpace 𝕜 (Fin k)) (u i))
  have hweval : ∀ i (g : StrongDual 𝕜 (X ⧸ M)), g (w i) = ⟪u i, Φ.symm g⟫_𝕜 := fun i g => by
    have h1 : T (w i) (Φ.symm g) = ⟪u i, Φ.symm g⟫_𝕜 := by
      rw [show T (w i) = InnerProductSpace.toDual 𝕜 (EuclideanSpace 𝕜 (Fin k)) (u i) from hw i,
        InnerProductSpace.toDual_apply_apply]
    rwa [hTapply (w i) (Φ.symm g), Φ.apply_symm_apply] at h1
  have hwnorm : ∀ i, ‖w i‖ ≤ 1 := fun i => by
    refine NormedSpace.norm_le_dual_bound 𝕜 (w i) zero_le_one fun g => ?_
    rw [one_mul, hweval i g]
    calc ‖⟪u i, Φ.symm g⟫_𝕜‖ = ‖⟪Φ.symm g, u i⟫_𝕜‖ := by
          rw [← inner_conj_symm (Φ.symm g) (u i), RCLike.norm_conj]
      _ ≤ q (Φ.symm g) := norm_inner_le_of_contact (hcontact i) (Φ.symm g)
      _ = ‖Φ (Φ.symm g)‖ := (hqΦ (Φ.symm g)).symm
      _ = ‖g‖ := by rw [Φ.apply_symm_apply]
  -- Lift each `w i` to a representative `x i ∈ X` with `‖x i‖ < 1 + ε'` — the
  -- sole source of the `ε`.
  set ε' : ℝ := ε / Real.sqrt k with hε'def
  have hsqrtk : 0 < Real.sqrt k := Real.sqrt_pos.mpr (by exact_mod_cast hkpos)
  have hε' : 0 < ε' := div_pos hε hsqrtk
  choose x hxmk hxnorm using fun i => Submodule.Quotient.norm_mk_lt (w i) hε'
  have hxbound : ∀ i, ‖x i‖ ≤ 1 + ε' := fun i => by
    linarith [hxnorm i, hwnorm i]
  -- The projection `P = ∑ᵢ cᵢ · (Φ uᵢ)(π ·) · xᵢ`.
  set π : X →L[𝕜] X ⧸ M := M.mkQL with hπdef
  have hπmk : ∀ y : X, π y = Submodule.Quotient.mk y := fun y => by
    rw [hπdef, Submodule.mkQL_apply, Submodule.mkQ_apply]
  have hπx : ∀ i, π (x i) = w i := fun i => by rw [hπmk]; exact hxmk i
  have hπle : ∀ y : X, ‖π y‖ ≤ ‖y‖ := fun y => by
    rw [hπmk]; exact Submodule.Quotient.norm_mk_le M y
  set P : X →L[𝕜] X := ∑ i, (c i : 𝕜) • (((Φ (u i)).comp π).smulRight (x i)) with hP
  have hPapply : ∀ y, P y = ∑ i, ((c i : 𝕜) * (Φ (u i)) (π y)) • x i := fun y => by
    rw [hP]
    simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.comp_apply, smul_smul]
  -- Key identity: the weighted combination of the `w i` reproduces every `v`.
  have hkey : ∀ v : X ⧸ M, (∑ i, ((c i : 𝕜) * (Φ (u i)) v) • w i) = v := by
    intro v
    obtain ⟨r, hr, _⟩ := hRiesz v
    apply (NormedSpace.inclusionInDoubleDualLi (E := X ⧸ M) 𝕜).injective
    apply ContinuousLinearMap.ext
    intro g
    have hLHS : (NormedSpace.inclusionInDoubleDualLi (E := X ⧸ M) 𝕜)
        (∑ i, ((c i : 𝕜) * (Φ (u i)) v) • w i) g
        = ∑ i, ((c i : 𝕜) * (Φ (u i)) v) * g (w i) := by
      show g (∑ i, ((c i : 𝕜) * (Φ (u i)) v) • w i) = _
      rw [map_sum]
      exact Finset.sum_congr rfl fun i _ => by
        rw [map_smul, smul_eq_mul]
    have hRHS : (NormedSpace.inclusionInDoubleDualLi (E := X ⧸ M) 𝕜) v g = g v := rfl
    rw [hLHS, hRHS]
    -- Rewrite through the Riesz vector and the decomposition of identity.
    set z := Φ.symm g with hz
    have hgz : g = Φ z := by rw [hz, Φ.apply_symm_apply]
    calc ∑ i, ((c i : 𝕜) * (Φ (u i)) v) * g (w i)
        = ∑ i, (c i : 𝕜) * ⟪u i, z⟫_𝕜 * ⟪r, u i⟫_𝕜 := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [hweval i g, ← hz, hr (u i)]; ring
      _ = ⟪r, ∑ i, ((c i : 𝕜) * ⟪u i, z⟫_𝕜) • u i⟫_𝕜 := by
          rw [inner_sum]
          exact Finset.sum_congr rfl fun i _ => by
            rw [inner_smul_right]
      _ = ⟪r, z⟫_𝕜 := by rw [hdec z]
      _ = (Φ z) v := hr z
      _ = g v := by rw [← hgz]
  have hπP : ∀ y, π (P y) = π y := fun y => by
    have hsum : π (P y) = ∑ i, ((c i : 𝕜) * (Φ (u i)) (π y)) • w i := by
      rw [hPapply, map_sum]
      exact Finset.sum_congr rfl fun i _ => by rw [map_smul, hπx i]
    rw [hsum, hkey (π y)]
  refine ⟨P, ?_, ?_, ?_⟩
  · -- `P ∘ P = P`, since `π ∘ P = π`.
    ext y
    show P (P y) = P y
    rw [hPapply (P y), hπP y, ← hPapply y]
  · -- `ker P = M`.
    ext x0
    simp only [LinearMap.mem_ker, ContinuousLinearMap.coe_coe]
    constructor
    · intro hPx
      have h0 : π x0 = 0 := by rw [← hπP x0, hPx, map_zero]
      rw [hπmk] at h0
      exact (Submodule.Quotient.mk_eq_zero M).mp h0
    · intro hx0
      have h0 : π x0 = 0 := by rw [hπmk]; exact (Submodule.Quotient.mk_eq_zero M).mpr hx0
      rw [hPapply, h0]
      simp
  · -- `‖P‖ ≤ √k + ε`.
    have hbnd : (0 : ℝ) ≤ Real.sqrt k + ε := by positivity
    refine ContinuousLinearMap.opNorm_le_bound P hbnd fun y => ?_
    obtain ⟨r, hr, hrnorm⟩ := hRiesz (π y)
    -- `∑ᵢ cᵢ ‖fᵢ(πy)‖² = ‖r‖² ≤ ‖y‖²` via the quadratic identity.
    have hquad : ∑ i, c i * ‖(Φ (u i)) (π y)‖ ^ 2 ≤ ‖y‖ ^ 2 := by
      have h1 : ∀ i, ‖(Φ (u i)) (π y)‖ = ‖⟪u i, r⟫_𝕜‖ := fun i => by
        rw [← hr (u i), ← inner_conj_symm r (u i), RCLike.norm_conj]
      calc ∑ i, c i * ‖(Φ (u i)) (π y)‖ ^ 2
          = ∑ i, c i * ‖⟪u i, r⟫_𝕜‖ ^ 2 := by
            exact Finset.sum_congr rfl fun i _ => by rw [h1 i]
        _ = ‖r‖ ^ 2 := sum_weight_inner_sq c u hdec r
        _ ≤ ‖π y‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg r) hrnorm 2
        _ ≤ ‖y‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hπle y) 2
    -- Cauchy–Schwarz: `∑ᵢ cᵢ ‖fᵢ(πy)‖ ≤ √k · ‖y‖`.
    have hCS : ∑ i, c i * ‖(Φ (u i)) (π y)‖ ≤ Real.sqrt k * ‖y‖ := by
      have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
        (fun i => Real.sqrt (c i)) (fun i => Real.sqrt (c i) * ‖(Φ (u i)) (π y)‖)
      have e1 : ∀ i, Real.sqrt (c i) * (Real.sqrt (c i) * ‖(Φ (u i)) (π y)‖)
          = c i * ‖(Φ (u i)) (π y)‖ := fun i => by
        rw [← mul_assoc, Real.mul_self_sqrt (hcnn i)]
      have e2 : ∀ i, (Real.sqrt (c i)) ^ 2 = c i := fun i => Real.sq_sqrt (hcnn i)
      have e3 : ∀ i, (Real.sqrt (c i) * ‖(Φ (u i)) (π y)‖) ^ 2
          = c i * ‖(Φ (u i)) (π y)‖ ^ 2 := fun i => by
        rw [mul_pow, Real.sq_sqrt (hcnn i)]
      simp only [e1, e2, e3] at h
      -- `h : (∑ᵢ cᵢ‖fᵢ(πy)‖)² ≤ (∑ᵢ cᵢ) · ∑ᵢ cᵢ‖fᵢ(πy)‖²`
      have hA0 : 0 ≤ ∑ i, c i * ‖(Φ (u i)) (π y)‖ :=
        Finset.sum_nonneg fun i _ => mul_nonneg (hcnn i) (norm_nonneg _)
      have hupper : (∑ i, c i * ‖(Φ (u i)) (π y)‖) ^ 2 ≤ (k : ℝ) * ‖y‖ ^ 2 := by
        calc (∑ i, c i * ‖(Φ (u i)) (π y)‖) ^ 2
            ≤ (∑ i, c i) * ∑ i, c i * ‖(Φ (u i)) (π y)‖ ^ 2 := h
          _ = (k : ℝ) * ∑ i, c i * ‖(Φ (u i)) (π y)‖ ^ 2 := by rw [hcsum]
          _ ≤ (k : ℝ) * ‖y‖ ^ 2 :=
              mul_le_mul_of_nonneg_left hquad (Nat.cast_nonneg k)
      calc ∑ i, c i * ‖(Φ (u i)) (π y)‖
          = Real.sqrt ((∑ i, c i * ‖(Φ (u i)) (π y)‖) ^ 2) := (Real.sqrt_sq hA0).symm
        _ ≤ Real.sqrt ((k : ℝ) * ‖y‖ ^ 2) := Real.sqrt_le_sqrt hupper
        _ = Real.sqrt k * ‖y‖ := by
            rw [Real.sqrt_mul (Nat.cast_nonneg k), Real.sqrt_sq (norm_nonneg _)]
    -- Assemble.
    calc ‖P y‖ ≤ ∑ i, ‖((c i : 𝕜) * (Φ (u i)) (π y)) • x i‖ := by
          rw [hPapply]; exact norm_sum_le _ _
      _ = ∑ i, c i * ‖(Φ (u i)) (π y)‖ * ‖x i‖ := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [norm_smul, norm_mul, RCLike.norm_ofReal, abs_of_nonneg (hcnn i)]
      _ ≤ ∑ i, c i * ‖(Φ (u i)) (π y)‖ * (1 + ε') := by
          refine Finset.sum_le_sum fun i _ => ?_
          exact mul_le_mul_of_nonneg_left (hxbound i)
            (mul_nonneg (hcnn i) (norm_nonneg _))
      _ = (1 + ε') * ∑ i, c i * ‖(Φ (u i)) (π y)‖ := by
          rw [← Finset.sum_mul, mul_comm]
      _ ≤ (1 + ε') * (Real.sqrt k * ‖y‖) :=
          mul_le_mul_of_nonneg_left hCS (by positivity)
      _ = (Real.sqrt k + ε) * ‖y‖ := by
          rw [← mul_assoc, show (1 + ε') * Real.sqrt k = Real.sqrt k + ε from by
            rw [hε'def, add_mul, one_mul, div_mul_cancel₀ ε (ne_of_gt hsqrtk)]]

end John
