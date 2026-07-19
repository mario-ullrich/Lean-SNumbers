/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
import SNumbers.Gelfand
import SNumbers.Hilbert
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.MetricSpace.Sequences

/-!
# The identity `ℓ₁ → ℓ_∞` and order-optimality of the maximal difference theorem

The maximal difference theorem `max(cₙ, dₙ) ≤ e·(n+1)·hₙ` (see `SNumbers.MaxDifference`)
has an optimal linear factor `n+1`. The witness is the natural inclusion
`I : ℓ₁ → ℓ_∞`, for which

  `½ ≤ cₙ(I) ≤ 1`   and   `hₙ(I) = 1/(n+1)`,

so that `max(cₙ(I), dₙ(I)) / hₙ(I) ≍ n`. This file develops the pieces that do not
require Hilbert–Schmidt / little-Grothendieck machinery: the two Gelfand bounds and the
lower bound `hₙ(I) ≥ 1/(n+1)`. The matching upper bound `hₙ(I) ≤ 1/(n+1)` is deferred.

Here `ℓ₁ = lp (fun _ : ℕ => 𝕜) 1` and `ℓ_∞ = lp (fun _ : ℕ => 𝕜) ∞`, and `𝕜` is `RCLike`.
-/

open scoped ENNReal

namespace SNumbers.L1Linf

variable {𝕜 : Type*} [RCLike 𝕜]

instance : Fact ((1 : ℝ≥0∞) ≤ 1) := ⟨le_refl _⟩
instance : Fact ((1 : ℝ≥0∞) ≤ ∞) := ⟨le_top⟩

/-- `ℓ₁(ℕ; 𝕜)`, the space of absolutely summable scalar sequences. -/
abbrev L1 (𝕜 : Type*) [RCLike 𝕜] : Type _ := lp (fun _ : ℕ => 𝕜) 1

/-- `ℓ_∞(ℕ; 𝕜)`, the space of bounded scalar sequences. -/
abbrev Linf (𝕜 : Type*) [RCLike 𝕜] : Type _ := lp (fun _ : ℕ => 𝕜) ∞

/-- `‖x‖_∞ ≤ ‖x‖₁`: each coordinate is bounded by the `ℓ₁` norm. -/
lemma norm_coe_linf_le_norm_l1 (f : L1 𝕜) :
    ‖(lp.linearMapOfLE 𝕜 (fun _ : ℕ => 𝕜) (le_top) f : Linf 𝕜)‖ ≤ ‖f‖ := by
  refine lp.norm_le_of_forall_le (norm_nonneg f) (fun i => ?_)
  rw [lp.coe_linearMapOfLE_apply]
  exact lp.norm_apply_le_norm (by norm_num) f i

/-- The natural inclusion `I : ℓ₁ → ℓ_∞`, a contraction. -/
noncomputable def incl : L1 𝕜 →L[𝕜] Linf 𝕜 :=
  LinearMap.mkContinuous (lp.linearMapOfLE 𝕜 (fun _ : ℕ => 𝕜) le_top) 1 (fun f => by
    rw [one_mul]; exact norm_coe_linf_le_norm_l1 f)

@[simp] lemma incl_apply (f : L1 𝕜) (i : ℕ) :
    ((incl : L1 𝕜 →L[𝕜] Linf 𝕜) f) i = f i := rfl

lemma norm_incl_le : ‖(incl : L1 𝕜 →L[𝕜] Linf 𝕜)‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

/-! ## Basis vectors of `ℓ₁` -/

/-- The `i`-th standard basis vector `eᵢ = δᵢ` of `ℓ₁`. -/
noncomputable def e (i : ℕ) : L1 𝕜 := lp.single 1 i (1 : 𝕜)

@[simp] lemma e_apply_self (i : ℕ) : (e i : L1 𝕜) i = 1 :=
  lp.single_apply_self (E := fun _ : ℕ => 𝕜) 1 i (1 : 𝕜)

lemma e_apply_ne {i j : ℕ} (h : j ≠ i) : (e i : L1 𝕜) j = 0 :=
  lp.single_apply_ne (E := fun _ : ℕ => 𝕜) 1 i (1 : 𝕜) h

/-- `‖eᵢ‖₁ = 1`. -/
lemma norm_e (i : ℕ) : ‖(e i : L1 𝕜)‖ = 1 := by
  unfold e; rw [lp.norm_single (by norm_num : (0 : ℝ≥0∞) < 1), norm_one]

/-! ## `cₙ(I) ≤ 1` -/

lemma gelfand_le_one (n : ℕ) :
    gelfandNumber (incl : L1 𝕜 →L[𝕜] Linf 𝕜) n ≤ 1 :=
  (gelfandNumber_le_norm _ _).trans norm_incl_le

/-! ## `cₙ(I) ≥ ½`

For any closed subspace `N ⊆ ℓ₁` of codimension `≤ n`, the quotient `ℓ₁ ⧸ N` is finite
dimensional, so the bounded family `([eᵢ])ᵢ` of basis-vector classes has two members
arbitrarily close (Bolzano–Weierstrass). Lifting their difference back gives `x ∈ N` close to
`eᵢ − eᵢ'`, with `‖x‖₁ ≈ 2` but `‖I x‖_∞ ≈ 1`, forcing `‖I|_N‖ ≥ ½`. -/

lemma half_le_gelfandNumber (n : ℕ) :
    (1 : ℝ) / 2 ≤ gelfandNumber (incl : L1 𝕜 →L[𝕜] Linf 𝕜) n := by
  refine le_gelfandNumber (fun N hN_closed hN_rank => ?_)
  haveI : IsClosed ((N : Set (L1 𝕜))) := hN_closed
  haveI : FiniteDimensional 𝕜 (L1 𝕜 ⧸ N) :=
    Module.rank_lt_aleph0_iff.mp (lt_of_le_of_lt hN_rank (Cardinal.natCast_lt_aleph0))
  haveI : ProperSpace (L1 𝕜 ⧸ N) := FiniteDimensional.proper 𝕜 _
  set D : ℝ := deviationFromRestriction (incl : L1 𝕜 →L[𝕜] Linf 𝕜) N with hD
  have hD_nn : 0 ≤ D := deviationFromRestriction_nonneg _ _
  -- Operator-norm bound on the restriction: `‖I x‖ ≤ D · ‖x‖` for `x ∈ N`.
  have hopbound : ∀ x : L1 𝕜, x ∈ N →
      ‖(incl : L1 𝕜 →L[𝕜] Linf 𝕜) x‖ ≤ D * ‖x‖ := by
    intro x hx
    have h := ((incl : L1 𝕜 →L[𝕜] Linf 𝕜).comp N.subtypeL).le_opNorm (⟨x, hx⟩ : N)
    rwa [ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply] at h
  -- Key ratio estimate for every `ε' > 0`.
  have key : ∀ ε' : ℝ, 0 < ε' → 1 - 2 * ε' ≤ D * (2 + 2 * ε') := by
    intro ε' hε'
    set g : ℕ → L1 𝕜 ⧸ N := fun i => Submodule.Quotient.mk (e i) with hg
    have hg_bdd : ∀ i, g i ∈ Metric.closedBall (0 : L1 𝕜 ⧸ N) 1 := by
      intro i
      rw [Metric.mem_closedBall, dist_zero_right]
      calc ‖g i‖ ≤ ‖(e i : L1 𝕜)‖ := Submodule.Quotient.norm_mk_le N (e i)
        _ = 1 := norm_e i
    obtain ⟨a, -, φ, hφ_mono, hφ_tendsto⟩ :=
      tendsto_subseq_of_bounded Metric.isBounded_closedBall hg_bdd
    rw [Metric.tendsto_atTop] at hφ_tendsto
    obtain ⟨K, hK⟩ := hφ_tendsto (ε' / 2) (by positivity)
    have hi_ne : φ K ≠ φ (K + 1) := (hφ_mono (Nat.lt_succ_self K)).ne
    have hclose : dist (g (φ K)) (g (φ (K + 1))) < ε' := by
      calc dist (g (φ K)) (g (φ (K + 1)))
          ≤ dist (g (φ K)) a + dist a (g (φ (K + 1))) := dist_triangle _ _ _
        _ = dist (g (φ K)) a + dist (g (φ (K + 1))) a := by rw [dist_comm a]
        _ < ε' / 2 + ε' / 2 := add_lt_add (hK K (le_refl _)) (hK (K + 1) (Nat.le_succ _))
        _ = ε' := by ring
    set d : L1 𝕜 := e (φ K) - e (φ (K + 1)) with hd_def
    have hmk_small : ‖(Submodule.Quotient.mk d : L1 𝕜 ⧸ N)‖ < ε' := by
      have hmk_eq : (Submodule.Quotient.mk d : L1 𝕜 ⧸ N) = g (φ K) - g (φ (K + 1)) := by
        rw [hg, hd_def, Submodule.Quotient.mk_sub]
      rw [hmk_eq, ← dist_eq_norm]; exact hclose
    obtain ⟨y, hy_mk, hy_lt⟩ :=
      Submodule.Quotient.norm_mk_lt (Submodule.Quotient.mk d : L1 𝕜 ⧸ N) hε'
    set x : L1 𝕜 := d - y with hx_def
    have hx_mem : x ∈ N := by
      rw [← Submodule.Quotient.mk_eq_zero, hx_def, Submodule.Quotient.mk_sub, hy_mk, sub_self]
    have hy_2 : ‖y‖ < 2 * ε' := by linarith [hy_lt, hmk_small]
    have hx_l1 : ‖x‖ ≤ 2 + 2 * ε' := by
      calc ‖x‖ = ‖d - y‖ := by rw [hx_def]
        _ ≤ ‖d‖ + ‖y‖ := norm_sub_le _ _
        _ ≤ (‖(e (φ K) : L1 𝕜)‖ + ‖(e (φ (K + 1)) : L1 𝕜)‖) + ‖y‖ := by
            gcongr; rw [hd_def]; exact norm_sub_le _ _
        _ ≤ (1 + 1) + 2 * ε' := by rw [norm_e, norm_e]; linarith [hy_2]
        _ = 2 + 2 * ε' := by ring
    have hx_linf : 1 - 2 * ε' ≤ ‖(incl : L1 𝕜 →L[𝕜] Linf 𝕜) x‖ := by
      have hcoord : ((incl : L1 𝕜 →L[𝕜] Linf 𝕜) d) (φ K) = (1 : 𝕜) := by
        rw [incl_apply, hd_def]
        simp only [lp.coeFn_sub, Pi.sub_apply, e_apply_self, e_apply_ne hi_ne, sub_zero]
      have h_incl_d : (1 : ℝ) ≤ ‖(incl : L1 𝕜 →L[𝕜] Linf 𝕜) d‖ := by
        have hb := lp.norm_apply_le_norm (show (∞ : ℝ≥0∞) ≠ 0 by simp)
          ((incl : L1 𝕜 →L[𝕜] Linf 𝕜) d) (φ K)
        rwa [hcoord, norm_one] at hb
      have h_incl_y : ‖(incl : L1 𝕜 →L[𝕜] Linf 𝕜) y‖ ≤ ‖y‖ :=
        ((incl : L1 𝕜 →L[𝕜] Linf 𝕜).le_opNorm y).trans
          (mul_le_of_le_one_left (norm_nonneg y) norm_incl_le)
      have hxeq : (incl : L1 𝕜 →L[𝕜] Linf 𝕜) x
          = (incl : L1 𝕜 →L[𝕜] Linf 𝕜) d - (incl : L1 𝕜 →L[𝕜] Linf 𝕜) y := by
        rw [hx_def, map_sub]
      calc 1 - 2 * ε'
          ≤ ‖(incl : L1 𝕜 →L[𝕜] Linf 𝕜) d‖ - ‖(incl : L1 𝕜 →L[𝕜] Linf 𝕜) y‖ := by
            linarith [h_incl_d, h_incl_y, hy_2]
        _ ≤ ‖(incl : L1 𝕜 →L[𝕜] Linf 𝕜) d - (incl : L1 𝕜 →L[𝕜] Linf 𝕜) y‖ :=
            norm_sub_norm_le _ _
        _ = ‖(incl : L1 𝕜 →L[𝕜] Linf 𝕜) x‖ := by rw [hxeq]
    calc 1 - 2 * ε'
        ≤ ‖(incl : L1 𝕜 →L[𝕜] Linf 𝕜) x‖ := hx_linf
      _ ≤ D * ‖x‖ := hopbound x hx_mem
      _ ≤ D * (2 + 2 * ε') := mul_le_mul_of_nonneg_left hx_l1 hD_nn
  -- Let `ε' → 0`.
  show (1 : ℝ) / 2 ≤ D
  have h2D : (1 : ℝ) ≤ 2 * D := by
    refine le_of_forall_pos_le_add (fun δ hδ => ?_)
    have h1D : (0 : ℝ) < 1 + D := by linarith
    set ε' : ℝ := δ / (2 * (1 + D)) with hε'_def
    have hε'_pos : 0 < ε' := by positivity
    have hk := key ε' hε'_pos
    have hδeq : 2 * ε' * (1 + D) = δ := by
      rw [hε'_def]; field_simp
    nlinarith [hk, hδeq]
  linarith

/-! ## `hₙ(I) ≥ 1/(n+1)`

Auxiliary Cauchy–Schwarz bounds relating the `ℓ₁`/`ℓ₂` and `ℓ₂`/`ℓ_∞` norms of a
finite vector, both with the factor `√m`. -/

open scoped Finset in
/-- `∑ᵢ ‖vᵢ‖ ≤ √m · ‖v‖₂` on `ℓ₂ᵐ` (Cauchy–Schwarz against the all-ones vector). -/
lemma sum_norm_le_sqrt_mul_norm {m : ℕ} (v : EuclideanSpace 𝕜 (Fin m)) :
    ∑ i, ‖v i‖ ≤ Real.sqrt m * ‖v‖ := by
  have h := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun i : Fin m => ‖v i‖) (fun _ => (1 : ℝ))
  simp only [mul_one, one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one] at h
  rw [EuclideanSpace.norm_eq, mul_comm]
  exact h

/-! ### The factorization `id_{ℓ₂ᵐ} = proj∞ ∘ I ∘ emb1`

`hₙ(I) ≥ 1/(n+1)` follows from `1 ≤ hₙ(id_{ℓ₂ᵐ})` (`one_le_hilbertNumber_id`) and the
factorization `id_{ℓ₂ᵐ} = proj∞ ∘ I ∘ emb1` through `√m`-bounded maps
`emb1 : ℓ₂ᵐ → ℓ₁` and `proj∞ : ℓ_∞ → ℓ₂ᵐ`, via the Hilbert-number ideal property
`hilbertNumber_comp_comp_le`. -/

/-- `emb1 v = ∑_{i<m} single 1 i (vᵢ)`, the finite-support embedding `ℓ₂ᵐ → ℓ₁`. -/
noncomputable def emb1 (m : ℕ) : EuclideanSpace 𝕜 (Fin m) →L[𝕜] L1 𝕜 :=
  ∑ i : Fin m,
    (lp.singleContinuousLinearMap 𝕜 (fun _ : ℕ => 𝕜) 1 (i : ℕ)).comp (EuclideanSpace.proj i)

lemma emb1_apply (m : ℕ) (v : EuclideanSpace 𝕜 (Fin m)) :
    emb1 m v = ∑ i : Fin m, lp.single 1 (i : ℕ) (v i) := by
  simp only [emb1, sum_apply, ContinuousLinearMap.comp_apply,
    lp.singleContinuousLinearMap_apply, EuclideanSpace.coe_proj]

lemma norm_emb1_apply_le (m : ℕ) (v : EuclideanSpace 𝕜 (Fin m)) :
    ‖emb1 m v‖ ≤ Real.sqrt m * ‖v‖ := by
  have key : ‖(∑ i : Fin m, lp.single 1 (i : ℕ) (v i) : L1 𝕜)‖ ≤ Real.sqrt m * ‖v‖ := by
    refine (norm_sum_le _ _).trans ?_
    have hsum : ∑ i : Fin m, ‖(lp.single 1 (i : ℕ) (v i) : L1 𝕜)‖ = ∑ i : Fin m, ‖v i‖ :=
      Finset.sum_congr rfl fun i _ =>
        lp.norm_single (E := fun _ : ℕ => 𝕜) (show (0 : ℝ≥0∞) < 1 by norm_num) (i : ℕ) (v i)
    rw [hsum]
    exact sum_norm_le_sqrt_mul_norm v
  exact (congrArg Norm.norm (emb1_apply m v)).trans_le key

lemma norm_emb1_le (m : ℕ) : ‖(emb1 m : EuclideanSpace 𝕜 (Fin m) →L[𝕜] L1 𝕜)‖ ≤ Real.sqrt m :=
  ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) (norm_emb1_apply_le m)

/-- `proj∞ y = ∑_{i<m} yᵢ • eᵢ`, the finite coordinate projection `ℓ_∞ → ℓ₂ᵐ`. -/
noncomputable def projinf (m : ℕ) : Linf 𝕜 →L[𝕜] EuclideanSpace 𝕜 (Fin m) :=
  ∑ i : Fin m,
    (lp.evalCLM 𝕜 (fun _ : ℕ => 𝕜) ∞ (i : ℕ)).smulRight (EuclideanSpace.single i (1 : 𝕜))

lemma projinf_apply (m : ℕ) (y : Linf 𝕜) :
    (projinf m : Linf 𝕜 →L[𝕜] EuclideanSpace 𝕜 (Fin m)) y
      = ∑ i : Fin m, (y (i : ℕ)) • EuclideanSpace.single i (1 : 𝕜) := by
  simp only [projinf, sum_apply, ContinuousLinearMap.smulRight_apply,
    lp.evalCLM, LinearMap.mkContinuous_apply, lp.evalₗ_apply]

/-- Coordinate of `proj∞ y`: the `j`-th entry is `y j`. -/
lemma projinf_coord (m : ℕ) (y : Linf 𝕜) (j : Fin m) :
    (projinf m : Linf 𝕜 →L[𝕜] EuclideanSpace 𝕜 (Fin m)) y j = y (j : ℕ) := by
  have h := congrArg (fun x : EuclideanSpace 𝕜 (Fin m) => x j) (projinf_apply m y)
  refine h.trans ?_
  simp [Pi.single_apply, Finset.sum_ite_eq]

lemma norm_projinf_apply_le (m : ℕ) (y : Linf 𝕜) :
    ‖(projinf m : Linf 𝕜 →L[𝕜] EuclideanSpace 𝕜 (Fin m)) y‖ ≤ Real.sqrt m * ‖y‖ := by
  have hnn : (0 : ℝ) ≤ ‖(projinf m : Linf 𝕜 →L[𝕜] EuclideanSpace 𝕜 (Fin m)) y‖ := norm_nonneg _
  have hsq : ‖(projinf m : Linf 𝕜 →L[𝕜] EuclideanSpace 𝕜 (Fin m)) y‖ ^ 2
      = ∑ j : Fin m, ‖y (j : ℕ)‖ ^ 2 := by
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => by positivity)]
    exact Finset.sum_congr rfl fun j _ => by rw [projinf_coord]
  have hle : ∑ j : Fin m, ‖y (j : ℕ)‖ ^ 2 ≤ (m : ℝ) * ‖y‖ ^ 2 := by
    calc ∑ j : Fin m, ‖y (j : ℕ)‖ ^ 2
        ≤ ∑ _j : Fin m, ‖y‖ ^ 2 :=
          Finset.sum_le_sum fun j _ => by gcongr; exact lp.norm_apply_le_norm (by simp) y (j : ℕ)
      _ = (m : ℝ) * ‖y‖ ^ 2 := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have key : ‖(projinf m : Linf 𝕜 →L[𝕜] EuclideanSpace 𝕜 (Fin m)) y‖ ^ 2
      ≤ (Real.sqrt m * ‖y‖) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ (m : ℝ)), hsq]; exact hle
  calc ‖(projinf m : Linf 𝕜 →L[𝕜] EuclideanSpace 𝕜 (Fin m)) y‖
      = Real.sqrt (‖(projinf m : Linf 𝕜 →L[𝕜] EuclideanSpace 𝕜 (Fin m)) y‖ ^ 2) :=
        (Real.sqrt_sq hnn).symm
    _ ≤ Real.sqrt ((Real.sqrt m * ‖y‖) ^ 2) := Real.sqrt_le_sqrt key
    _ = Real.sqrt m * ‖y‖ := Real.sqrt_sq (by positivity)

lemma norm_projinf_le (m : ℕ) :
    ‖(projinf m : Linf 𝕜 →L[𝕜] EuclideanSpace 𝕜 (Fin m))‖ ≤ Real.sqrt m :=
  ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) (norm_projinf_apply_le m)

/-- Coordinate of `emb1 v` at `j < m`: the `j`-th entry is `vⱼ`. -/
lemma emb1_coord (m : ℕ) (v : EuclideanSpace 𝕜 (Fin m)) (j : Fin m) :
    (emb1 m v) (j : ℕ) = v j := by
  have h := congrArg (fun x : L1 𝕜 => x (j : ℕ)) (emb1_apply m v)
  refine h.trans ?_
  rw [lp.coeFn_sum, Finset.sum_apply]
  simp [lp.single_apply, Pi.single_apply, Finset.sum_ite_eq, Fin.val_inj]

/-- The factorization `id_{ℓ₂ᵐ} = proj∞ ∘ I ∘ emb1`. -/
lemma projinf_comp_incl_comp_emb1 (m : ℕ) :
    (projinf m : Linf 𝕜 →L[𝕜] EuclideanSpace 𝕜 (Fin m)).comp
        ((incl : L1 𝕜 →L[𝕜] Linf 𝕜).comp (emb1 m))
      = ContinuousLinearMap.id 𝕜 (EuclideanSpace 𝕜 (Fin m)) := by
  ext v j
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply]
  rw [projinf_coord, incl_apply, emb1_coord]

/-! ## `hₙ(I) ≥ 1/(n+1)` -/

/-- The Hilbert numbers of `I : ℓ₁ → ℓ_∞` are bounded below by `1/(n+1)`. Combined with
`cₙ(I) ≥ ½`, this shows the factor `n+1` in the maximal difference theorem is order-optimal. -/
theorem one_div_le_hilbertNumber (n : ℕ) :
    (1 : ℝ) / (n + 1) ≤ hilbertNumber (incl : L1 𝕜 →L[𝕜] Linf 𝕜) n := by
  set hI := hilbertNumber (incl : L1 𝕜 →L[𝕜] Linf 𝕜) n with hI_def
  have hmnn : (0 : ℝ) ≤ hI := hilbertNumber_nonneg _ _
  have hid := one_le_hilbertNumber_id (𝕜 := 𝕜) n
  have hideal := hilbertNumber_comp_comp_le (emb1 (n + 1))
    (incl : L1 𝕜 →L[𝕜] Linf 𝕜) (projinf (n + 1)) n
  rw [projinf_comp_incl_comp_emb1 (n + 1), ← hI_def] at hideal
  -- `1 ≤ hₙ(id) ≤ ‖proj∞‖ · hI · ‖emb1‖`.
  have h1 : (1 : ℝ)
      ≤ ‖(projinf (n + 1) : Linf 𝕜 →L[𝕜] EuclideanSpace 𝕜 (Fin (n + 1)))‖ * hI
        * ‖(emb1 (n + 1) : EuclideanSpace 𝕜 (Fin (n + 1)) →L[𝕜] L1 𝕜)‖ := hid.trans hideal
  -- `‖proj∞‖ · hI · ‖emb1‖ ≤ √(n+1) · hI · √(n+1) = (n+1) · hI`.
  have hbound : ‖(projinf (n + 1) : Linf 𝕜 →L[𝕜] EuclideanSpace 𝕜 (Fin (n + 1)))‖ * hI
      * ‖(emb1 (n + 1) : EuclideanSpace 𝕜 (Fin (n + 1)) →L[𝕜] L1 𝕜)‖
      ≤ Real.sqrt ((n + 1 : ℕ) : ℝ) * hI * Real.sqrt ((n + 1 : ℕ) : ℝ) := by
    gcongr
    · exact norm_projinf_le (𝕜 := 𝕜) (n + 1)
    · exact norm_emb1_le (𝕜 := 𝕜) (n + 1)
  have hsqrt : Real.sqrt ((n + 1 : ℕ) : ℝ) * hI * Real.sqrt ((n + 1 : ℕ) : ℝ)
      = ((n : ℝ) + 1) * hI := by
    rw [mul_right_comm, Real.mul_self_sqrt (by positivity)]; push_cast; ring
  have h3 : (1 : ℝ) ≤ ((n : ℝ) + 1) * hI := by
    calc (1 : ℝ) ≤ _ := h1
      _ ≤ _ := hbound
      _ = ((n : ℝ) + 1) * hI := hsqrt
  rw [div_le_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) + 1)]
  linarith [h3]

end SNumbers.L1Linf

