/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import SNumbers.Approximation
public import SNumbers.Gelfand
public import SNumbers.Injectivity
public import Mathlib.Analysis.Normed.Lp.lpSpace
public import Mathlib.Analysis.Normed.Module.HahnBanach

/-!
# Gelfand numbers `cₙ`: Pietsch's embedding identity

This file proves Pietsch's identity

  `cₙ(S) = aₙ(J_Y ∘ S)`,

where `aₙ` is the approximation number and

  `J_Y : Y →L[𝕜] ℓ_∞(B_{Y*})`,    `(J_Y y)(φ) := φ y`,

is the canonical embedding of `Y` into the bounded families indexed by the closed unit
ball `B_{Y*}` of the dual. It is the dual counterpart of the lifting identity
`dₙ(S) = aₙ(S ∘ Q_X)` of `SNumbers.KolmogorovLifting`: there the Kolmogorov numbers are
the approximation numbers after a metric surjection onto the domain, here the Gelfand
numbers are the approximation numbers after a metric injection of the codomain.

Unlike the lifting identity, which needs the domain to be complete (the summation map
`Q_X` is an infinite series), the embedding identity holds between arbitrary normed spaces
over `ℝ` or `ℂ`: `J_Y` only evaluates functionals, and the one analytic input is the
Hahn–Banach theorem.

## Main results

* `SNumbers.Embedding.toLInfty`: the bounded linear map into `ℓ_∞(ι)` with coordinates
  given by a bounded family of functionals.
* `SNumbers.Embedding.J`: the canonical embedding `J_Y`, and
  `SNumbers.Embedding.isMetricInjection_J`: it is a metric injection.
* `SNumbers.Embedding.gelfandNumber_eq_approximationNumber`: Pietsch's identity
  `cₙ(S) = aₙ(J_Y ∘ S)`.

## The proof

`cₙ(S) = cₙ(J_Y ∘ S) ≤ aₙ(J_Y ∘ S)` because the Gelfand numbers are injective and every
s-number sequence lies below the approximation numbers. Conversely, for a closed subspace
`M` of codimension at most `n`, extend each functional `(φ ∘ S)|_M`, `φ ∈ B_{Y*}`, to
`g_φ ∈ X*` of the same norm (Hahn–Banach). The map `L x = (φ(S x) - g_φ(x))_φ` vanishes on
`M`, so it has rank at most `codim M ≤ n`, and `(J_Y S - L) x = (g_φ(x))_φ` has norm at most
`‖S|_M‖ ‖x‖`. Hence `aₙ(J_Y ∘ S) ≤ ‖S|_M‖`, and the infimum over `M` gives
`aₙ(J_Y ∘ S) ≤ cₙ(S)`.
-/

@[expose] public section

universe u

open scoped Cardinal ENNReal
open ContinuousLinearMap

namespace SNumbers

namespace Embedding

variable {𝕜 : Type u} [RCLike 𝕜]
variable {X Y : Type u}
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]

/-! ### Maps into `ℓ_∞` -/

section ToLInfty

variable {ι : Type u}

/-- The coordinates `(f i x)_i` of a bounded family of functionals are a bounded family. -/
lemma memℓp_infty_apply (f : ι → X →L[𝕜] 𝕜) {C : ℝ} (hC : ∀ i, ‖f i‖ ≤ C) (x : X) :
    Memℓp (fun i => f i x) ∞ := by
  refine memℓp_infty ⟨C * ‖x‖, ?_⟩
  rintro _ ⟨i, rfl⟩
  exact (f i).le_opNorm x |>.trans (mul_le_mul_of_nonneg_right (hC i) (norm_nonneg x))

/-- The bounded linear map `x ↦ (f i x)_i` into `ℓ_∞(ι)`, for a family of functionals
`f i` of norm at most `C`. -/
noncomputable def toLInfty (f : ι → X →L[𝕜] 𝕜) {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ i, ‖f i‖ ≤ C) :
    X →L[𝕜] lp (fun _ : ι => 𝕜) ∞ :=
  LinearMap.mkContinuous
    { toFun := fun x => ⟨fun i => f i x, memℓp_infty_apply f hC x⟩
      map_add' := fun x y => by ext i; exact map_add (f i) x y
      map_smul' := fun c x => by ext i; exact map_smul (f i) c x }
    C
    (fun x => lp.norm_le_of_forall_le (mul_nonneg hC0 (norm_nonneg x)) fun i =>
      (f i).le_opNorm x |>.trans (mul_le_mul_of_nonneg_right (hC i) (norm_nonneg x)))

@[simp] lemma toLInfty_apply (f : ι → X →L[𝕜] 𝕜) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ i, ‖f i‖ ≤ C) (x : X) (i : ι) :
    (toLInfty f hC0 hC x : ι → 𝕜) i = f i x := rfl

end ToLInfty

/-! ### The canonical embedding `J_Y` -/

/-- The closed unit ball `B_{Y*}` of the dual of `Y`, the index set of `ℓ_∞(B_{Y*})`. -/
abbrev DualBall (𝕜 : Type u) [RCLike 𝕜] (Y : Type u) [NormedAddCommGroup Y]
    [NormedSpace 𝕜 Y] : Type u :=
  Metric.closedBall (0 : Y →L[𝕜] 𝕜) 1

/-- A functional in `B_{Y*}` has norm at most `1`. -/
lemma norm_le_one (φ : DualBall 𝕜 Y) : ‖(φ : Y →L[𝕜] 𝕜)‖ ≤ 1 := by
  have h := φ.2
  rwa [Metric.mem_closedBall, dist_zero_right] at h

/-- The canonical embedding `J_Y : Y → ℓ_∞(B_{Y*})`, `(J_Y y)(φ) = φ y`. -/
noncomputable def J : Y →L[𝕜] lp (fun _ : DualBall 𝕜 Y => 𝕜) ∞ :=
  toLInfty (fun φ : DualBall 𝕜 Y => (φ : Y →L[𝕜] 𝕜)) zero_le_one norm_le_one

/-- **`J_Y` is a metric injection**: `‖J_Y y‖ = ‖y‖`, the upper bound because every
coordinate is a functional of norm at most `1`, the lower bound by a norming functional
(Hahn–Banach). -/
lemma isMetricInjection_J : IsMetricInjection (J : Y →L[𝕜] _) := by
  intro y
  refine le_antisymm ?_ ?_
  · refine lp.norm_le_of_forall_le (norm_nonneg y) fun φ => ?_
    calc ‖(φ : Y →L[𝕜] 𝕜) y‖ ≤ ‖(φ : Y →L[𝕜] 𝕜)‖ * ‖y‖ := (φ : Y →L[𝕜] 𝕜).le_opNorm y
      _ ≤ 1 * ‖y‖ := mul_le_mul_of_nonneg_right (norm_le_one φ) (norm_nonneg y)
      _ = ‖y‖ := one_mul _
  · obtain ⟨g, hg, hgy⟩ := exists_dual_vector'' 𝕜 y
    have hmem : g ∈ Metric.closedBall (0 : Y →L[𝕜] 𝕜) 1 := by
      rwa [Metric.mem_closedBall, dist_zero_right]
    calc ‖y‖ = ‖g y‖ := by rw [hgy, RCLike.norm_ofReal, abs_norm]
      _ = ‖(J y : DualBall 𝕜 Y → 𝕜) ⟨g, hmem⟩‖ := rfl
      _ ≤ ‖J y‖ := lp.norm_apply_le_norm ENNReal.top_ne_zero _ _

/-! ### The approximant built from a subspace of finite codimension -/

/-- A continuous linear map that vanishes on `M` has rank at most `codim M`: it factors
through `X ⧸ M`. -/
lemma rank_le_rank_quotient_of_le_ker {Z : Type u} [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]
    (L : X →L[𝕜] Z) {M : Submodule 𝕜 X} (h : M ≤ LinearMap.ker (L : X →ₗ[𝕜] Z)) :
    L.rank ≤ Module.rank 𝕜 (X ⧸ M) := by
  rw [ContinuousLinearMap.rank, LinearMap.rank, ← Submodule.range_liftQ M _ h]
  exact rank_range_le _

/-- **Hahn–Banach approximant.** For a subspace `M` of `X` there is a continuous linear
map `L : X → ℓ_∞(B_{Y*})` vanishing on `M` with `‖J_Y ∘ S - L‖ ≤ ‖S|_M‖`. -/
lemma exists_le_ker_norm_sub_le (S : X →L[𝕜] Y) (M : Submodule 𝕜 X) :
    ∃ L : X →L[𝕜] lp (fun _ : DualBall 𝕜 Y => 𝕜) ∞,
      M ≤ LinearMap.ker (L : X →ₗ[𝕜] lp (fun _ : DualBall 𝕜 Y => 𝕜) ∞) ∧
        ‖(J : Y →L[𝕜] _).comp S - L‖ ≤ ‖S.comp M.subtypeL‖ := by
  set d := ‖S.comp M.subtypeL‖ with hd
  -- The restricted functionals `(φ ∘ S)|_M` have norm at most `d`.
  have hψ : ∀ φ : DualBall 𝕜 Y, ‖((φ : Y →L[𝕜] 𝕜).comp S).comp M.subtypeL‖ ≤ d := by
    intro φ
    calc ‖((φ : Y →L[𝕜] 𝕜).comp S).comp M.subtypeL‖
        = ‖(φ : Y →L[𝕜] 𝕜).comp (S.comp M.subtypeL)‖ := rfl
      _ ≤ ‖(φ : Y →L[𝕜] 𝕜)‖ * d := opNorm_comp_le _ _
      _ ≤ 1 * d := mul_le_mul_of_nonneg_right (norm_le_one φ) (norm_nonneg _)
      _ = d := one_mul _
  -- Hahn–Banach extensions `g φ` of the restricted functionals, of the same norm.
  choose g hg_ext hg_norm using fun φ : DualBall 𝕜 Y =>
    exists_extension_norm_eq M (((φ : Y →L[𝕜] 𝕜).comp S).comp M.subtypeL)
  have hg_le : ∀ φ, ‖g φ‖ ≤ d := fun φ => (hg_norm φ).trans_le (hψ φ)
  have hd0 : 0 ≤ d := norm_nonneg _
  -- The approximant `L x = (φ(S x) - g φ x)_φ`.
  have hL : ∀ φ : DualBall 𝕜 Y, ‖(φ : Y →L[𝕜] 𝕜).comp S - g φ‖ ≤ ‖S‖ + d := fun φ =>
    (norm_sub_le _ _).trans (add_le_add
      ((opNorm_comp_le _ _).trans
        ((mul_le_mul_of_nonneg_right (norm_le_one φ) (norm_nonneg _)).trans_eq (one_mul _)))
      (hg_le φ))
  set L := toLInfty (fun φ : DualBall 𝕜 Y => (φ : Y →L[𝕜] 𝕜).comp S - g φ) (by positivity) hL
    with hL_def
  refine ⟨L, ?_, ?_⟩
  · -- `L` vanishes on `M`: `g φ` agrees with `φ ∘ S` there.
    intro m hm
    rw [LinearMap.mem_ker]
    ext φ
    have h := hg_ext φ ⟨m, hm⟩
    simp only [coe_comp, Function.comp_apply, Submodule.coe_subtypeL,
      Submodule.coe_subtype] at h
    simp [hL_def, h]
  · -- `(J_Y S - L) x = (g φ x)_φ`.
    refine opNorm_le_bound _ hd0 fun x => ?_
    refine lp.norm_le_of_forall_le (mul_nonneg hd0 (norm_nonneg x)) fun φ => ?_
    have hcoord : (((J : Y →L[𝕜] _).comp S - L) x : DualBall 𝕜 Y → 𝕜) φ = g φ x := by
      simp [hL_def, J]
    rw [hcoord]
    exact (g φ).le_opNorm x |>.trans (mul_le_mul_of_nonneg_right (hg_le φ) (norm_nonneg x))

/-! ### Pietsch's embedding identity -/

/-- The approximation numbers of `J_Y ∘ S` are at most the Gelfand numbers of `S`. -/
lemma approximationNumber_J_comp_le (S : X →L[𝕜] Y) (n : ℕ) :
    approximationNumber ((J : Y →L[𝕜] _).comp S) n ≤ gelfandNumber S n := by
  rw [gelfandNumber_def]
  refine le_csInf (gelfandSet_nonempty S n) ?_
  rintro _ ⟨M, -, hM, rfl⟩
  obtain ⟨L, hker, hnorm⟩ := exists_le_ker_norm_sub_le S M
  exact (approximationNumber_le_norm_sub
    ((rank_le_rank_quotient_of_le_ker L hker).trans hM)).trans hnorm

/-- **Pietsch's embedding identity** `cₙ(S) = aₙ(J_Y ∘ S)`: the Gelfand numbers are the
approximation numbers after the canonical embedding of the codomain into `ℓ_∞(B_{Y*})`. -/
theorem gelfandNumber_eq_approximationNumber (S : X →L[𝕜] Y) (n : ℕ) :
    gelfandNumber S n = approximationNumber ((J : Y →L[𝕜] _).comp S) n := by
  refine le_antisymm ?_ (approximationNumber_J_comp_le S n)
  rw [← gelfandNumber_comp_metricInjection isMetricInjection_J S n]
  exact sn_le_approximationNumber isSNumberSequence_gelfandNumber _ n

end Embedding

end SNumbers
