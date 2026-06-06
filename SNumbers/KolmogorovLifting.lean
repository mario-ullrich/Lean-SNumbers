/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
import SNumbers.Approximation
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.Normed.Module.RieszLemma
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Kolmogorov numbers `d_n` — Pietsch's lifting identity

This file develops the Kolmogorov numbers via Pietsch's identity

  `d_n S = a_n (S ∘ Q_X)`,

where `a_n` is the approximation number (already developed in
`SNumbers.Approximation`) and

  `Q_X : ℓ¹(B_X) →L[𝕜] X`,    `Q_X(α) := ∑' x : B_X, α(x) • x`

is the canonical "summation" surjection from the ℓ¹ space indexed by the
closed unit ball `B_X = {x : X | ‖x‖ ≤ 1}`. The companion file
`SNumbers.Kolmogorov` gives the classical inf/sup definition; the two
agree (Pietsch's identity).

## Banach-space restriction

This development requires the domain spaces to be **Banach** (i.e.
`[CompleteSpace X]`). The reason is concrete: `Q_X(α) = ∑' x, α(x) • x`
is an infinite series in `X`, and the family `(α(x) • x)_{x ∈ B_X}` is
absolutely summable but only converges to an element of `X` when `X` is
complete. In the Pietsch identity itself the equation `d_n S = a_n(S∘Q)`
needs `Q` to be a continuous linear map into `X`, which fails if `X` is
not Banach (the natural codomain becomes the completion `X̂`).

The main file `SNumbers.Kolmogorov` (the classical inf/sup definition)
does **not** require `[CompleteSpace X]`, since it never references `Q`
directly — use that file when you need the Kolmogorov numbers on
non-Banach spaces.

## Naming convention

To avoid collision with `SNumbers.Kolmogorov`, all definitions in this
file live in the sub-namespace `SNumbers.Lifting`. Pietsch's identity
then reads:

  `SNumbers.Lifting.kolmogorovNumber S n = SNumbers.kolmogorovNumber S n`

(the two definitions agree on Banach spaces).

## Hypotheses required

The Pietsch route needs `[CompleteSpace X]` everywhere (so `Q_X` is
defined), and `[DenselyNormedField 𝕜]` everywhere except the elementary
axioms (S1c), (S1b), (S2), (S4):

* (S1c, S1b, S2, S4): `[NontriviallyNormedField 𝕜] + [CompleteSpace X]`.
* (S1a): adds `[DenselyNormedField 𝕜]` (norm-density for the scaling
  argument that gives `‖S∘Q‖ = ‖S‖`).
* (S3): adds `[DenselyNormedField 𝕜] + [CompleteSpace 𝕜] + [CompleteSpace W]`
  (the lift `T_{A,c}` needs density, and its codomain `ℓ¹(B_X)` must be
  complete).
* (S5'): adds `[DenselyNormedField 𝕜] + [CompleteSpace 𝕜]` (Riesz).

By contrast, the companion `SNumbers.Kolmogorov` proves (S3) under just
`[NontriviallyNormedField 𝕜]` and no `[CompleteSpace X]`. The price paid
here is therefore `[CompleteSpace X]`, plus `[DenselyNormedField 𝕜]` and
`[CompleteSpace 𝕜]` for (S3).

## File overview

* The free ℓ¹ space `BallLp 𝕜 X` and its summation map `Q`.
* `kolmogorovNumber S n := approximationNumber (S ∘ Q_X) n`.

The axioms are presented in **numerical order** (S1)→(S2)→(S3)→(S4)→(S5'/S5),
with `section` blocks switching to stronger hypotheses when needed:

* (S1c, S1b): one-liners over `a_n` (`[NontrivNF + CompleteSpace X]`).
* (S1a): basis-vector lemma + density-of-norm scaling
  (extra `[DenselyNormedField 𝕜]`).
* (S2): one-liner over `a_n` plus `‖T∘Q‖ ≤ ‖T‖`.
* (S3): the lift `T_{A,c} : ℓ¹(B_W) →L[𝕜] ℓ¹(B_X)` factoring
  `(B∘S∘A) ∘ Q_W = B ∘ (S ∘ Q_X) ∘ T_{A,c}` (extra
  `[DenselyNormedField 𝕜] + [CompleteSpace 𝕜] + [CompleteSpace W]`).
* (S4): one-liner over `a_n` (`range (S∘Q) ⊆ range S`).
* (S5'/S5): Riesz + density-of-norm scaling (extra
  `[DenselyNormedField 𝕜] + [CompleteSpace 𝕜]`).
-/

universe u

open scoped Cardinal NNReal ENNReal
open ContinuousLinearMap

namespace SNumbers
namespace Lifting

/-! ## The closed unit ball and the free ℓ¹ space -/

/-- The closed unit ball of `X` as a `Type`. -/
abbrev Ball (X : Type u) [NormedAddCommGroup X] : Type u :=
  {x : X // ‖x‖ ≤ 1}

/-- `ℓ¹(B_X, 𝕜)` — the scalar `ℓ¹` space indexed by the closed unit ball
of `X`. -/
abbrev BallLp (𝕜 : Type u) [NontriviallyNormedField 𝕜] (X : Type u)
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] : Type u :=
  lp (fun _ : Ball X => 𝕜) 1

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]
variable {X Y : Type u}
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]

/-! ## The Pietsch surjection `Q : ℓ¹(B_X) →L[𝕜] X` -/

/-- `α ∈ ℓ¹(B_X)` has summable absolute values. -/
private lemma summable_norm_α (α : BallLp 𝕜 X) :
    Summable (fun x : Ball X => ‖α x‖) := by
  have hp1 : (0 : ℝ) < (1 : ℝ≥0∞).toReal := by norm_num
  simpa using (lp.memℓp α).summable hp1

/-- `‖α(x) • x‖ ≤ |α(x)|` on the unit ball, so the family is summable. -/
private lemma summable_norm_smul_val (α : BallLp 𝕜 X) :
    Summable (fun x : Ball X => ‖α x • (x : X)‖) :=
  (summable_norm_α α).of_nonneg_of_le (fun _ => norm_nonneg _) (fun x => by
    rw [norm_smul]; exact mul_le_of_le_one_right (norm_nonneg _) x.2)

/-- The vector family is summable in `X` (uses completeness). -/
private lemma summable_smul_val [CompleteSpace X] (α : BallLp 𝕜 X) :
    Summable (fun x : Ball X => α x • (x : X)) :=
  (summable_norm_smul_val α).of_norm

/-- The summation surjection `Q : ℓ¹(B_X) →L[𝕜] X`. Operator norm `≤ 1`. -/
noncomputable def Q [CompleteSpace X] : BallLp 𝕜 X →L[𝕜] X :=
  LinearMap.mkContinuous
    { toFun := fun α => ∑' x : Ball X, α x • (x : X)
      map_add' := fun α β => by
        simp only [lp.coeFn_add, Pi.add_apply, add_smul]
        exact (summable_smul_val α).tsum_add (summable_smul_val β)
      map_smul' := fun c α => by
        simp only [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul,
          RingHom.id_apply, mul_smul]
        exact (summable_smul_val α).tsum_const_smul c }
    1 (fun α => by
      rw [one_mul]
      refine (norm_tsum_le_tsum_norm (summable_norm_smul_val α)).trans ?_
      refine (Summable.tsum_le_tsum (fun x => by
        rw [norm_smul]; exact mul_le_of_le_one_right (norm_nonneg _) x.2)
        (summable_norm_smul_val α) (summable_norm_α α)).trans_eq ?_
      have hp1 : (0 : ℝ) < (1 : ℝ≥0∞).toReal := by norm_num
      rw [lp.norm_eq_tsum_rpow hp1 α, show (1 : ℝ≥0∞).toReal = 1 from by norm_num]
      simp [Real.rpow_one])

variable [CompleteSpace X]

@[simp] lemma Q_apply (α : BallLp 𝕜 X) :
    (Q : BallLp 𝕜 X →L[𝕜] X) α = ∑' x : Ball X, α x • (x : X) := rfl

lemma norm_Q_le : ‖(Q : BallLp 𝕜 X →L[𝕜] X)‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

/-- The basis-vector identity: `Q (lp.single 1 ⟨x,h⟩ c) = c • x`. -/
lemma Q_single (x : X) (hx : ‖x‖ ≤ 1) (c : 𝕜) :
    letI : DecidableEq (Ball X) := Classical.decEq _
    (Q : BallLp 𝕜 X →L[𝕜] X) (lp.single 1 (⟨x, hx⟩ : Ball X) c) = c • x := by
  letI : DecidableEq (Ball X) := Classical.decEq _
  rw [Q_apply, tsum_eq_single (⟨x, hx⟩ : Ball X)]
  · rw [lp.single_apply_self]
  · intro y hy; rw [lp.single_apply_ne 1 _ _ hy, zero_smul]

/-! ## Definition -/

/-- The `n`-th **Kolmogorov number** of `S : X →L[𝕜] Y` (Pietsch's identity). -/
noncomputable def kolmogorovNumber (S : X →L[𝕜] Y) (n : ℕ) : ℝ :=
  approximationNumber (S.comp (Q : BallLp 𝕜 X →L[𝕜] X)) n


/-! ## (S1c) Non-negativity -/

lemma kolmogorovNumber_nonneg (S : X →L[𝕜] Y) (n : ℕ) :
    0 ≤ kolmogorovNumber S n :=
  approximationNumber_nonneg _ _


/-! ## (S1b) Antitone in `n` -/

lemma kolmogorovNumber_antitone (S : X →L[𝕜] Y) (n : ℕ) :
    kolmogorovNumber S (n + 1) ≤ kolmogorovNumber S n :=
  approximationNumber_antitone _ _


/-! ## (S1a) `kolmogorovNumber S 0 = ‖S‖`

We isolate a basis-vector lemma `exists_lift_of_pos_norm` packaging
`α := lp.single 1 ⟨c⁻¹ • x, _⟩ c` with `Q α = x` and `‖α‖ = ‖c‖`. Density of
`‖𝕜‖` lets us pick `‖c‖ ↘ ‖x‖`, giving `‖S x‖ ≤ ‖S∘Q‖ · ‖c‖`; the limit
yields `‖S∘Q‖ = ‖S‖`. -/

section S1a
variable {𝕜 : Type u} [DenselyNormedField 𝕜]
variable {X Y : Type u}
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]

/-- The **basis-vector lifting lemma** packaging the construction
`α := lp.single 1 ⟨c⁻¹ • x, _⟩ c` with `Q α = x` and `‖α‖ = ‖c‖`. -/
private lemma exists_lift_of_pos_norm
    {x : X} (hx : 0 < ‖x‖) {δ : ℝ} (hδ : 0 < δ) :
    ∃ (c : 𝕜) (h_in : ‖c⁻¹ • x‖ ≤ 1),
      ‖x‖ < ‖c‖ ∧ ‖c‖ < ‖x‖ + δ ∧
      (Q : BallLp 𝕜 X →L[𝕜] X)
          (letI := Classical.decEq (Ball X);
           lp.single 1 (⟨c⁻¹ • x, h_in⟩ : Ball X) c) = x ∧
      (letI := Classical.decEq (Ball X);
       ‖lp.single (E := fun _ : Ball X => 𝕜) 1 (⟨c⁻¹ • x, h_in⟩ : Ball X) c‖) = ‖c‖ := by
  obtain ⟨c, hc_lb, hc_ub⟩ :=
    NormedField.exists_lt_norm_lt 𝕜 hx.le (lt_add_of_pos_right _ hδ)
  have hc_pos : 0 < ‖c‖ := hx.trans hc_lb
  have hc_ne : c ≠ 0 := norm_pos_iff.mp hc_pos
  have h_in : ‖c⁻¹ • x‖ ≤ 1 := by
    rw [norm_smul, norm_inv, inv_mul_le_iff₀ hc_pos, mul_one]; exact hc_lb.le
  refine ⟨c, h_in, hc_lb, hc_ub, ?_, ?_⟩
  · rw [Q_single _ h_in c, smul_smul, mul_inv_cancel₀ hc_ne, one_smul]
  · letI := Classical.decEq (Ball X)
    rw [lp.norm_single (by norm_num : (0 : ℝ≥0∞) < 1)]

/-- (S1a) `kolmogorovNumber S 0 = ‖S‖`. -/
lemma kolmogorovNumber_zero_eq_norm (S : X →L[𝕜] Y) :
    kolmogorovNumber S 0 = ‖S‖ := by
  unfold kolmogorovNumber
  rw [approximationNumber_zero_eq_norm]
  refine le_antisymm ?_ ?_
  · -- `‖S∘Q‖ ≤ ‖S‖` from submultiplicativity and `‖Q‖ ≤ 1`.
    refine (opNorm_comp_le _ _).trans ?_
    exact (mul_le_mul_of_nonneg_left norm_Q_le (norm_nonneg _)).trans (mul_one _).le
  · -- `‖S‖ ≤ ‖S∘Q‖` via density-of-norm scaling on each `x ≠ 0`.
    refine opNorm_le_bound _ (norm_nonneg _) fun x => ?_
    set M := ‖S.comp (Q : BallLp 𝕜 X →L[𝕜] X)‖
    have hM_nn : 0 ≤ M := norm_nonneg _
    by_cases hx : x = 0
    · simp [hx]
    refine le_of_forall_pos_le_add fun ε hε => ?_
    have hM1_pos : (0 : ℝ) < M + 1 := by linarith
    obtain ⟨c, h_in, hc_lb, hc_ub, hQα, hαnorm⟩ :=
      exists_lift_of_pos_norm (𝕜 := 𝕜) (X := X) (norm_pos_iff.mpr hx)
        (div_pos hε hM1_pos)
    -- `‖S x‖ = ‖(S∘Q) α‖ ≤ M · ‖α‖ = M · ‖c‖ ≤ M · ‖x‖ + ε`.
    letI : DecidableEq (Ball X) := Classical.decEq _
    have h_op := (S.comp (Q : BallLp 𝕜 X →L[𝕜] X)).le_opNorm
                  (lp.single 1 (⟨c⁻¹ • x, h_in⟩ : Ball X) c)
    rw [coe_comp', Function.comp_apply, hQα, hαnorm] at h_op
    have : M * ‖c‖ ≤ M * ‖x‖ + ε := by
      calc M * ‖c‖
          ≤ M * (‖x‖ + ε / (M + 1)) :=
            mul_le_mul_of_nonneg_left hc_ub.le hM_nn
        _ = M * ‖x‖ + (M / (M + 1)) * ε := by ring
        _ ≤ M * ‖x‖ + 1 * ε := by
            gcongr; exact (div_le_one hM1_pos).mpr (by linarith)
        _ = M * ‖x‖ + ε := by ring
    linarith

end S1a


/-! ## A useful upper bound: `kolmogorovNumber S n ≤ ‖S‖` -/

lemma kolmogorovNumber_le_norm (S : X →L[𝕜] Y) (n : ℕ) :
    kolmogorovNumber S n ≤ ‖S‖ :=
  (approximationNumber_le_norm _ _).trans <|
    (opNorm_comp_le _ _).trans <|
      (mul_le_mul_of_nonneg_left norm_Q_le (norm_nonneg _)).trans (mul_one _).le


/-! ## (S2) Subadditivity -/

lemma kolmogorovNumber_add_le (S T : X →L[𝕜] Y) (n : ℕ) :
    kolmogorovNumber (S + T) n ≤ kolmogorovNumber S n + ‖T‖ := by
  unfold kolmogorovNumber
  rw [ContinuousLinearMap.add_comp]
  have h_TQ : ‖T.comp (Q : BallLp 𝕜 X →L[𝕜] X)‖ ≤ ‖T‖ :=
    (opNorm_comp_le _ _).trans <|
      (mul_le_mul_of_nonneg_left norm_Q_le (norm_nonneg _)).trans (mul_one _).le
  linarith [approximationNumber_add_le (S.comp Q) (T.comp Q) n]

/-! ## (S3) Ideal property — via the lift `T_{A,c}`

For `A : W →L[𝕜] X` and `c ∈ 𝕜` with `‖A‖ ≤ ‖c‖` and `c ≠ 0`, the lift
`T_{A,c}(α) := ∑' w, α(w) • lp.single 1 ⟨c⁻¹ • A w, _⟩ c` satisfies
`Q_X ∘ T_{A,c} = A ∘ Q_W` and `‖T_{A,c}‖ ≤ ‖c‖`. (S3) follows by
factoring `(B∘S∘A) ∘ Q_W = B ∘ (S ∘ Q_X) ∘ T_{A,c}`, applying (S3) for
`a_n`, and taking `‖c‖ ↘ ‖A‖`. -/

section S3
variable {𝕜 : Type u} [DenselyNormedField 𝕜] [CompleteSpace 𝕜]
variable {W X Y Z : Type u}
variable [NormedAddCommGroup W] [NormedSpace 𝕜 W] [CompleteSpace W]
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
variable [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]
set_option linter.unusedSectionVars false

/-- For `w ∈ B_W`, `c⁻¹ • A w ∈ B_X` (provided `‖A‖ ≤ ‖c‖`, `c ≠ 0`). -/
private lemma Aw_in_ball {A : W →L[𝕜] X} {c : 𝕜} (hc : ‖A‖ ≤ ‖c‖) (hc_ne : c ≠ 0)
    (w : Ball W) : ‖c⁻¹ • A (w : W)‖ ≤ 1 := by
  have hc_pos : 0 < ‖c‖ := norm_pos_iff.mpr hc_ne
  rw [norm_smul, norm_inv, inv_mul_le_iff₀ hc_pos, mul_one]
  refine (A.le_opNorm _).trans ?_
  rw [mul_comm]
  exact (mul_le_of_le_one_left (norm_nonneg _) w.2).trans hc

/-- The basis-vector image of the lift. -/
private noncomputable def liftBasis {A : W →L[𝕜] X} {c : 𝕜}
    (hc : ‖A‖ ≤ ‖c‖) (hc_ne : c ≠ 0) (w : Ball W) : BallLp 𝕜 X :=
  letI : DecidableEq (Ball X) := Classical.decEq _
  lp.single 1 (⟨c⁻¹ • A (w : W), Aw_in_ball hc hc_ne w⟩ : Ball X) c

private lemma norm_liftBasis {A : W →L[𝕜] X} {c : 𝕜} (hc : ‖A‖ ≤ ‖c‖) (hc_ne : c ≠ 0)
    (w : Ball W) : ‖liftBasis hc hc_ne w‖ = ‖c‖ := by
  letI := Classical.decEq (Ball X)
  exact lp.norm_single (by norm_num : (0 : ℝ≥0∞) < 1) _ _

private lemma Q_liftBasis (A : W →L[𝕜] X) {c : 𝕜} (hc : ‖A‖ ≤ ‖c‖) (hc_ne : c ≠ 0)
    (w : Ball W) : (Q : BallLp 𝕜 X →L[𝕜] X) (liftBasis hc hc_ne w) = A (w : W) := by
  unfold liftBasis
  rw [Q_single _ (Aw_in_ball hc hc_ne w) c, smul_smul, mul_inv_cancel₀ hc_ne, one_smul]

private lemma summable_norm_smul_liftBasis {A : W →L[𝕜] X} {c : 𝕜}
    (hc : ‖A‖ ≤ ‖c‖) (hc_ne : c ≠ 0) (α : BallLp 𝕜 W) :
    Summable (fun w : Ball W => ‖α w • liftBasis hc hc_ne w‖) := by
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun w => ?_)
    ((summable_norm_α α).mul_right ‖c‖)
  rw [norm_smul]
  exact mul_le_mul_of_nonneg_left (norm_liftBasis hc hc_ne w).le (norm_nonneg _)

private lemma summable_smul_liftBasis {A : W →L[𝕜] X} {c : 𝕜}
    (hc : ‖A‖ ≤ ‖c‖) (hc_ne : c ≠ 0) (α : BallLp 𝕜 W) :
    Summable (fun w : Ball W => α w • liftBasis hc hc_ne w) :=
  Summable.of_norm_bounded ((summable_norm_α α).mul_right ‖c‖) (fun w => by
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_left (norm_liftBasis hc hc_ne w).le (norm_nonneg _))

/-- The lift `T_{A,c} : ℓ¹(B_W) →L[𝕜] ℓ¹(B_X)`. -/
noncomputable def liftA (A : W →L[𝕜] X) {c : 𝕜} (hc : ‖A‖ ≤ ‖c‖) (hc_ne : c ≠ 0) :
    BallLp 𝕜 W →L[𝕜] BallLp 𝕜 X :=
  LinearMap.mkContinuous
    { toFun := fun α => ∑' w : Ball W, α w • liftBasis hc hc_ne w
      map_add' := fun α β => by
        simp only [lp.coeFn_add, Pi.add_apply, add_smul]
        exact (summable_smul_liftBasis hc hc_ne α).tsum_add
              (summable_smul_liftBasis hc hc_ne β)
      map_smul' := fun k α => by
        simp only [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul,
          RingHom.id_apply, mul_smul]
        exact (summable_smul_liftBasis hc hc_ne α).tsum_const_smul k }
    ‖c‖ (fun α => by
      refine (norm_tsum_le_tsum_norm (summable_norm_smul_liftBasis hc hc_ne α)).trans ?_
      refine (Summable.tsum_le_tsum (fun w => by
        rw [norm_smul]
        exact mul_le_mul_of_nonneg_left (norm_liftBasis hc hc_ne w).le (norm_nonneg _))
        (summable_norm_smul_liftBasis hc hc_ne α)
        ((summable_norm_α α).mul_right ‖c‖)).trans_eq ?_
      rw [tsum_mul_right]
      have hp1 : (0 : ℝ) < (1 : ℝ≥0∞).toReal := by norm_num
      rw [lp.norm_eq_tsum_rpow hp1 α, show (1 : ℝ≥0∞).toReal = 1 from by norm_num]
      simp [Real.rpow_one, mul_comm])

@[simp] lemma liftA_apply (A : W →L[𝕜] X) {c : 𝕜} (hc : ‖A‖ ≤ ‖c‖) (hc_ne : c ≠ 0)
    (α : BallLp 𝕜 W) :
    liftA A hc hc_ne α = ∑' w : Ball W, α w • liftBasis hc hc_ne w := rfl

lemma norm_liftA_le (A : W →L[𝕜] X) {c : 𝕜} (hc : ‖A‖ ≤ ‖c‖) (hc_ne : c ≠ 0) :
    ‖liftA A hc hc_ne‖ ≤ ‖c‖ :=
  LinearMap.mkContinuous_norm_le _ (norm_nonneg _) _

/-- The defining property: `Q_X ∘ T_{A,c} = A ∘ Q_W`. Proved by commuting
`Q` with the tsum (via `ContinuousLinearMap.map_tsum`). -/
lemma Q_comp_liftA (A : W →L[𝕜] X) {c : 𝕜} (hc : ‖A‖ ≤ ‖c‖) (hc_ne : c ≠ 0) :
    (Q : BallLp 𝕜 X →L[𝕜] X).comp (liftA A hc hc_ne) = A.comp Q := by
  ext α
  show (Q : BallLp 𝕜 X →L[𝕜] X) (liftA A hc hc_ne α)
        = A ((Q : BallLp 𝕜 W →L[𝕜] W) α)
  rw [liftA_apply,
      (Q : BallLp 𝕜 X →L[𝕜] X).map_tsum (summable_smul_liftBasis hc hc_ne α)]
  simp_rw [map_smul, Q_liftBasis A hc hc_ne]
  rw [Q_apply, A.map_tsum (summable_smul_val α)]
  simp_rw [map_smul]

/-- (S3) Ideal property. -/
lemma kolmogorovNumber_comp_comp_le
    (A : W →L[𝕜] X) (S : X →L[𝕜] Y) (B : Y →L[𝕜] Z) (n : ℕ) :
    kolmogorovNumber (B.comp (S.comp A)) n ≤
      ‖B‖ * kolmogorovNumber S n * ‖A‖ := by
  refine le_of_forall_pos_le_add fun ε hε => ?_
  set kN := kolmogorovNumber S n
  have hkN_nn : 0 ≤ kN := kolmogorovNumber_nonneg S n
  set BkN := ‖B‖ * kN
  have hBkN_nn : 0 ≤ BkN := mul_nonneg (norm_nonneg _) hkN_nn
  have hBkN1_pos : (0 : ℝ) < BkN + 1 := by linarith
  obtain ⟨c, hc_lb, hc_ub⟩ :=
    NormedField.exists_lt_norm_lt 𝕜 (norm_nonneg A)
      (lt_add_of_pos_right ‖A‖ (div_pos hε hBkN1_pos))
  have hc_ne : c ≠ 0 := norm_pos_iff.mp (lt_of_le_of_lt (norm_nonneg _) hc_lb)
  -- Factor: (B∘S∘A) ∘ Q_W = B ∘ ((S∘Q_X) ∘ T).
  have h_inner : (S.comp A).comp (Q : BallLp 𝕜 W →L[𝕜] W)
      = (S.comp Q).comp (liftA A hc_lb.le hc_ne) := by
    rw [ContinuousLinearMap.comp_assoc,
        show A.comp (Q : BallLp 𝕜 W →L[𝕜] W) =
             (Q : BallLp 𝕜 X →L[𝕜] X).comp (liftA A hc_lb.le hc_ne) from
          (Q_comp_liftA A hc_lb.le hc_ne).symm,
        ← ContinuousLinearMap.comp_assoc]
  show approximationNumber
      ((B.comp (S.comp A)).comp (Q : BallLp 𝕜 W →L[𝕜] W)) n ≤ ‖B‖ * kN * ‖A‖ + ε
  rw [show (B.comp (S.comp A)).comp (Q : BallLp 𝕜 W →L[𝕜] W)
        = B.comp ((S.comp Q).comp (liftA A hc_lb.le hc_ne)) by
      rw [ContinuousLinearMap.comp_assoc, h_inner]]
  refine (approximationNumber_comp_comp_le _ _ _ _).trans ?_
  -- ‖B‖ · kN · ‖T‖ ≤ ‖B‖ · kN · ‖c‖ ≤ ‖B‖ · kN · (‖A‖ + δ) ≤ ‖B‖ · kN · ‖A‖ + ε.
  calc ‖B‖ * kN * ‖liftA A hc_lb.le hc_ne‖
      ≤ ‖B‖ * kN * (‖A‖ + ε / (BkN + 1)) :=
        mul_le_mul_of_nonneg_left
          ((norm_liftA_le A hc_lb.le hc_ne).trans hc_ub.le) hBkN_nn
    _ = ‖B‖ * kN * ‖A‖ + (BkN / (BkN + 1)) * ε := by ring
    _ ≤ ‖B‖ * kN * ‖A‖ + 1 * ε := by
        gcongr; exact (div_le_one hBkN1_pos).mpr (by linarith)
    _ = ‖B‖ * kN * ‖A‖ + ε := by ring

end S3


/-! ## (S4) Vanishing on operators of rank ≤ n -/

/-- (S4) Vanishing on operators of rank ≤ n. -/
lemma kolmogorovNumber_eq_zero_of_rank_le {S : X →L[𝕜] Y} {n : ℕ}
    (hS : S.rank ≤ (n : Cardinal)) :
    kolmogorovNumber S n = 0 :=
  approximationNumber_eq_zero_of_rank_le <|
    (Submodule.rank_mono (by rintro y ⟨α, hα⟩; exact ⟨Q α, hα⟩)).trans hS


/-! ## (S5'/S5) Strict normalisation -/

section S5
variable {𝕜 : Type u} [DenselyNormedField 𝕜] [CompleteSpace 𝕜]
variable {X : Type u}
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]

/-- Per-approximant: `‖Q − L‖ ≥ 1` for every rank-`n` `L : ℓ¹(B_X) →L[𝕜] X`,
`n < dim X`. Riesz at level `r = 1 − ε/2` plus density-of-norm scaling. -/
private lemma one_le_norm_Q_sub_L (n : ℕ) (h_dim : n < Module.finrank 𝕜 X)
    (L : BallLp 𝕜 X →L[𝕜] X) (hL : L.rank ≤ (n : Cardinal)) :
    1 ≤ ‖(Q : BallLp 𝕜 X →L[𝕜] X) - L‖ := by
  haveI : FiniteDimensional 𝕜 X :=
    .of_finrank_pos (Nat.lt_of_le_of_lt (Nat.zero_le _) h_dim)
  haveI : Nontrivial X := Module.nontrivial_of_finrank_pos
    (Nat.lt_of_le_of_lt (Nat.zero_le _) h_dim)
  set V : Submodule 𝕜 X := LinearMap.range (L : BallLp 𝕜 X →ₗ[𝕜] X)
  have hV_lt : Module.finrank 𝕜 V < Module.finrank 𝕜 X :=
    lt_of_le_of_lt (Module.finrank_le_of_rank_le hL) h_dim
  have hV_ne_top : V ≠ ⊤ := fun h => by rw [h, finrank_top] at hV_lt; exact lt_irrefl _ hV_lt
  have hV_closed : IsClosed (V : Set X) := V.closed_of_finiteDimensional
  have hV_exists : ∃ x : X, x ∉ V := SetLike.exists_not_mem_of_ne_top V hV_ne_top
  -- Limit `r → 1`: enough to show `1 ≤ ‖Q − L‖ + ε` for every `ε > 0`. The
  -- `ε ≥ 1` case is trivial; for `ε ∈ (0, 1)` we run Riesz at level `1 − ε/2`.
  refine le_of_forall_pos_le_add fun ε hε => ?_
  by_cases hε1 : 1 ≤ ε
  · linarith [norm_nonneg ((Q : BallLp 𝕜 X →L[𝕜] X) - L)]
  have hε1' : ε < 1 := lt_of_not_ge hε1
  have h1ε_pos : (0 : ℝ) < 1 - ε := by linarith
  -- Riesz at level `1 − ε/2`.
  obtain ⟨x₀, hx₀_ne, hx₀_dist⟩ :=
    riesz_lemma hV_closed hV_exists (by linarith : (1 - ε / 2 : ℝ) < 1)
  have hx₀_pos : 0 < ‖x₀‖ :=
    norm_pos_iff.mpr (fun h => hx₀_ne (h ▸ V.zero_mem))
  -- Pick `c` with `‖x₀‖ < ‖c‖ < ‖x₀‖ + δ`, `δ := ε·‖x₀‖/(2(1−ε))`.
  set δ : ℝ := ε * ‖x₀‖ / (2 * (1 - ε)) with hδ_def
  have hδ_pos : 0 < δ := by positivity
  obtain ⟨c, _, hc_lb, hc_ub, hα_Q, hα_norm⟩ :=
    exists_lift_of_pos_norm (𝕜 := 𝕜) hx₀_pos hδ_pos
  letI := Classical.decEq (Ball X)
  set α : BallLp 𝕜 X := lp.single 1 (⟨c⁻¹ • x₀, _⟩ : Ball X) c
  -- `(1 − ε/2) · ‖x₀‖ ≤ ‖x₀ − L α‖ = ‖(Q − L) α‖ ≤ ‖Q − L‖ · ‖c‖`.
  have h_riesz : (1 - ε / 2) * ‖x₀‖ ≤ ‖x₀ - L α‖ :=
    hx₀_dist (L α) ⟨α, rfl⟩
  have h_op := ((Q : BallLp 𝕜 X →L[𝕜] X) - L).le_opNorm α
  rw [ContinuousLinearMap.sub_apply, hα_Q, hα_norm] at h_op
  have h_chain := h_riesz.trans h_op
  -- The choice of `δ` ensures `(1 − ε) · ‖c‖ < (1 − ε/2) · ‖x₀‖`.
  have h_lhs : (1 - ε) * ‖c‖ < (1 - ε / 2) * ‖x₀‖ := by
    calc (1 - ε) * ‖c‖
        < (1 - ε) * (‖x₀‖ + δ) := mul_lt_mul_of_pos_left hc_ub h1ε_pos
      _ = (1 - ε) * ‖x₀‖ + ε * ‖x₀‖ / 2 := by rw [hδ_def]; field_simp
      _ = (1 - ε / 2) * ‖x₀‖ := by ring
  -- `(1 - ε) · ‖c‖ < ‖Q − L‖ · ‖c‖`, cancel `‖c‖ > 0` to get `1 - ε ≤ ‖Q − L‖`,
  -- then rearrange to `1 ≤ ‖Q − L‖ + ε`.
  have : (1 - ε : ℝ) ≤ ‖(Q : BallLp 𝕜 X →L[𝕜] X) - L‖ :=
    (lt_of_mul_lt_mul_right (h_lhs.trans_le h_chain) (norm_nonneg _)).le
  linarith

/-- (S5') Strict normalisation `kolmogorovNumber id_X n = 1` whenever
`n < Module.finrank 𝕜 X`. -/
lemma kolmogorovNumber_strict (n : ℕ) (h : n < Module.finrank 𝕜 X) :
    kolmogorovNumber (ContinuousLinearMap.id 𝕜 X) n = 1 := by
  haveI : Nontrivial X :=
    Module.nontrivial_of_finrank_pos (Nat.lt_of_le_of_lt (Nat.zero_le _) h)
  refine le_antisymm ((kolmogorovNumber_le_norm _ _).trans norm_id.le) ?_
  show 1 ≤ approximationNumber
    ((ContinuousLinearMap.id 𝕜 X).comp (Q : BallLp 𝕜 X →L[𝕜] X)) n
  rw [ContinuousLinearMap.id_comp]
  refine le_csInf (approximationSet_nonempty _ _) ?_
  rintro _ ⟨L, hL_rank, rfl⟩
  exact one_le_norm_Q_sub_L n h L hL_rank

end S5

section S5b
variable {𝕜 : Type u} [DenselyNormedField 𝕜] [CompleteSpace 𝕜]

/-- (S5) Normalisation on `id_{ℓ₂^{n+1}}`. -/
lemma kolmogorovNumber_id_euclidean (n : ℕ) :
    kolmogorovNumber
      (ContinuousLinearMap.id 𝕜 (EuclideanSpace 𝕜 (Fin (n + 1)))) n = 1 := by
  have h_finrank : Module.finrank 𝕜 (EuclideanSpace 𝕜 (Fin (n + 1))) = n + 1 := by
    rw [(WithLp.linearEquiv 2 𝕜 (Fin (n + 1) → 𝕜)).finrank_eq, Module.finrank_pi 𝕜]
    exact Fintype.card_fin _
  have h : n < Module.finrank 𝕜 (EuclideanSpace 𝕜 (Fin (n + 1))) := by
    rw [h_finrank]; exact Nat.lt_succ_self n
  exact kolmogorovNumber_strict n h

end S5b

/-! ## Notes on packaging

The `Family 𝕜` type in `SNumbers.Basic` quantifies over all Banach
spaces `X` without a `[CompleteSpace X]` hypothesis. Our `Q`-based
definition needs `[CompleteSpace X]`, so `Lifting.kolmogorovNumber` is
**not** a `Family 𝕜` — it's only defined for complete `X`. The main
file `SNumbers.Kolmogorov` (the inf/sup definition) avoids the
completeness restriction and exports `IsStrictSNumberSequence` directly.
The two definitions agree on the standard examples; Pietsch's identity
is the bridge. -/

end Lifting
end SNumbers
