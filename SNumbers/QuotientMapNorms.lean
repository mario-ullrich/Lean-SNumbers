/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import SNumbers.Basic
public import Mathlib.Analysis.Normed.Group.Quotient

/-!
# Norms of the quotient maps, and the operator norm from the unit ball

Mathlib ships the continuous linear maps `Submodule.mkQL` (the quotient projection
`Y →L[𝕜] Y ⧸ V`) and `Submodule.liftQL` (the lift of a continuous linear map through that
quotient), in `Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient`, for general
topological modules and without operator-norm information. This file adds the norm bounds
in the normed setting:

* `Submodule.norm_mkQL_le` and `Submodule.norm_mkQL_apply_le`: the projection is a
  contraction, `‖V.mkQL‖ ≤ 1` and `‖V.mkQL y‖ ≤ ‖y‖`;
* `Submodule.norm_liftQL_le`: the lift does not increase the norm,
  `‖V.liftQL f h‖ ≤ ‖f‖`, with the computation rule `Submodule.liftQL_mkQL`;
* `ContinuousLinearMap.opNorm_le_of_unit_closedBall`: over densely normed scalars, a bound
  on the closed unit ball bounds the operator norm, also for a merely seminormed codomain
  such as a quotient `Y ⧸ V`.
-/

@[expose] public section

namespace ContinuousLinearMap

section UnitBall
/-! The operator norm is the supremum of `‖f x‖` over the *closed unit ball*
only when the scalar norms are dense: over a discretely valued field one can
never rescale a vector to have norm exactly `1`, and the supremum over the
unit ball may fall short of `‖f‖`. Mathlib's
`ContinuousLinearMap.sSup_unitClosedBall_eq_norm` is stated in exactly that
`DenselyNormedField` setting; the lemma below is the bound-form we need. The
codomain may be merely seminormed, which matters because our applications take
values in a quotient `Y ⧸ V`. -/

variable {𝕜' : Type*} [DenselyNormedField 𝕜']
variable {E F : Type*}
variable [NormedAddCommGroup E] [NormedSpace 𝕜' E]
variable [SeminormedAddCommGroup F] [NormedSpace 𝕜' F]

/-- A bound on the closed unit ball bounds the operator norm:
if `‖f x‖ ≤ C` for every `x` with `‖x‖ ≤ 1`, then `‖f‖ ≤ C`. -/
lemma opNorm_le_of_unit_closedBall (f : E →L[𝕜'] F) {C : ℝ}
    (h : ∀ x : E, ‖x‖ ≤ 1 → ‖f x‖ ≤ C) : ‖f‖ ≤ C := by
  rw [← f.sSup_unitClosedBall_eq_norm]
  refine csSup_le ((Metric.nonempty_closedBall.2 zero_le_one).image _) ?_
  rintro _ ⟨x, hx, rfl⟩
  exact h x (mem_closedBall_zero_iff.mp hx)

end UnitBall

end ContinuousLinearMap

/-! ## Operator-norm bounds for the quotient maps `Submodule.mkQL` and `liftQL` -/

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

/-- Pointwise form of `norm_mkQL_le`: passing to the quotient does not
increase the norm, `‖V.mkQL y‖ ≤ ‖y‖`. -/
lemma norm_mkQL_apply_le (V : Submodule 𝕜 Y) (y : Y) : ‖V.mkQL y‖ ≤ ‖y‖ := by
  rw [V.mkQL_apply, mkQ_apply]
  exact _root_.Submodule.Quotient.norm_mk_le (S := V) y

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
