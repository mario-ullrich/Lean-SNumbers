/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
import BasicResults.Determinant
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Triangular determinant factorisation through `ℓ₂ⁿ⁺¹`

Domain-general linear-algebra infrastructure for the Gelfand/Kolmogorov product (determinant)
bounds in `SNumbers.Inequalities`. Given an operator `S : X →L[𝕜] Y`, a family of unit vectors
`xⱼ ∈ X`, and a family of norm-`≤1` functionals `gᵢ ∈ Y*` whose Gram-type matrix `[gᵢ(S xⱼ)]` is
triangular, one builds contraction-like operators `A' : ℓ₂ⁿ⁺¹ → X`, `B' : Y → ℓ₂ⁿ⁺¹` of norm
`≤ √(n+1)` with `‖det(B'∘S∘A')‖ = ∏ₖ ‖gₖ(S xₖ)‖`. None of this involves `s`-numbers.

## Main results

* `exists_closed_codim_forall_eq_zero` — the common kernel of `k` functionals `gᵢ ∘ S` is closed
  of codimension `≤ k`.
* `exists_factorisation_of_flag` — the determinant of a triangular flag equals the product of its
  diagonal norms, realised through `ℓ₂ⁿ⁺¹` with both factors of norm `≤ √(n+1)`.
-/

universe u

namespace TriangularFactorisation

variable {𝕜 : Type u} [RCLike 𝕜]
variable {X : Type u} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable {Y : Type u} [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]

/-- The common kernel `{x | ∀ i, gᵢ(S x) = 0}` of `k` continuous functionals `gᵢ ∘ S` is a
closed subspace of codimension `≤ k` (kernel of `x ↦ (gᵢ(S x))ᵢ : X → 𝕜ᵏ`). -/
lemma exists_closed_codim_forall_eq_zero (S : X →L[𝕜] Y) {k : ℕ}
    (g : Fin k → (Y →L[𝕜] 𝕜)) :
    ∃ M : Submodule 𝕜 X, IsClosed (M : Set X) ∧
      Module.rank 𝕜 (X ⧸ M) ≤ (k : Cardinal) ∧ (∀ x ∈ M, ∀ i, g i (S x) = 0) := by
  set Φ : X →L[𝕜] (Fin k → 𝕜) := ContinuousLinearMap.pi (fun i => (g i).comp S) with hΦ
  refine ⟨LinearMap.ker (Φ : X →ₗ[𝕜] (Fin k → 𝕜)), Φ.isClosed_ker, ?_, ?_⟩
  · rw [(LinearMap.quotKerEquivRange (Φ : X →ₗ[𝕜] (Fin k → 𝕜))).rank_eq]
    calc Module.rank 𝕜 (LinearMap.range (Φ : X →ₗ[𝕜] (Fin k → 𝕜)))
        ≤ Module.rank 𝕜 (Fin k → 𝕜) := Submodule.rank_le _
      _ = (k : Cardinal) := rank_fin_fun k
  · intro x hx i
    have h0 := congrFun (LinearMap.mem_ker.mp hx) i
    simpa [hΦ] using h0

/-- Package functionals `g₀,…,gₙ ∈ B_{Y*}` into `B' : Y → ℓ₂ⁿ⁺¹`, `y ↦ (gᵢ y)ᵢ`, with
`‖B'‖ ≤ √(n+1)`. -/
private lemma exists_clm_to_euclideanSpace {n : ℕ} (g : Fin (n + 1) → (Y →L[𝕜] 𝕜))
    (hg : ∀ i, ‖g i‖ ≤ 1) :
    ∃ B' : Y →L[𝕜] EuclideanSpace 𝕜 (Fin (n + 1)),
      ‖B'‖ ≤ Real.sqrt ((n : ℝ) + 1) ∧ ∀ y j, B' y j = g j y := by
  classical
  set B' : Y →L[𝕜] EuclideanSpace 𝕜 (Fin (n + 1)) :=
    ∑ i, (g i).smulRight (EuclideanSpace.single i (1 : 𝕜)) with hB'
  have happ : ∀ y j, B' y j = g j y := by
    intro y j
    simp [hB', ContinuousLinearMap.sum_apply, ContinuousLinearMap.smulRight_apply,
      Pi.single_apply]
  refine ⟨B', ?_, happ⟩
  refine ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) fun y => ?_
  rw [EuclideanSpace.norm_eq,
    show Real.sqrt ((n : ℝ) + 1) * ‖y‖ = Real.sqrt (((n : ℝ) + 1) * ‖y‖ ^ 2) by
      rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (norm_nonneg _)]]
  refine Real.sqrt_le_sqrt ?_
  have hle : ∀ j : Fin (n + 1), ‖B' y j‖ ^ 2 ≤ ‖y‖ ^ 2 := by
    intro j
    have h1 : ‖g j y‖ ≤ ‖y‖ := by
      refine ((g j).le_opNorm y).trans ?_
      calc ‖g j‖ * ‖y‖ ≤ 1 * ‖y‖ := mul_le_mul_of_nonneg_right (hg j) (norm_nonneg _)
        _ = ‖y‖ := one_mul _
    rw [happ]; nlinarith [norm_nonneg (g j y)]
  refine (Finset.sum_le_sum fun j _ => hle j).trans_eq ?_
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]; ring

/-- Package vectors `x₀,…,xₙ ∈ B_X` into `A' : ℓ₂ⁿ⁺¹ → X`, `eⱼ ↦ xⱼ`, with `‖A'‖ ≤ √(n+1)`
(Cauchy–Schwarz `∑ⱼ|cⱼ| ≤ √(n+1)·‖c‖₂`). -/
private lemma exists_clm_from_euclideanSpace {n : ℕ} (x : Fin (n + 1) → X)
    (hx : ∀ j, ‖x j‖ ≤ 1) :
    ∃ A' : EuclideanSpace 𝕜 (Fin (n + 1)) →L[𝕜] X,
      ‖A'‖ ≤ Real.sqrt ((n : ℝ) + 1) ∧
      ∀ k, A' (EuclideanSpace.single k (1 : 𝕜)) = x k := by
  classical
  set A' : EuclideanSpace 𝕜 (Fin (n + 1)) →L[𝕜] X :=
    ∑ j, (innerSL 𝕜 (EuclideanSpace.single j (1 : 𝕜))).smulRight (x j) with hA'
  have happ : ∀ c : EuclideanSpace 𝕜 (Fin (n + 1)), A' c = ∑ j, c j • x j := by
    intro c
    simp only [hA', ContinuousLinearMap.sum_apply, ContinuousLinearMap.smulRight_apply,
      innerSL_apply_apply, EuclideanSpace.inner_single_left, map_one, one_mul]
  refine ⟨A', ?_, fun k => ?_⟩
  · refine ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) fun c => ?_
    rw [happ]
    have hsum : ‖∑ j, c j • x j‖ ≤ ∑ j, ‖c j‖ := by
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
      rw [norm_smul]
      calc ‖c j‖ * ‖x j‖ ≤ ‖c j‖ * 1 := mul_le_mul_of_nonneg_left (hx j) (norm_nonneg _)
        _ = ‖c j‖ := mul_one _
    have hcs : (∑ j, ‖c j‖) ^ 2 ≤ ((n : ℝ) + 1) * ‖c‖ ^ 2 := by
      have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
        (fun j : Fin (n + 1) => ‖c j‖) (fun _ => (1 : ℝ))
      have hcnorm : ‖c‖ ^ 2 = ∑ j, ‖c j‖ ^ 2 := by
        rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
      rw [hcnorm]
      simpa [Finset.card_univ, Fintype.card_fin, mul_comm] using h
    have hnn : 0 ≤ ∑ j, ‖c j‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
    refine hsum.trans ?_
    rw [show Real.sqrt ((n : ℝ) + 1) * ‖c‖ = Real.sqrt (((n : ℝ) + 1) * ‖c‖ ^ 2) by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (norm_nonneg _)],
      ← Real.sqrt_sq hnn]
    exact Real.sqrt_le_sqrt hcs
  · rw [happ]
    simp

/-- **Determinant of a triangular flag.** Given `xⱼ ∈ B_X`, `gᵢ ∈ B_{Y*}` and that `[gᵢ(S xⱼ)]`
is triangular (lower `i<j ⇒ 0`, or upper `j<i ⇒ 0`), assemble `A' eⱼ = xⱼ`, `B' y = (gᵢ y)ᵢ`
(norm `≤ √(n+1)`); then `‖det(B'∘S∘A')‖ = ∏ₖ ‖gₖ(S xₖ)‖`. Shared by the Gelfand and Kolmogorov
product bounds. -/
lemma exists_factorisation_of_flag (S : X →L[𝕜] Y) (n : ℕ)
    (x : Fin (n + 1) → X) (g : Fin (n + 1) → (Y →L[𝕜] 𝕜))
    (hx : ∀ j, ‖x j‖ ≤ 1) (hg : ∀ i, ‖g i‖ ≤ 1)
    (htri : (∀ i j : Fin (n + 1), i < j → g i (S (x j)) = 0) ∨
      (∀ i j : Fin (n + 1), j < i → g i (S (x j)) = 0)) :
    ∃ (A' : EuclideanSpace 𝕜 (Fin (n + 1)) →L[𝕜] X)
      (B' : Y →L[𝕜] EuclideanSpace 𝕜 (Fin (n + 1))),
      ‖A'‖ ≤ Real.sqrt ((n : ℝ) + 1) ∧ ‖B'‖ ≤ Real.sqrt ((n : ℝ) + 1) ∧
      ‖LinearMap.det (B'.comp (S.comp A') :
          EuclideanSpace 𝕜 (Fin (n + 1)) →ₗ[𝕜] EuclideanSpace 𝕜 (Fin (n + 1)))‖
        = ∏ k, ‖g k (S (x k))‖ := by
  classical
  obtain ⟨A', hA', hAbasis⟩ := exists_clm_from_euclideanSpace (𝕜 := 𝕜) x hx
  obtain ⟨B', hB', hBcoord⟩ := exists_clm_to_euclideanSpace g hg
  refine ⟨A', B', hA', hB', ?_⟩
  set b := EuclideanSpace.basisFun (Fin (n + 1)) 𝕜 with hb
  have hmat : ∀ i j, LinearMap.toMatrix b.toBasis b.toBasis
      (B'.comp (S.comp A') : EuclideanSpace 𝕜 (Fin (n + 1)) →ₗ[𝕜] _) i j = g i (S (x j)) := by
    intro i j
    rw [LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,
      OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply,
      ContinuousLinearMap.coe_coe, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.comp_apply, hAbasis j, hBcoord]
  have key : LinearMap.det (B'.comp (S.comp A') :
      EuclideanSpace 𝕜 (Fin (n + 1)) →ₗ[𝕜] _) = ∏ k, g k (S (x k)) := by
    rw [← LinearMap.det_toMatrix b.toBasis]
    rcases htri with hlo | hup
    · rw [Matrix.det_of_lowerTriangular _ fun i j h =>
        (hmat i j).trans (hlo i j (OrderDual.toDual_lt_toDual.mp h))]
      exact Finset.prod_congr rfl fun k _ => hmat k k
    · rw [Matrix.det_of_upperTriangular fun i j h => (hmat i j).trans (hup i j h)]
      exact Finset.prod_congr rfl fun k _ => hmat k k
  rw [key, norm_prod]

end TriangularFactorisation
