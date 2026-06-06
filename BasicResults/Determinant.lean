/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.SingularValues
import Mathlib.LinearAlgebra.Determinant

/-!
# Determinant of an adjoint, and `‖det‖` as a product of singular values

* `LinearMap.det_adjoint` — `det T* = conj (det T)`, for an endomorphism of a
  finite-dimensional inner product space. In an orthonormal basis the matrix of
  the adjoint is the conjugate transpose, and `det Aᴴ = conj (det A)`.
* `LinearMap.norm_det_eq_prod_singularValues` — `‖det T‖ = ∏ₖ σₖ(T)`, where
  `σₖ` are Mathlib's eigenvalue-defined singular values: `‖det T‖² = det(T*∘T)
  = ∏ eigenvalues(T*∘T) = ∏ σₖ²`. This is pure linear algebra over Mathlib's
  singular values (no `s`-number theory); the `s`-number reading
  `∏ aₖ(T) = ‖det T‖` is then immediate on Hilbert spaces.
-/

open LinearMap
open scoped ComplexConjugate

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]

/-- **`det T* = conj (det T)`.** In an orthonormal basis the matrix of the
adjoint is the conjugate transpose, and `det Aᴴ = conj (det A)`. -/
theorem LinearMap.det_adjoint (T : E →ₗ[𝕜] E) :
    LinearMap.det (adjoint T) = conj (LinearMap.det T) := by
  set v := stdOrthonormalBasis 𝕜 E with hv
  rw [← LinearMap.det_toMatrix v.toBasis (adjoint T), LinearMap.toMatrix_adjoint v v T,
    Matrix.det_conjTranspose, LinearMap.det_toMatrix v.toBasis T, starRingEnd_apply]

/-- **`‖det T‖ = ∏ₖ σₖ(T)`** for an endomorphism of a finite-dimensional inner
product space, with `σₖ` Mathlib's singular values. Indeed
`‖det T‖² = det(T*∘T) = ∏ eigenvalues(T*∘T) = ∏ σₖ²`, using `det_adjoint`,
`det_eq_prod_eigenvalues` and `sq_singularValues_fin`. -/
theorem LinearMap.norm_det_eq_prod_singularValues (T : E →ₗ[𝕜] E) :
    ‖LinearMap.det T‖ = ∏ k ∈ Finset.range (Module.finrank 𝕜 E), T.singularValues k := by
  have hnn : 0 ≤ ∏ k ∈ Finset.range (Module.finrank 𝕜 E), T.singularValues k :=
    Finset.prod_nonneg fun k _ => T.singularValues_nonneg k
  have hkey : ‖LinearMap.det T‖ ^ 2
      = ∏ i : Fin (Module.finrank 𝕜 E), T.singularValues ↑i ^ 2 := by
    have e1 : LinearMap.det (LinearMap.adjoint T ∘ₗ T)
        = ∏ i : Fin (Module.finrank 𝕜 E), ((T.singularValues ↑i ^ 2 : ℝ) : 𝕜) := by
      rw [LinearMap.IsSymmetric.det_eq_prod_eigenvalues T.isSymmetric_adjoint_comp_self rfl]
      exact Finset.prod_congr rfl fun i _ => by rw [T.sq_singularValues_fin rfl i]
    have e2 : LinearMap.det (LinearMap.adjoint T ∘ₗ T)
        = ((‖LinearMap.det T‖ ^ 2 : ℝ) : 𝕜) := by
      rw [LinearMap.det_comp, LinearMap.det_adjoint, RCLike.conj_mul]; push_cast; ring
    have e3 : ((‖LinearMap.det T‖ ^ 2 : ℝ) : 𝕜)
        = ((∏ i : Fin (Module.finrank 𝕜 E), T.singularValues ↑i ^ 2 : ℝ) : 𝕜) := by
      rw [← e2, e1]; push_cast; ring
    exact_mod_cast e3
  have hsq : ‖LinearMap.det T‖ ^ 2
      = (∏ k ∈ Finset.range (Module.finrank 𝕜 E), T.singularValues k) ^ 2 := by
    rw [← Finset.prod_pow,
      ← Fin.prod_univ_eq_prod_range (fun k => T.singularValues k ^ 2) (Module.finrank 𝕜 E), hkey]
  rw [← Real.sqrt_sq (norm_nonneg _), hsq, Real.sqrt_sq hnn]
