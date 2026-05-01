/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
import Mathlib.Analysis.InnerProductSpace.Spectrum

/-!
# Singular value decomposition: blueprint declaration

A standalone module declaring the singular-value-decomposition (SVD) of
compact operators between Hilbert spaces as a `sorry`-stub: there exist
orthonormal sequences `u, v` and non-negative non-increasing singular
values `σ` diagonalising the action of the operator. The proof typically
goes via the spectral theorem applied to `S* ∘ S`.
-/

namespace SVD

open ContinuousLinearMap RCLike

variable {𝕜 : Type*} [RCLike 𝕜]

/-- **Singular value decomposition for compact operators between Hilbert
spaces.** For every compact `S : H₁ →L[𝕜] H₂` there exist orthonormal
sequences `(uₖ) ⊆ H₁`, `(vₖ) ⊆ H₂` and a non-increasing sequence of
non-negative reals `σ` such that `S x = Σ σₖ ⟨x, uₖ⟩ vₖ` for every `x`. -/
theorem compactOperator_svd
    {H₁ H₂ : Type*}
    [NormedAddCommGroup H₁] [InnerProductSpace 𝕜 H₁]
    [NormedAddCommGroup H₂] [InnerProductSpace 𝕜 H₂]
    [CompleteSpace H₁] [CompleteSpace H₂]
    (S : H₁ →L[𝕜] H₂) (_hS : IsCompactOperator S) :
    ∃ (u : ℕ → H₁) (v : ℕ → H₂) (σ : ℕ → ℝ),
      Orthonormal 𝕜 u ∧ Orthonormal 𝕜 v ∧
      Antitone σ ∧ (∀ k, 0 ≤ σ k) ∧
      ∀ x : H₁, HasSum (fun k => ((σ k : 𝕜) * inner 𝕜 (u k) x) • v k) (S x) := by
  sorry

end SVD
