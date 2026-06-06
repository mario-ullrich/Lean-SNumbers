/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
import AddOns.Approximable
import BasicResults.SVD

/-!
# Compact ⇔ approximable on Hilbert spaces

Following Pietsch, *Eigenvalues and s-numbers*, §2.11. While "approximable
⇒ compact" holds on every normed space (`SVD.IsApproximable.isCompactOperator`),
the converse fails on Banach spaces without the approximation property
(Enflo, 1973). On Hilbert spaces, however, the Schmidt representation
shows that every compact operator is the operator-norm limit of its own
SVD truncations, hence approximable.

## Main results

* `SVD.IsCompactOperator.isApproximable` — compact ⇒ approximable
  (Hilbert-space case).
* `SVD.isApproximable_iff_isCompactOperator` — equivalence on Hilbert
  spaces.

The SVD of a compact operator itself is `SVD.IsCompactOperator.SVD` in
`BasicResults.SVD`.
-/

universe u

namespace SVD

variable {𝕜 : Type u} [RCLike 𝕜]
variable {H₁ H₂ : Type u}
variable [NormedAddCommGroup H₁] [InnerProductSpace 𝕜 H₁] [CompleteSpace H₁]
variable [NormedAddCommGroup H₂] [InnerProductSpace 𝕜 H₂] [CompleteSpace H₂]

/-- On Hilbert spaces, every compact operator is approximable. The singular
value decomposition `IsCompactOperator.SVD` produces singular values `σₙ → 0`
which, by Eckart–Young (`svd_sigma_eq_approx`), equal the approximation numbers
`aₙ(S)`; hence `aₙ(S) → 0`. -/
theorem IsCompactOperator.isApproximable {S : H₁ →L[𝕜] H₂}
    (hS : IsCompactOperator S) :
    IsApproximable S := by
  obtain ⟨σ, u, v, hσ0, hσanti, hu, hv, hut, hvt, hσlim, hsum⟩ := IsCompactOperator.SVD hS
  exact (Filter.tendsto_congr fun n =>
    (svd_sigma_eq_approx hσ0 hσanti hu hv hut hvt hsum n).symm).mpr hσlim

/-- On Hilbert spaces, approximable and compact operators coincide. -/
theorem isApproximable_iff_isCompactOperator (S : H₁ →L[𝕜] H₂) :
    IsApproximable S ↔ IsCompactOperator S :=
  ⟨IsApproximable.isCompactOperator, IsCompactOperator.isApproximable⟩

end SVD
