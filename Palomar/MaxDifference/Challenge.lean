/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
import Mathlib.LinearAlgebra.Dimension.LinearMap
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# The maximal difference theorem for s-numbers — statement surface

This module is the *Challenge* of a Palomar submission: the small, auditable
surface carrying the advertised statements. It imports nothing beyond Mathlib,
so every notion it uses is either standard or written out here. The proofs live
in `Palomar.MaxDifference.Solution`, which supplies them from the development in
`SNumbers/`; the `sorry`s below are the placeholders required by that format.

## The mathematics

An *s-number sequence* in the sense of Pietsch assigns to every bounded linear
operator `S : X →L[𝕜] Y` between Banach spaces a non-increasing sequence
`s₀(S) ≥ s₁(S) ≥ ⋯ ≥ 0` with `s₀(S) = ‖S‖`, subadditive in `S`, behaving like an
ideal under composition, vanishing on operators of rank at most `n`, and
normalised to `1` on the identity of `ℓ₂ⁿ⁺¹`. Two of these sequences bracket all
the others: the **approximation numbers** `aₙ` are the largest, and the
**Hilbert numbers** `hₙ` the smallest, so that `hₙ(S) ≤ sₙ(S) ≤ aₙ(S)` for every
s-number sequence `s`.

How far apart can the two extremes be? The theorems below answer this: they are
within a factor linear in `n`,

  `aₙ(S) ≤ ((n+1)^{n+1}/nⁿ) · hₙ(S) ≤ e · (n+1) · hₙ(S)`,

for every bounded operator between normed spaces over `ℝ` or `ℂ`. Since `hₙ` is
the smallest s-number sequence, this bounds the gap between *any* two s-number
sequences by the same factor. The factor `n+1` is order-optimal.

## The definitions restated here

* `ContinuousLinearMap.rank` — the rank of a continuous linear map.
* `SNumbers.approximationSet`, `SNumbers.approximationNumber` — the
  approximation numbers `aₙ`.
* `SNumbers.L2`, `SNumbers.hilbertSet`, `SNumbers.hilbertNumber` — the Hilbert
  numbers `hₙ`.

Each is reproduced verbatim from the development, so that Comparator can match
it against its counterpart there.

## Index convention

Indexing is **0-based**, shifted by one from Pietsch's original convention:
Pietsch's `s₁(S) = ‖S‖` is our `s₀(S)`. This matches the convention used for
`n`-widths and in information-based complexity.
-/

universe u

open scoped Cardinal

namespace ContinuousLinearMap

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {X Y : Type*}
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]

/-- The rank of a continuous linear map, defined as the dimension of its
range as a `Cardinal`. -/
noncomputable abbrev rank (S : X →L[𝕜] Y) : Cardinal :=
  LinearMap.rank (S : X →ₗ[𝕜] Y)

end ContinuousLinearMap

namespace SNumbers

section Approximation

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]
variable {W X Y Z : Type u}
variable [NormedAddCommGroup W] [NormedSpace 𝕜 W]
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
variable [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]

/-- The set of approximation residuals `‖S - L‖` over operators `L` of rank
at most `n`. -/
def approximationSet (S : X →L[𝕜] Y) (n : ℕ) : Set ℝ :=
  {r | ∃ L : X →L[𝕜] Y, L.rank ≤ (n : Cardinal) ∧ r = ‖S - L‖}

/-- The `n`-th **approximation number** of a continuous linear map: the
infimum of `‖S - L‖` over operators `L` of rank at most `n`. -/
noncomputable def approximationNumber (S : X →L[𝕜] Y) (n : ℕ) : ℝ :=
  sInf (approximationSet S n)

end Approximation

section Hilbert

variable {𝕜 : Type u} [RCLike 𝕜]
variable {X Y W Z : Type u}
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
variable [NormedAddCommGroup W] [NormedSpace 𝕜 W]
variable [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]

/-- A model of `ℓ₂` over `𝕜`: the space `lp` with exponent `2` over `ℕ`.
For `RCLike 𝕜` this is a Hilbert space, and—crucially—it lives in the same
universe as `X` and `Y`. -/
abbrev L2 (𝕜 : Type*) [RCLike 𝕜] : Type _ := lp (fun _ : ℕ => 𝕜) 2

/-- The set of ratios `a_n (B ∘ S ∘ A) / (‖B‖ ‖A‖)` over nonzero
`A : ℓ₂ → X`, `B : Y → ℓ₂`, whose supremum is the Hilbert number. -/
def hilbertSet (S : X →L[𝕜] Y) (n : ℕ) : Set ℝ :=
  {r | ∃ (A : L2 𝕜 →L[𝕜] X) (B : Y →L[𝕜] L2 𝕜),
      A ≠ 0 ∧ B ≠ 0 ∧
      r = approximationNumber (B.comp (S.comp A)) n / (‖B‖ * ‖A‖)}

/-- The `n`-th **Hilbert number** of a continuous linear map between
`𝕜`-Banach spaces (`𝕜 = ℝ` or `ℂ`).

`h_n S = sup { a_n (B ∘ S ∘ A) / (‖B‖ * ‖A‖) :
                  A : ℓ₂ →L X, B : Y →L ℓ₂, A ≠ 0, B ≠ 0 }`. -/
noncomputable def hilbertNumber (S : X →L[𝕜] Y) (n : ℕ) : ℝ :=
  sSup (hilbertSet S n)

end Hilbert

end SNumbers

namespace Palomar.MaxDifference

variable {𝕜 : Type u} [RCLike 𝕜]
variable {X Y : Type u}
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]

/-- **Maximal difference theorem, sharp form of the constant.**

For every bounded linear operator `S : X →L[𝕜] Y` between normed spaces over
`𝕜 = ℝ` or `ℂ`, and every `n`,

  `aₙ(S) ≤ ((n+1)^{n+1} / nⁿ) · hₙ(S)`.

The approximation numbers `aₙ` are the largest s-number sequence and the
Hilbert numbers `hₙ` the smallest, so this bounds the gap between the two
extremes of the Pietsch scale — and hence between any two s-number sequences.
At `n = 0` the constant is `1`, matching `a₀(S) = ‖S‖ = h₀(S)`. -/
theorem approximationNumber_le_mul_hilbertNumber (S : X →L[𝕜] Y) (n : ℕ) :
    SNumbers.approximationNumber S n
      ≤ ((n : ℝ) + 1) ^ (n + 1) / (n : ℝ) ^ n * SNumbers.hilbertNumber S n :=
  sorry

/-- **Maximal difference theorem.**

  `aₙ(S) ≤ e · (n+1) · hₙ(S)`

for every bounded linear operator `S : X →L[𝕜] Y` between normed spaces over
`𝕜 = ℝ` or `ℂ`, and every `n`. This is the previous bound weakened by
`(n+1)^{n+1}/nⁿ ≤ e · (n+1)`: the largest s-numbers exceed the smallest ones by
at most a factor linear in `n`. The linear growth is order-optimal. -/
theorem approximationNumber_le_e_mul_hilbertNumber (S : X →L[𝕜] Y) (n : ℕ) :
    SNumbers.approximationNumber S n
      ≤ Real.exp 1 * ((n : ℝ) + 1) * SNumbers.hilbertNumber S n :=
  sorry

end Palomar.MaxDifference
