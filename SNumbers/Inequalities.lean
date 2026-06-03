/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
import SNumbers.Hilbert
import SNumbers.Uniqueness

/-!
# Comparison of `s`-number sequences (general spaces)

Pietsch's classical extremality result: among all `s`-number sequences, the
**Hilbert numbers** `hₙ` are the smallest and the **approximation numbers**
`aₙ` are the largest. This file collects the comparison statements that hold
for operators between **arbitrary** `𝕜`-Banach spaces.

## Main results

* `hilbertNumber_le_sn` — lower bound `hₙ(S) ≤ sₙ(S)`.
* `hilbertNumber_le_sn_le_approximationNumber` — Pietsch's sandwich theorem
  `hₙ(S) ≤ sₙ(S) ≤ aₙ(S)`.

## Where the ingredients live

The two halves of the sandwich rest on results in their natural homes:

* the upper bound `sₙ(S) ≤ aₙ(S)` is `SNumbers.sn_le_approximationNumber`
  (in `SNumbers.Approximation` — "`aₙ` is the largest");
* reverse homogeneity `‖c‖ · sₙ(T) ≤ sₙ(c • T)` is `SNumbers.norm_smul_le_sn`
  (in `SNumbers.Basic`);
* the Hilbert-space coincidence `aₙ = sₙ`, used to bound each ratio
  `aₙ(B ∘ S ∘ A)/(‖B‖‖A‖)` defining `hₙ`, is
  `SNumbers.allSNumbers_eq_on_HilbertSpace` / the lower bound
  `SNumbers.approximationNumber_le_sn` (in `SNumbers.Uniqueness`, Hilbert
  spaces only, resting on the singular value decomposition).

## Proof strategy for `hₙ ≤ sₙ`

Each ratio `aₙ(B ∘ S ∘ A)/(‖B‖‖A‖)` defining `hₙ(S)` has `B ∘ S ∘ A` an
operator **between Hilbert spaces** (`ℓ₂ → ℓ₂`), so the coincidence gives
`aₙ(B ∘ S ∘ A) ≤ sₙ(B ∘ S ∘ A)`; the (S3) ideal property then bounds this by
`‖B‖ · sₙ(S) · ‖A‖`. Dividing by `‖B‖‖A‖` and taking the supremum over the
admissible `(A, B)` yields `hₙ(S) ≤ sₙ(S)`.
-/

universe u

open ContinuousLinearMap

namespace SNumbers

variable {𝕜 : Type u} [RCLike 𝕜]
variable {X Y : Type u}
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]

/-- **Lower bound.** The Hilbert numbers are the smallest `s`-number
sequence: `hₙ(S) ≤ sₙ(S)` for every `s`-number sequence `s`. -/
theorem hilbertNumber_le_sn {s : Family 𝕜} (hs : IsSNumberSequence s)
    (S : X →L[𝕜] Y) (n : ℕ) :
    hilbertNumber S n ≤ s S n := by
  rw [hilbertNumber_def]
  refine Real.sSup_le ?_ (hs.nonneg S n)
  rintro r ⟨A, B, hA, hB, rfl⟩
  have hpos : 0 < ‖B‖ * ‖A‖ := mul_pos (norm_pos_iff.mpr hB) (norm_pos_iff.mpr hA)
  rw [div_le_iff₀ hpos]
  -- `B ∘ S ∘ A : ℓ₂ → ℓ₂` is between Hilbert spaces, so `aₙ = sₙ` on it.
  calc approximationNumber (B.comp (S.comp A)) n
      ≤ s (B.comp (S.comp A)) n := approximationNumber_le_sn hs (B.comp (S.comp A)) n
    _ ≤ ‖B‖ * s S n * ‖A‖ := hs.ideal A S B n
    _ = s S n * (‖B‖ * ‖A‖) := by ring

/-- **Pietsch's sandwich theorem.** For every `s`-number sequence `s` and
every bounded operator `S : X → Y`: `hₙ(S) ≤ sₙ(S) ≤ aₙ(S)`. -/
theorem hilbertNumber_le_sn_le_approximationNumber {s : Family 𝕜}
    (hs : IsSNumberSequence s) (S : X →L[𝕜] Y) (n : ℕ) :
    hilbertNumber S n ≤ s S n ∧ s S n ≤ approximationNumber S n :=
  ⟨hilbertNumber_le_sn hs S n, sn_le_approximationNumber hs S n⟩

end SNumbers
