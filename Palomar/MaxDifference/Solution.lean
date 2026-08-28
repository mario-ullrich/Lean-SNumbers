/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
import SNumbers.MaxDifference

/-!
# The maximal difference theorem for s-numbers — proofs

This module is the *Solution* of a Palomar submission. It imports the full proof
development and discharges each statement advertised in
`Palomar.MaxDifference.Challenge`. Comparator checks that the declarations below
have exactly the same names and types as their counterparts there, and that they
use no axioms beyond `propext`, `Classical.choice` and `Quot.sound`.

The definitions the statements rest on — `ContinuousLinearMap.rank`,
`SNumbers.approximationSet`, `SNumbers.approximationNumber`, `SNumbers.L2`,
`SNumbers.hilbertSet`, `SNumbers.hilbertNumber` — are not repeated here: they
arrive through the import, from `SNumbers/Basic.lean`, `SNumbers/Approximation.lean`
and `SNumbers/Hilbert.lean`, which is where the Challenge copied them from.

Both proofs are one-liners: the mathematics sits in
`SNumbers/MaxDifference.lean`, where the bound is obtained by chaining the
growth lemma for the determinant quantities `Δₖ(S)` with the upper bound
`Δₙ₊₁(S) ≤ hₙ(S) · Δₙ(S)` and cancelling `Δₙ(S) > 0`.
-/

universe u

namespace Palomar.MaxDifference

variable {𝕜 : Type u} [RCLike 𝕜]
variable {X Y : Type u}
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]

/-- **Maximal difference theorem, sharp form of the constant.**
`aₙ(S) ≤ ((n+1)^{n+1}/nⁿ) · hₙ(S)`; see the Challenge module for the
mathematical account. -/
theorem approximationNumber_le_mul_hilbertNumber (S : X →L[𝕜] Y) (n : ℕ) :
    SNumbers.approximationNumber S n
      ≤ ((n : ℝ) + 1) ^ (n + 1) / (n : ℝ) ^ n * SNumbers.hilbertNumber S n :=
  SNumbers.approximationNumber_le_mul_hilbertNumber S n

/-- **Maximal difference theorem.** `aₙ(S) ≤ e · (n+1) · hₙ(S)`; see the
Challenge module for the mathematical account. -/
theorem approximationNumber_le_e_mul_hilbertNumber (S : X →L[𝕜] Y) (n : ℕ) :
    SNumbers.approximationNumber S n
      ≤ Real.exp 1 * ((n : ℝ) + 1) * SNumbers.hilbertNumber S n :=
  SNumbers.approximationNumber_le_e_mul_hilbertNumber S n

end Palomar.MaxDifference
