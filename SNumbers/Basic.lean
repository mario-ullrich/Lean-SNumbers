/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Dimension.LinearMap

/-!
# s-Numbers: rank definition and the Pietsch axioms

This file collects:

* `ContinuousLinearMap.rank` — a thin wrapper around `LinearMap.rank` providing
  dot notation for continuous linear maps. Auxiliary rank facts live in
  `SNumbers.Helpers`.
* The five Pietsch axioms (S1)–(S5) characterising an *s-number sequence*,
  packaged in the structure `IsSNumberSequence`.
* The strengthening (S5') and the structure `IsStrictSNumberSequence`,
  introduced *after* the standard axioms.

An s-number sequence assigns to every bounded linear operator
`S : X →L[𝕜] Y` between (real or complex) Banach spaces a sequence
`(s_n S)_{n ∈ ℕ}` of non-negative reals satisfying:

* (S1) `0 ≤ s (n+1) S ≤ s n S` and `s 0 S = ‖S‖`,
* (S2) `s n (S + T) ≤ s n S + ‖T‖`,
* (S3) `s n (B ∘ S ∘ A) ≤ ‖B‖ * s n S * ‖A‖`,
* (S4) `s n S = 0` whenever `rank S ≤ n`,
* (S5) `s n (id_{ℓ₂^{n+1}}) = 1`.

A *strict* s-number sequence additionally satisfies the strengthening
(S5') `s n (id_X) = 1` for every `X` with `dim X > n`, not just `ℓ₂^{n+1}`.

## Index convention

We use **0-based indexing**, shifted by one from Pietsch's original convention:
Pietsch's `s_1 S = ‖S‖` is our `s_0 S`, and Pietsch's `s_{n+1}` is our `s_n`.

## Implementation notes

The carrier is a universe-polymorphic family — see `Family` — mirroring
Pietsch's class function on `𝓛 = ⋃_{X,Y} 𝓛(X,Y)`. Completeness is **not**
required at the level of axioms; downstream constructions add
`[CompleteSpace X]` where needed.
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

/-- The carrier of an s-number candidate: a family of `ℕ → ℝ` sequences
indexed by operators between normed `𝕜`-spaces. -/
abbrev Family (𝕜 : Type u) [NontriviallyNormedField 𝕜] :=
  ∀ {X Y : Type u} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
      [NormedAddCommGroup Y] [NormedSpace 𝕜 Y],
      (X →L[𝕜] Y) → ℕ → ℝ

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]

/-- (S1) `s` takes non-negative values. -/
def Nonneg (s : Family 𝕜) : Prop :=
  ∀ {X Y : Type u} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
      [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] (S : X →L[𝕜] Y) (n : ℕ),
    0 ≤ s S n

/-- (S1) The first value equals the operator norm: `s 0 S = ‖S‖`. -/
def NormAtZero (s : Family 𝕜) : Prop :=
  ∀ {X Y : Type u} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
      [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] (S : X →L[𝕜] Y),
    s S 0 = ‖S‖

/-- (S1) The sequence is non-increasing in `n`. -/
def Antitone (s : Family 𝕜) : Prop :=
  ∀ {X Y : Type u} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
      [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] (S : X →L[𝕜] Y) (n : ℕ),
    s S (n + 1) ≤ s S n

/-- (S2) Subadditivity: `s n (S + T) ≤ s n S + ‖T‖`. -/
def Subadditive (s : Family 𝕜) : Prop :=
  ∀ {X Y : Type u} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
      [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] (S T : X →L[𝕜] Y) (n : ℕ),
    s (S + T) n ≤ s S n + ‖T‖

/-- (S3) Ideal property: `s n (B ∘ S ∘ A) ≤ ‖B‖ * s n S * ‖A‖`. -/
def IdealLike (s : Family 𝕜) : Prop :=
  ∀ {W X Y Z : Type u} [NormedAddCommGroup W] [NormedSpace 𝕜 W]
      [NormedAddCommGroup X] [NormedSpace 𝕜 X]
      [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
      [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]
      (A : W →L[𝕜] X) (S : X →L[𝕜] Y) (B : Y →L[𝕜] Z) (n : ℕ),
    s (B.comp (S.comp A)) n ≤ ‖B‖ * s S n * ‖A‖

/-- (S4) Vanishing on operators of rank at most `n`. -/
def VanishesOnLowRank (s : Family 𝕜) : Prop :=
  ∀ {X Y : Type u} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
      [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] (S : X →L[𝕜] Y) (n : ℕ),
    S.rank ≤ (n : Cardinal) → s S n = 0

/-- (S5) Normalisation: `s n (id_{ℓ₂^{n+1}}) = 1`. -/
def NormalisedAtId (s : Family 𝕜) : Prop :=
  ∀ (n : ℕ), s (ContinuousLinearMap.id 𝕜 (EuclideanSpace 𝕜 (Fin (n + 1)))) n = 1

/-- (S5') **Strict normalisation**: `s n (id_X) = 1` whenever `dim X > n`.

A strengthening of (S5), which only fixes the value on the specific Hilbert
space `ℓ₂^{n+1}`. Sequences satisfying (S5') have `s n (id_X) = 1` on *every*
`X` with finite dimension strictly above `n`; specialising to
`X = ℓ₂^{n+1}` (where `dim = n + 1 > n`) recovers (S5). -/
def StrictlyNormalisedAtId (s : Family 𝕜) : Prop :=
  ∀ {X : Type u} [NormedAddCommGroup X] [NormedSpace 𝕜 X] (n : ℕ),
      n < Module.finrank 𝕜 X → s (ContinuousLinearMap.id 𝕜 X) n = 1

/-- An **s-number sequence** in the sense of Pietsch. -/
structure IsSNumberSequence (s : Family 𝕜) : Prop where
  /-- (S1) `s` takes non-negative values. -/
  nonneg : Nonneg s
  /-- (S1) `s 0 S = ‖S‖`. -/
  norm_at_zero : NormAtZero s
  /-- (S1) `s` is antitone in `n`. -/
  antitone : Antitone s
  /-- (S2) Subadditivity. -/
  subadditive : Subadditive s
  /-- (S3) Ideal property. -/
  ideal : IdealLike s
  /-- (S4) Vanishes on operators of rank at most `n`. -/
  vanishes_on_low_rank : VanishesOnLowRank s
  /-- (S5) Normalised on `id_{ℓ₂^{n+1}}`. -/
  normalised_at_id : NormalisedAtId s

/-! ### Strict s-number sequences

The structure `IsStrictSNumberSequence` packages an `IsSNumberSequence` together
with the (S5') strengthening above. It is independent of the standard axioms
(S1)–(S5): the latter form the classical Pietsch theory by themselves. -/

/-- A **strict s-number sequence**: an s-number sequence satisfying the
stronger normalisation (S5') `s n (id_X) = 1` for every `X` with `dim X > n`,
not just on `ℓ₂^{n+1}`. -/
structure IsStrictSNumberSequence (s : Family 𝕜) : Prop extends IsSNumberSequence s where
  /-- (S5') `s n (id_X) = 1` whenever `dim X > n`. -/
  strictly_normalised_at_id : StrictlyNormalisedAtId s

end SNumbers
