/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import SNumbers.Basic

/-!
# Rank of continuous linear maps, and the dimension of `ℓ₂ⁿ`

Three facts about the rank `ContinuousLinearMap.rank` defined in `SNumbers.Basic`, which
the rank axiom (S4) and its applications need:

* `ContinuousLinearMap.rank_zero`: the zero map has rank `0`;
* `ContinuousLinearMap.eq_zero_of_rank_le_zero`: rank `0` forces the zero map;
* `ContinuousLinearMap.rank_comp_comp_le`: the rank of `B ∘ L ∘ A` is at most the rank of
  the middle factor `L`.

Beside them, the dimension count behind the normalisation axiom (S5):
`SNumbers.finrank_euclideanSpace_fin'`, `dim ℓ₂ⁿ = n` over any `NontriviallyNormedField`
(Mathlib's `finrank_euclideanSpace_fin` needs `RCLike`).
-/

@[expose] public section

universe u

open scoped Cardinal

namespace ContinuousLinearMap

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]

section Rank
variable {X Y : Type*}
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]

/-- The zero map has rank `0`. -/
@[simp] lemma rank_zero : (0 : X →L[𝕜] Y).rank = 0 := by simp

/-- The only continuous linear map of rank `0` is the zero map. -/
lemma eq_zero_of_rank_le_zero {L : X →L[𝕜] Y}
    (hL : L.rank ≤ (0 : Cardinal)) : L = 0 := by
  have hbot : LinearMap.range (L : X →ₗ[𝕜] Y) = ⊥ :=
    Submodule.rank_eq_zero.mp (le_antisymm hL zero_le)
  exact ContinuousLinearMap.coe_injective (LinearMap.range_eq_bot.mp hbot)

end Rank

section CompRank
-- Comparing the ranks of operators with different domain/codomain forces a
-- single universe for `Cardinal` to be well-defined.
variable {W X Y Z : Type u}
variable [NormedAddCommGroup W] [NormedSpace 𝕜 W]
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
variable [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]

/-- The rank of a composition is bounded by the rank of the middle factor. -/
lemma rank_comp_comp_le (A : W →L[𝕜] X) (L : X →L[𝕜] Y) (B : Y →L[𝕜] Z) :
    (B.comp (L.comp A)).rank ≤ L.rank := by
  have hsub :
      LinearMap.range (B.comp (L.comp A) : W →ₗ[𝕜] Z) ≤
        Submodule.map (B : Y →ₗ[𝕜] Z) (LinearMap.range (L : X →ₗ[𝕜] Y)) := by
    intro z hz
    obtain ⟨w, hw⟩ := hz
    exact ⟨L (A w), ⟨A w, rfl⟩, by simpa using hw⟩
  calc Module.rank 𝕜 (LinearMap.range (B.comp (L.comp A) : W →ₗ[𝕜] Z))
      ≤ Module.rank 𝕜
          (Submodule.map (B : Y →ₗ[𝕜] Z) (LinearMap.range (L : X →ₗ[𝕜] Y))) :=
        Submodule.rank_mono hsub
    _ ≤ Module.rank 𝕜 (LinearMap.range (L : X →ₗ[𝕜] Y)) :=
        rank_map_le _ _

end CompRank

end ContinuousLinearMap

namespace SNumbers

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]

/-- The dimension of `ℓ₂ⁿ = EuclideanSpace 𝕜 (Fin n)` is `n`, over any
`NontriviallyNormedField`. Mathlib's `finrank_euclideanSpace_fin` proves the
same, but only for `RCLike` fields; the s-number axioms are stated over a general
field, so this variant is what the `(S5)` normalisations `_id_euclidean` need. -/
lemma finrank_euclideanSpace_fin' (n : ℕ) :
    Module.finrank 𝕜 (EuclideanSpace 𝕜 (Fin n)) = n := by
  rw [(WithLp.linearEquiv 2 𝕜 (Fin n → 𝕜)).finrank_eq, Module.finrank_pi 𝕜]
  exact Fintype.card_fin _

end SNumbers
