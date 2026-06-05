/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic

/-!
# Spectral engine, Phase 1: the continuous functional calculus of `S*S`

This file builds the **continuous functional calculus** (CFC) for the
positive self-adjoint operator `P = S* ∘ S` on a *complex* Hilbert space, as
the first step of the spectral-projection construction
(`SpectralRepresentation.exists_spectral_projection`).

Working over `ℂ` (the scalar-field choice agreed for the engine; the real
case is deferred), the operator algebra `H₁ →L[ℂ] H₁` is a C⋆-algebra
(`Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap`), so Mathlib's
continuous functional calculus applies. Since `P` is self-adjoint its
spectrum is real, and the natural CFC is the **real** one: a `⋆`-algebra
homomorphism

`Φ : C(spectrum ℝ P, ℝ) →⋆ₐ[ℝ] (H₁ →L[ℂ] H₁)`

sending the coordinate function to `P`. Real continuous functions of `P` are
exactly what the spectral measure (Phase 2) integrates, and the spectral
projection is `Φ` of an indicator (after the Borel extension).

## Main definitions

* `SpectralRepresentation.cfcStarHom S` — the homomorphism `Φ` above,
  `cfcHom` of `S*S`.

## Main results

* `cfcStarHom_apply_id` — `Φ(coord) = S*S` (the coordinate function maps to
  the operator).
* `cfcStarHom_isSelfAdjoint` — every `Φ(g)` is self-adjoint.
* `cfcStarHom_norm` — `Φ` is isometric: `‖Φ g‖ = ‖g‖`.
* `cfcStarHom_continuous` — `Φ` is continuous.

All other algebraic properties (`map_add`, `map_mul`, `map_one`, `map_star`,
`map_smul`) come for free from the `StarAlgHom` structure.

Mathlib reuse: `cfcHom`, `cfcHom_id`, `cfcHom_predicate`, `norm_cfcHom`,
`cfcHom_continuous`, and the C⋆-algebra instance on `H₁ →L[ℂ] H₁`.
-/

open ContinuousLinearMap

namespace SpectralRepresentation

variable {H₁ H₂ : Type*}
variable [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [CompleteSpace H₁]
variable [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] [CompleteSpace H₂]

/-- `S* ∘ S` is self-adjoint (local copy with `ℂ`-independent universes, so
the scalar field `ℂ : Type 0` need not share a universe with `H₁`). -/
private theorem isSelfAdjoint_sq (S : H₁ →L[ℂ] H₂) :
    IsSelfAdjoint ((adjoint S).comp S) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff', ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.adjoint_adjoint]

/-- The **continuous functional calculus of `S* ∘ S`** as a `⋆`-algebra
homomorphism `Φ : C(spectrum ℝ (S*S), ℝ) →⋆ₐ[ℝ] (H₁ →L[ℂ] H₁)`.

This is `cfcHom` applied to the self-adjoint operator `S* ∘ S`; it sends a
real continuous function `g` on the spectrum to the operator `g(S*S)`. -/
noncomputable def cfcStarHom (S : H₁ →L[ℂ] H₂) :
    C(spectrum ℝ ((adjoint S).comp S), ℝ) →⋆ₐ[ℝ] (H₁ →L[ℂ] H₁) :=
  cfcHom (isSelfAdjoint_sq S)

/-- `Φ` sends the coordinate function `λ ↦ λ` to the operator `S* ∘ S`. -/
theorem cfcStarHom_apply_id (S : H₁ →L[ℂ] H₂) :
    cfcStarHom S ((ContinuousMap.id ℝ).restrict (spectrum ℝ ((adjoint S).comp S)))
      = (adjoint S).comp S :=
  cfcHom_id (isSelfAdjoint_sq S)

/-- Every `Φ(g)` is self-adjoint (real functions of a self-adjoint operator). -/
theorem cfcStarHom_isSelfAdjoint (S : H₁ →L[ℂ] H₂)
    (g : C(spectrum ℝ ((adjoint S).comp S), ℝ)) :
    IsSelfAdjoint (cfcStarHom S g) :=
  cfcHom_predicate (isSelfAdjoint_sq S) g

/-- `Φ` is isometric: `‖Φ g‖ = ‖g‖`. -/
theorem cfcStarHom_norm (S : H₁ →L[ℂ] H₂)
    (g : C(spectrum ℝ ((adjoint S).comp S), ℝ)) :
    ‖cfcStarHom S g‖ = ‖g‖ :=
  norm_cfcHom ((adjoint S).comp S) g (isSelfAdjoint_sq S)

/-- `Φ` is continuous. -/
theorem cfcStarHom_continuous (S : H₁ →L[ℂ] H₂) :
    Continuous (cfcStarHom S) :=
  cfcHom_continuous (isSelfAdjoint_sq S)

end SpectralRepresentation
