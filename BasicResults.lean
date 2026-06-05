/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
import BasicResults.Auerbach
import BasicResults.SVD
import BasicResults.Determinant
import BasicResults.Spectral.Complexification
import BasicResults.Spectral.MultiplicationOperator
import BasicResults.Spectral.Representation
import BasicResults.Spectral.FunctionalCalculus
import BasicResults.Spectral.MonotoneConvergence
import BasicResults.Spectral.Projection

/-!
# Basic results

A small library of generic linear-algebra / functional-analysis results
that support the s-numbers framework:

* `BasicResults.Auerbach` — Auerbach's lemma (every finite-dimensional
  normed space over `ℝ` admits an Auerbach basis).
* `BasicResults.SVD` — the singular value decomposition of a (compact)
  Hilbert-space operator via the singular-value iteration, together with
  the **scalar factorisation** `SVD.exists_scalar_factorisation` that the
  s-numbers uniqueness theorem (`SNumbers.Uniqueness`) consumes.
  Following Pietsch, *Eigenvalues and s-numbers*, §2.11.
* `BasicResults.Determinant` — elementary determinant facts for
  endomorphisms of a finite-dimensional inner product space
  (`det T* = conj (det T)`; isometries and coisometries have `‖det‖ = 1`);
  ingredients of the maximal difference theorem in `SNumbers.Inequalities`.
* `BasicResults.Spectral.MultiplicationOperator` — the multiplication operator
  `M_f : L²(μ) →L L²(μ)`, `g ↦ f • g`, for an essentially bounded symbol `f`;
  its norm bound, multiplicativity `M_f ∘ M_g = M_{fg}`, and
  self-adjointness for real symbols. **Phase 0** of the spectral
  representation below.
* `BasicResults.Spectral.Complexification` — the complexification of a real
  inner product space, equipped with its complex inner product
  (`InnerProductSpace ℂ`), together with the canonical real-linear isometric
  embedding. A self-contained piece of infrastructure currently missing from
  Mathlib.
* `BasicResults.SpectralEngine` — **Phase 1** of the spectral projection:
  the continuous functional calculus of `S*S` on a complex Hilbert space,
  packaged as `cfcStarHom S : C(spectrum ℝ (S*S), ℝ) →⋆ₐ[ℝ] (H₁ →L[ℂ] H₁)`.
* `BasicResults.SpectralRepresentation` — the spectral projection of `S*S`
  and the lower-bound subspace `(★)` that extend `SVD.exists_scalar_factorisation`
  (hence `s`-number uniqueness) from compact to **arbitrary bounded**
  operators. The spectral-theory input the compact SVD does not provide;
  currently `sorry` (see the module header for the construction plan).

Each module here is a candidate for upstreaming to Mathlib in its own
right.
-/
