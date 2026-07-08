/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
import BasicResults.Auerbach
import BasicResults.SVD
import BasicResults.Determinant
import BasicResults.GarlingGordon
import BasicResults.KadetsSnobar
import BasicResults.John
import BasicResults.TriangularFactorisation
import BasicResults.Spectral.MonotoneConvergence
import BasicResults.Spectral.Complexification
import BasicResults.Spectral.Projection
import BasicResults.Spectral.RealProjection
import BasicResults.Spectral.Representation
import BasicResults.Spectral.MultiplicationOperator

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
  (`det T* = conj (det T)` and `‖det T‖ = ∏ₖ σₖ`).
* `BasicResults.GarlingGordon` / `BasicResults.KadetsSnobar` — the
  Garling–Gordon and Kadets–Snobar projection theorems (`‖P‖ ≤ √n`),
  classical Banach-space geometry, stated as `sorry`.
* `BasicResults.John` — towards the sharp `√n` above: John's ellipsoid theorem.
  So far, the maximal-volume inscribed ellipsoid exists (`John.exists_maxVolume`);
  the decomposition of identity from its optimality is in progress.
* `BasicResults.TriangularFactorisation` — the determinant of a triangular flag
  `[gᵢ(S xⱼ)]` realised through `ℓ₂ⁿ⁺¹` with factors of norm `≤ √(n+1)`; the
  linear-algebra engine behind the Gelfand/Kolmogorov product bounds.

## The `BasicResults.Spectral` subpackage

This is the spectral-theory input that extends `s`-number uniqueness from compact to **arbitrary
bounded** operators. It produces, for any `RCLike` field, the spectral projection of `S*S` with its
two operator-norm bounds (`SpectralRepresentation.exists_spectral_projection`), and the lower-bound
subspace `(★)` the uniqueness theorem consumes — all unconditional, with no extra hypotheses. The
pipeline:

* `MonotoneConvergence` — analytic core: strong-operator limits of antitone positive operators.
* `Complexification` — the complexification of a real inner product space (missing from Mathlib),
  the vehicle for the real and `RCLike` cases.
* `Projection` — the spectral projection over `ℂ` (continuous functional calculus of `S*S`), plus
  the commutation lemma `cfc_comm_of_comm`.
* `RealProjection` — the spectral projection over `ℝ`, by complexifying and restricting.
* `Representation` — the capstone: the uniform `RCLike` spectral projection (realify → complexify
  → lift) and the lower-bound subspace `(★)`.
* `MultiplicationOperator` — independent: the multiplication operator `M_f` on `L²`. The seed of an
  alternative (multiplication-form) route to the spectral theorem; **not** used by the current
  development.

Each module here (especially `Complexification`) is a candidate for upstreaming to Mathlib.
-/
