/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
import BasicResults.Auerbach
import BasicResults.SVD

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

Each module here is a candidate for upstreaming to Mathlib in its own
right.
-/
