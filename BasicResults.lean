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
that are needed in the s-numbers framework. Currently:

* `BasicResults.Auerbach` — Auerbach's lemma (every finite-dimensional
  normed space over `ℝ` admits an Auerbach basis).
* `BasicResults.SVD` — blueprint declaration for the singular-value
  decomposition of compact operators between Hilbert spaces.

Each module here is a candidate for upstreaming to Mathlib in its own
right.
-/
