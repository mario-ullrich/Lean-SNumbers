/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
import AddOns.Approximable
import AddOns.Compact

/-!
# Add-ons: approximable operators and the compact ↔ approximable theory

Auxiliary Hilbert/Banach-space material around the s-numbers framework,
following Pietsch, *Eigenvalues and s-numbers* (Cambridge, 1987), §2.11.
None of this is on the critical path of the s-numbers development; it is
kept as optional supporting material.

## Layout

* `AddOns.Approximable` — the class of *approximable* operators (those
  whose approximation numbers `aₙ` tend to zero), its closure properties,
  and the implication `IsApproximable ⇒ IsCompactOperator`.
* `AddOns.Compact` — the converse *compact ⇒ approximable* on Hilbert
  spaces and the equivalence `IsApproximable ↔ IsCompactOperator`.

The singular value decomposition itself — including the **scalar
factorisation** `SVD.exists_scalar_factorisation` consumed by the
`s`-numbers uniqueness theorem — lives in `BasicResults.SVD`.
-/
