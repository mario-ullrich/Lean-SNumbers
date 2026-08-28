/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
/-!
# Palomar submissions

Root module of the `Palomar` library, which collects the submission surfaces for
the [Palomar registry](https://palomar-registry.org) — one directory per
registered result, each holding a `Challenge` module (the audited statements),
a `Solution` module (the proofs, drawn from the development in `SNumbers/` and
`BasicResults/`), a `comparator.json` and a `formalization.yaml`.

The `sorry`s in the `Challenge` modules are placeholders required by the
submission format: a Challenge advertises statements and imports only Mathlib,
so that a reader can audit what is claimed without reading the development. The
mathematical development itself is `sorry`-free.

A `Challenge` and its `Solution` are **separate roots**, never imported into one
another or into a common module: the Challenge repeats the definitions the
statements rest on, while the Solution receives the very same definitions
through `SNumbers`, so a shared environment would see each of them twice.
Comparator compiles the two against separate environments for exactly this
reason. Hence this module imports nothing, and the library is built from the
glob `Palomar.+`.

This library is deliberately absent from `defaultTargets`, so a plain
`lake build` behaves exactly as it does without it. Build these modules with
`lake build Palomar`.

## Registered results

* `Palomar.MaxDifference` — the maximal difference theorem
  `aₙ(S) ≤ ((n+1)^{n+1}/nⁿ) · hₙ(S) ≤ e · (n+1) · hₙ(S)` between the largest
  and the smallest s-number sequence.
-/
