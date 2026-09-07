/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
/-!
# Palomar submissions — audited statements

Root module of the `PalomarChallenges` library, which holds the *Challenge* of
every submission to the [Palomar registry](https://palomar-registry.org): one
module per registered result, stating the advertised theorems and importing
nothing beyond Mathlib, so that a reader can audit what is claimed without
reading the development. The metadata of a submission — its `comparator.json`
and `formalization.yaml` — sits in the like-named subdirectory next to it.

The proofs live in the sibling library `PalomarSolutions`.

The `sorry`s in these modules are placeholders required by the submission
format; the mathematical development in `SNumbers/`, `BasicResults/` and
`AddOns/` is `sorry`-free.

## Why Challenge and Solution are separate libraries

A Challenge repeats the definitions its statements rest on, while its Solution
receives the very same definitions through `SNumbers`. The two must therefore
never meet in one environment, and Comparator compiles them separately for
exactly that reason. Beyond that, Lean resolves a module by its **root
component**, and Comparator puts the isolated Challenge directory first on the
search path — so a Solution sharing the root component with its Challenge is
looked for in the Challenge-only directory and not found. Hence the two roots
`PalomarChallenges` and `PalomarSolutions`, and hence this module imports
nothing.

Both libraries are deliberately absent from `defaultTargets`, so a plain
`lake build` behaves exactly as it would without them. Build them with
`lake build PalomarChallenges PalomarSolutions`.

## Registered results

* `PalomarChallenges.MaxDifference` — the maximal difference theorem
  `aₙ(S) ≤ ((n+1)^{n+1}/nⁿ) · hₙ(S) ≤ e · (n+1) · hₙ(S)` between the largest
  and the smallest s-number sequence, advertising
  `SNumbers.approximationNumber_le_mul_hilbertNumber` and
  `SNumbers.approximationNumber_le_e_mul_hilbertNumber`.
-/
