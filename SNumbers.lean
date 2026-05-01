/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
import SNumbers.Basic
import SNumbers.Helpers
import SNumbers.Approximation
import SNumbers.Bernstein
import SNumbers.Gelfand
import SNumbers.Kolmogorov
import SNumbers.Hilbert
import SNumbers.Inequalities

/-!
# s-Numbers of bounded linear operators between Banach spaces

The Pietsch axiomatic theory of s-numbers, formalised in Lean 4 / Mathlib.

## Main contents

* `SNumbers.Basic`: the `rank` of a continuous linear map and the Pietsch
  axioms (S1)–(S5), packaged as `IsSNumberSequence`. Also the (S5')
  strengthening and the structure `IsStrictSNumberSequence`.
* `SNumbers.Helpers`: small generic facts shared across the development —
  rank lemmas for continuous linear maps and the closing-step ε-limit
  `le_of_mul_one_sub_le_of_nonneg`.
* `SNumbers.Approximation`: the approximation numbers `aₙ`, fully proved
  to form a strict s-number sequence (S1)–(S5)+(S5').
* `SNumbers.Bernstein`, `SNumbers.Gelfand`, `SNumbers.Kolmogorov`,
  `SNumbers.Hilbert`: the further canonical examples — `bₙ`, `cₙ`, `dₙ`,
  `hₙ`. One file per construction. The Kolmogorov numbers are fully proved
  to form a strict s-number sequence; the other three are stated, with
  proofs forthcoming.
* `SNumbers.Inequalities`: comparison results, in particular Pietsch's
  sandwich theorem `hₙ ≤ sₙ ≤ aₙ` for every s-number sequence `s`. The
  upper bound is fully proved; the lower bound and the underlying
  Hilbert-space coincidence theorem are left for a follow-up.

A companion library `BasicResults` (top-level, sibling of this module)
collects generic auxiliary material needed by the framework — Auerbach's
lemma (fully proved) and the compact-operator SVD blueprint.

## References

* A. Pietsch, *s-Numbers of operators in Banach spaces*, Studia Math. 51
  (1974), 201–223.
* A. Pietsch, *Eigenvalues and s-numbers*, Cambridge studies in advanced
  mathematics 13, Cambridge University Press, 1987.
* M. Ullrich, *Inequalities between s-numbers*. <https://doi.org/10.1007/s43036-024-00386-x>
-/
