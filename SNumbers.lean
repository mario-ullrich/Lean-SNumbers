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
import SNumbers.KolmogorovLifting
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
  rank lemmas for continuous linear maps (`rank_zero`,
  `eq_zero_of_rank_le_zero`, `rank_comp_comp_le`) and the
  `ContinuousLinearMap` packaging of the quotient projection /
  universal lift (`Submodule.mkQL`, `Submodule.liftQL`).
* `SNumbers.Approximation`: the approximation numbers `aₙ`, fully proved
  to form a strict s-number sequence (S1)–(S5)+(S5').
* `SNumbers.Bernstein`, `SNumbers.Gelfand`, `SNumbers.Kolmogorov`,
  `SNumbers.Hilbert`: the further canonical examples — `bₙ`, `cₙ`, `dₙ`,
  `hₙ`. One file per construction. The Bernstein, Gelfand, and Kolmogorov
  numbers are fully proved to form strict s-number sequences; the
  remaining `hₙ` is stated, with proofs forthcoming.
* `SNumbers.KolmogorovLifting`: an alternative development of the
  Kolmogorov numbers via Pietsch's identity `d_n S = a_n(S ∘ Q_X)`,
  where `Q_X : ℓ¹(B_X) →L[𝕜] X` is the canonical summation surjection.
  Many axioms become one-liners over `a_n`, but the construction needs
  `[CompleteSpace X]` (an infinite series in `X`) — restricted to
  Banach spaces. Lives in the sub-namespace `SNumbers.Lifting` to
  coexist with `SNumbers.Kolmogorov`.
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
