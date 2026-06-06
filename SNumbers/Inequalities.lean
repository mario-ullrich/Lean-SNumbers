/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
import SNumbers.Hilbert
import SNumbers.Uniqueness
import SNumbers.Gelfand
import SNumbers.Kolmogorov
import SNumbers.SingularValuesFinDim
import BasicResults.Determinant
import BasicResults.GarlingGordon
import BasicResults.KadetsSnobar
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Comparison of `s`-number sequences (general spaces)

Pietsch's classical extremality result: among all `s`-number sequences, the
**Hilbert numbers** `hₙ` are the smallest and the **approximation numbers**
`aₙ` are the largest. This file collects the comparison statements that hold
for operators between **arbitrary** `𝕜`-Banach spaces.

## Main results

* `hilbertNumber_le_sn` — lower bound `hₙ(S) ≤ sₙ(S)`.
* `hilbertNumber_le_sn_le_approximationNumber` — the sandwich theorem
  `hₙ(S) ≤ sₙ(S) ≤ aₙ(S)`.
* `approximationNumber_le_sqrt_mul_gelfandNumber` —
  `aₙ(S) ≤ (1 + √n)·cₙ(S)`.
* `approximationNumber_le_sqrt_mul_kolmogorovNumber` —
  `aₙ(S) ≤ (1 + √n)·dₙ(S)`.
* `approximationNumber_le_sqrt_mul_min` — the combined bound
  `aₙ(S) ≤ (1 + √n)·min(cₙ(S), dₙ(S))` (Ullrich, *Inequalities between
  s-numbers*, Prop. on `aₙ` vs `cₙ`, `dₙ`; Pietsch [Pie87, 2.10.2]).
* `max_gelfandNumber_kolmogorovNumber_le_geomMean_hilbertNumber` — the
  **maximal difference theorem**, a reverse-direction bound
  `max(cₙ(S), dₙ(S)) ≤ (n+1)·(∏_{k=0}^n hₖ(S))^{1/(n+1)}`
  (reference: Ullrich, *Inequalities between s-numbers*, arXiv:2405.05509,
  Thm 3).

## The `aₙ` vs `cₙ`, `dₙ` bound and its two projection inputs

The bound `aₙ(S) ≤ (1 + √n)·min(cₙ(S), dₙ(S))` says that the *largest*
`s`-number `aₙ` cannot exceed the Gelfand / Kolmogorov numbers by more
than a factor `1 + √n`. Each half is proved by turning a near-optimal
subspace into a finite-rank approximant `L`, using a bounded projection:

* **Gelfand half** (`aₙ ≤ (1+√n)·cₙ`): pick a closed `M ⊆ X` of
  codimension `≤ n` with `‖S|_M‖` near `cₙ(S)`; the **Garling–Gordon**
  theorem supplies a projection `P` with kernel `M` and `‖P‖ ≤ √n`. Then
  `L := S ∘ P` has rank `≤ n` and `S - L = S ∘ (id − P)` has range
  inside `M`, so `‖S − L‖ ≤ ‖S|_M‖·‖id − P‖ ≤ (1 + √n)·‖S|_M‖`.
* **Kolmogorov half** (`aₙ ≤ (1+√n)·dₙ`): pick `V ⊆ Y` of dimension
  `≤ n` with `‖π_V ∘ S‖` near `dₙ(S)`; the **Kadets–Snobar** theorem
  supplies a projection `P` onto `V` with `‖P‖ ≤ √n`. Then `L := P ∘ S`
  has rank `≤ n` and `S − L = (id − P) ∘ S`, where `id − P` factors
  through the quotient `Y ⧸ V`, so
  `‖S − L‖ ≤ ‖id − P‖·‖π_V ∘ S‖ ≤ (1 + √n)·‖π_V ∘ S‖`.

The two projection theorems are deep results of Banach-space geometry, imported
as `sorry` basic inputs from `BasicResults.GarlingGordon`
(`exists_projection_ker_eq_of_codim_le`) and `BasicResults.KadetsSnobar`
(`exists_projection_range_eq_of_rank_le`); every other lemma in this section is a
full proof built on top of them.

## Proof strategy for `hₙ ≤ sₙ`

Each ratio `aₙ(B ∘ S ∘ A)/(‖B‖‖A‖)` defining `hₙ(S)` has `B ∘ S ∘ A` an
operator **between Hilbert spaces** (`ℓ₂ → ℓ₂`), so the coincidence gives
`aₙ(B ∘ S ∘ A) ≤ sₙ(B ∘ S ∘ A)`; the (S3) ideal property then bounds this by
`‖B‖ · sₙ(S) · ‖A‖`. Dividing by `‖B‖‖A‖` and taking the supremum over the
admissible `(A, B)` yields `hₙ(S) ≤ sₙ(S)`.

## References

* M. Ullrich, *Inequalities between s-numbers*, Advances in Operator
  Theory **9** (2024), no. 4, art. 82.
  <https://doi.org/10.1007/s43036-024-00386-x> (preprint:
  arXiv:2405.05509). The `aₙ ≤ (1+√n)·min(cₙ,dₙ)` bound and the maximal
  difference theorem `max(cₙ,dₙ) ≤ (n+1)·(∏hₖ)^{1/(n+1)}` are from here.
* A. Pietsch, *Eigenvalues and s-numbers*, Cambridge Univ. Press, 1987
  ([Pie87]); the projection theorems are 1.7.17 (Garling–Gordon) and
  1.5.5 (Kadets–Snobar).
-/

universe u

open ContinuousLinearMap

namespace SNumbers

variable {𝕜 : Type u} [RCLike 𝕜]
variable {X Y : Type u}
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]

/-- **Lower bound.** The Hilbert numbers are the smallest `s`-number
sequence: `hₙ(S) ≤ sₙ(S)` for every `s`-number sequence `s`. -/
theorem hilbertNumber_le_sn {s : Family 𝕜} (hs : IsSNumberSequence s)
    (S : X →L[𝕜] Y) (n : ℕ) :
    hilbertNumber S n ≤ s S n := by
  rw [hilbertNumber_def]
  refine Real.sSup_le ?_ (hs.nonneg S n)
  rintro r ⟨A, B, hA, hB, rfl⟩
  have hpos : 0 < ‖B‖ * ‖A‖ := mul_pos (norm_pos_iff.mpr hB) (norm_pos_iff.mpr hA)
  rw [div_le_iff₀ hpos]
  -- `B ∘ S ∘ A : ℓ₂ → ℓ₂` is between Hilbert spaces, so `aₙ = sₙ` on it.
  calc approximationNumber (B.comp (S.comp A)) n
      ≤ s (B.comp (S.comp A)) n := approximationNumber_le_sn hs (B.comp (S.comp A)) n
    _ ≤ ‖B‖ * s S n * ‖A‖ := hs.ideal A S B n
    _ = s S n * (‖B‖ * ‖A‖) := by ring

/-- **Sandwich theorem.** For every `s`-number sequence `s` and
every bounded operator `S : X → Y`: `hₙ(S) ≤ sₙ(S) ≤ aₙ(S)`. -/
theorem hilbertNumber_le_sn_le_approximationNumber {s : Family 𝕜}
    (hs : IsSNumberSequence s) (S : X →L[𝕜] Y) (n : ℕ) :
    hilbertNumber S n ≤ s S n ∧ s S n ≤ approximationNumber S n :=
  ⟨hilbertNumber_le_sn hs S n, sn_le_approximationNumber hs S n⟩

/-! ## Comparison of `aₙ` with the Gelfand and Kolmogorov numbers

We now formalise the bound

  `aₙ(S) ≤ (1 + √n)·min(cₙ(S), dₙ(S))`

between the approximation numbers and the Gelfand / Kolmogorov numbers.
See the module docstring for the overall strategy. We work over an
`RCLike` field with `S : X →L[𝕜] Y` between Banach spaces.
-/

variable [CompleteSpace X] [CompleteSpace Y]

/-! ### Two norm lemmas about compositions through a subspace / quotient -/

omit [CompleteSpace X] [CompleteSpace Y] in
/-- If an operator `R : X →L[𝕜] X` has its whole range inside `M`, then
post-composing with `S` is controlled by the restricted norm `‖S|_M‖`:
`‖S ∘ R‖ ≤ ‖S|_M‖·‖R‖`. This is the elementary estimate behind the
Gelfand half. (`deviationFromRestriction S M = ‖S|_M‖`.) -/
lemma norm_comp_le_deviationFromRestriction_mul {S : X →L[𝕜] Y}
    {M : Submodule 𝕜 X} {R : X →L[𝕜] X} (hR : ∀ x, R x ∈ M) :
    ‖S.comp R‖ ≤ deviationFromRestriction S M * ‖R‖ := by
  refine opNorm_le_bound _
    (mul_nonneg (deviationFromRestriction_nonneg S M) (norm_nonneg R)) fun x => ?_
  -- Evaluate `S (R x)` through the inclusion `M ↪ X`: it equals
  -- `(S ∘ ι_M) ⟨R x, hR x⟩`, whose norm is `≤ ‖S|_M‖ · ‖R x‖`.
  have h_eq : (S.comp R) x = (S.comp M.subtypeL) ⟨R x, hR x⟩ := rfl
  rw [h_eq]
  calc ‖(S.comp M.subtypeL) ⟨R x, hR x⟩‖
      ≤ ‖S.comp M.subtypeL‖ * ‖(⟨R x, hR x⟩ : M)‖ := (S.comp M.subtypeL).le_opNorm _
    _ = deviationFromRestriction S M * ‖R x‖ := rfl
    _ ≤ deviationFromRestriction S M * (‖R‖ * ‖x‖) :=
        mul_le_mul_of_nonneg_left (R.le_opNorm x) (deviationFromRestriction_nonneg S M)
    _ = deviationFromRestriction S M * ‖R‖ * ‖x‖ := by ring

omit [CompleteSpace X] [CompleteSpace Y] in
/-- If an operator `R : Y →L[𝕜] Y` vanishes on `V` (i.e. `V ≤ ker R`),
then pre-composing with `S` is controlled by the quotient norm
`‖π_V ∘ S‖`: `‖R ∘ S‖ ≤ ‖R‖·‖π_V ∘ S‖`. This is the elementary estimate
behind the Kolmogorov half: `R` factors through `Y ⧸ V` via the universal
lift `V.liftQL`. (`deviationFromSubspace S V = ‖π_V ∘ S‖`.) -/
lemma norm_comp_le_norm_mul_deviationFromSubspace {S : X →L[𝕜] Y}
    {V : Submodule 𝕜 Y} {R : Y →L[𝕜] Y}
    (hR : V ≤ LinearMap.ker (R : Y →ₗ[𝕜] Y)) :
    ‖R.comp S‖ ≤ ‖R‖ * deviationFromSubspace S V := by
  -- `R = (V.liftQL R hR) ∘ π_V`, so `R ∘ S = (V.liftQL R hR) ∘ (π_V ∘ S)`.
  have hfac : R.comp S = (V.liftQL R hR).comp (V.mkQL.comp S) := by
    ext x
    show R (S x) = V.liftQL R hR (V.mkQL (S x))
    rw [Submodule.liftQL_mkQL]
  rw [hfac]
  calc ‖(V.liftQL R hR).comp (V.mkQL.comp S)‖
      ≤ ‖V.liftQL R hR‖ * ‖V.mkQL.comp S‖ := opNorm_comp_le _ _
    _ ≤ ‖R‖ * ‖V.mkQL.comp S‖ :=
        mul_le_mul_of_nonneg_right (V.norm_liftQL_le R hR) (norm_nonneg _)
    _ = ‖R‖ * deviationFromSubspace S V := rfl

/-! ### Per-subspace bounds -/

omit [CompleteSpace Y] in
/-- **Gelfand half, per subspace.** For a closed `M ⊆ X` of codimension
`≤ n`, `aₙ(S) ≤ (1 + √n)·‖S|_M‖`. The approximant is `L := S ∘ P` for the
Garling–Gordon projection `P` with kernel `M`. -/
lemma approximationNumber_le_sqrt_mul_deviationFromRestriction
    (S : X →L[𝕜] Y) {n : ℕ} {M : Submodule 𝕜 X}
    (hM_closed : IsClosed (M : Set X))
    (hM_codim : Module.rank 𝕜 (X ⧸ M) ≤ (n : Cardinal)) :
    approximationNumber S n ≤ (1 + Real.sqrt n) * deviationFromRestriction S M := by
  obtain ⟨P, hP_idem, hP_ker, hP_norm⟩ :=
    exists_projection_ker_eq_of_codim_le hM_closed hM_codim
  -- `rank P = codim (ker P) = codim M ≤ n`.
  have hPrank : P.rank ≤ (n : Cardinal) := by
    have e : Module.rank 𝕜 (X ⧸ LinearMap.ker (P : X →ₗ[𝕜] X))
              = Module.rank 𝕜 (LinearMap.range (P : X →ₗ[𝕜] X)) :=
      (LinearMap.quotKerEquivRange (P : X →ₗ[𝕜] X)).rank_eq
    rw [hP_ker] at e
    calc P.rank = Module.rank 𝕜 (LinearMap.range (P : X →ₗ[𝕜] X)) := rfl
      _ = Module.rank 𝕜 (X ⧸ M) := e.symm
      _ ≤ (n : Cardinal) := hM_codim
  -- `L := S ∘ P` is an admissible rank-≤ n approximant.
  have hL_rank : (S.comp P).rank ≤ (n : Cardinal) := by
    have h := ContinuousLinearMap.rank_comp_comp_le (ContinuousLinearMap.id 𝕜 X) P S
    rw [ContinuousLinearMap.comp_id] at h
    exact h.trans hPrank
  -- `id − P` lands in `M` (its range is `ker P = M`).
  have hR : ∀ x, (ContinuousLinearMap.id 𝕜 X - P) x ∈ M := by
    intro x
    have hPP : P (P x) = P x := by
      have h : (P.comp P) x = P x := by rw [hP_idem]
      exact h
    have hkey : P ((ContinuousLinearMap.id 𝕜 X - P) x) = 0 := by
      rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply, map_sub,
        hPP, sub_self]
    rw [← hP_ker, LinearMap.mem_ker]
    exact hkey
  -- `‖id − P‖ ≤ 1 + √n`.
  have h4 : ‖(ContinuousLinearMap.id 𝕜 X - P : X →L[𝕜] X)‖ ≤ 1 + Real.sqrt n :=
    (norm_sub_le _ _).trans (add_le_add ContinuousLinearMap.norm_id_le hP_norm)
  calc approximationNumber S n
      ≤ ‖S - S.comp P‖ := approximationNumber_le_norm_sub hL_rank
    _ = ‖S.comp (ContinuousLinearMap.id 𝕜 X - P)‖ := by
        rw [ContinuousLinearMap.comp_sub, ContinuousLinearMap.comp_id]
    _ ≤ deviationFromRestriction S M *
          ‖(ContinuousLinearMap.id 𝕜 X - P : X →L[𝕜] X)‖ :=
        norm_comp_le_deviationFromRestriction_mul hR
    _ ≤ deviationFromRestriction S M * (1 + Real.sqrt n) :=
        mul_le_mul_of_nonneg_left h4 (deviationFromRestriction_nonneg S M)
    _ = (1 + Real.sqrt n) * deviationFromRestriction S M := by ring

omit [CompleteSpace X] in
/-- **Kolmogorov half, per subspace.** For `V ⊆ Y` of dimension `≤ n`,
`aₙ(S) ≤ (1 + √n)·‖π_V ∘ S‖`. The approximant is `L := P ∘ S` for the
Kadets–Snobar projection `P` onto `V`. -/
lemma approximationNumber_le_sqrt_mul_deviationFromSubspace
    (S : X →L[𝕜] Y) {n : ℕ} {V : Submodule 𝕜 Y}
    (hV_rank : Module.rank 𝕜 V ≤ (n : Cardinal)) :
    approximationNumber S n ≤ (1 + Real.sqrt n) * deviationFromSubspace S V := by
  obtain ⟨P, hP_idem, hP_range, hP_norm⟩ :=
    exists_projection_range_eq_of_rank_le hV_rank
  -- `rank P = dim (range P) = dim V ≤ n`.
  have hPrank : P.rank ≤ (n : Cardinal) := by
    calc P.rank = Module.rank 𝕜 (LinearMap.range (P : Y →ₗ[𝕜] Y)) := rfl
      _ = Module.rank 𝕜 V := by rw [hP_range]
      _ ≤ (n : Cardinal) := hV_rank
  -- `L := P ∘ S` is an admissible rank-≤ n approximant.
  have hL_rank : (P.comp S).rank ≤ (n : Cardinal) := by
    have h := ContinuousLinearMap.rank_comp_comp_le S P (ContinuousLinearMap.id 𝕜 Y)
    rw [ContinuousLinearMap.id_comp] at h
    exact h.trans hPrank
  -- `id − P` vanishes on `V` (since `P` fixes its range `V`).
  have hVker : V ≤ LinearMap.ker
      ((ContinuousLinearMap.id 𝕜 Y - P : Y →L[𝕜] Y) : Y →ₗ[𝕜] Y) := by
    intro v hv
    have hPv : P v = v := by
      rw [← hP_range] at hv
      obtain ⟨w, hw⟩ := hv
      have hPP : P (P w) = P w := by
        have h : (P.comp P) w = P w := by rw [hP_idem]
        exact h
      rw [← hw]; exact hPP
    rw [LinearMap.mem_ker]
    show (ContinuousLinearMap.id 𝕜 Y - P) v = 0
    rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply, hPv, sub_self]
  -- `‖id − P‖ ≤ 1 + √n`.
  have h4 : ‖(ContinuousLinearMap.id 𝕜 Y - P : Y →L[𝕜] Y)‖ ≤ 1 + Real.sqrt n :=
    (norm_sub_le _ _).trans (add_le_add ContinuousLinearMap.norm_id_le hP_norm)
  calc approximationNumber S n
      ≤ ‖S - P.comp S‖ := approximationNumber_le_norm_sub hL_rank
    _ = ‖(ContinuousLinearMap.id 𝕜 Y - P).comp S‖ := by
        rw [ContinuousLinearMap.sub_comp, ContinuousLinearMap.id_comp]
    _ ≤ ‖(ContinuousLinearMap.id 𝕜 Y - P : Y →L[𝕜] Y)‖ * deviationFromSubspace S V :=
        norm_comp_le_norm_mul_deviationFromSubspace hVker
    _ ≤ (1 + Real.sqrt n) * deviationFromSubspace S V :=
        mul_le_mul_of_nonneg_right h4 (deviationFromSubspace_nonneg S V)

/-! ### The infimum bounds and the combined result -/

omit [CompleteSpace Y] in
/-- **Gelfand bound.** `aₙ(S) ≤ (1 + √n)·cₙ(S)` (Pietsch [Pie87, 2.10.2]).
The per-subspace bound is uniform over the closed codimension-`≤ n`
subspaces, so it passes to the infimum defining `cₙ`. -/
theorem approximationNumber_le_sqrt_mul_gelfandNumber
    (S : X →L[𝕜] Y) (n : ℕ) :
    approximationNumber S n ≤ (1 + Real.sqrt n) * gelfandNumber S n := by
  have hc_pos : (0 : ℝ) < 1 + Real.sqrt n := by positivity
  rw [← div_le_iff₀' hc_pos, gelfandNumber]
  refine le_csInf ⟨_, ⊤, by rw [Submodule.top_coe]; exact isClosed_univ,
    by rw [rank_zero_iff.mpr inferInstance]; exact bot_le, rfl⟩ ?_
  rintro r ⟨M, hM_closed, hM_codim, rfl⟩
  rw [div_le_iff₀' hc_pos]
  exact approximationNumber_le_sqrt_mul_deviationFromRestriction S hM_closed hM_codim

omit [CompleteSpace X] in
/-- **Kolmogorov bound.** `aₙ(S) ≤ (1 + √n)·dₙ(S)` (Pietsch
[Pie87, 2.10.2]). The per-subspace bound is uniform over the
dimension-`≤ n` subspaces, so it passes to the infimum defining `dₙ`. -/
theorem approximationNumber_le_sqrt_mul_kolmogorovNumber
    (S : X →L[𝕜] Y) (n : ℕ) :
    approximationNumber S n ≤ (1 + Real.sqrt n) * kolmogorovNumber S n := by
  have hc_pos : (0 : ℝ) < 1 + Real.sqrt n := by positivity
  rw [← div_le_iff₀' hc_pos, kolmogorovNumber]
  refine le_csInf ⟨_, ⊥, by rw [rank_bot]; exact bot_le, rfl⟩ ?_
  rintro r ⟨V, hV_rank, rfl⟩
  rw [div_le_iff₀' hc_pos]
  exact approximationNumber_le_sqrt_mul_deviationFromSubspace S hV_rank

/-- **Approximation vs. Gelfand and Kolmogorov numbers.** The combined
bound `aₙ(S) ≤ (1 + √n)·min(cₙ(S), dₙ(S))`: the largest `s`-number `aₙ`
exceeds neither `cₙ` nor `dₙ` by more than the factor `1 + √n`. -/
theorem approximationNumber_le_sqrt_mul_min (S : X →L[𝕜] Y) (n : ℕ) :
    approximationNumber S n ≤
      (1 + Real.sqrt n) * min (gelfandNumber S n) (kolmogorovNumber S n) := by
  rcases le_total (gelfandNumber S n) (kolmogorovNumber S n) with h | h
  · rw [min_eq_left h]
    exact approximationNumber_le_sqrt_mul_gelfandNumber S n
  · rw [min_eq_right h]
    exact approximationNumber_le_sqrt_mul_kolmogorovNumber S n

/-! ## Bounding the largest `s`-numbers by the Hilbert numbers

The next result goes the other way round: the *largest* `s`-numbers `cₙ`
and `dₙ` are bounded by the geometric mean of the *smallest* `s`-numbers
`h₀, …, hₙ`:

  `max(cₙ(S), dₙ(S)) ≤ (n+1)·(∏_{k=0}^n hₖ(S))^{1/(n+1)}`.

This is the **maximal difference theorem** (reference: Ullrich,
*Inequalities between s-numbers*, arXiv:2405.05509, Thm 3), restated under
our `0`-based index convention (the paper's `n·(∏_{k=1}^n hₖ)^{1/n}`
becomes `(n+1)·(∏_{k=0}^n hₖ)^{1/(n+1)}`).

### Proof skeleton

The heart of the proof is a **product (determinant) bound**

  `∏_{k=0}^n cₖ(S) ≤ (n+1)^{n+1}·∏_{k=0}^n hₖ(S)`              (★)

and its Kolmogorov analogue, `prod_gelfandNumber_le` / `prod_kolmogorovNumber_le`.
These rest on the inductive triangular determinant construction of the paper, isolated as
`exists_gelfandNumber_det_factorisation` / `exists_kolmogorovNumber_det_factorisation`
(a `sorry`): one assembles `A : ℓ₂ⁿ⁺¹ → X` and `B : Y → ℓ₂ⁿ⁺¹` with
`‖A‖, ‖B‖ ≤ √(n+1)` and `BSA` triangular with `∏ cₖ(S) ≤ ‖det(BSA)‖`. The
determinant is read on Hilbert spaces as
`‖det(BSA)‖ = ∏ aₖ(BSA) ≤ ∏ ‖B‖‖A‖·hₖ(S) ≤ (n+1)^{n+1}∏hₖ(S)`
(`prod_approximationNumber_eq_norm_det`).

Everything else is elementary and fully proved here:

* `self_pow_le_prod`: since `cₖ` is non-increasing, `cₙ` is the smallest of
  `c₀, …, cₙ`, so `cₙ^{n+1} ≤ ∏_{k=0}^n cₖ`;
* `rpow_combine`: from `a^{n+1} ≤ (n+1)^{n+1}·P` (with `a, P ≥ 0`) the
  `(n+1)`-th root gives `a ≤ (n+1)·P^{1/(n+1)}`.

Chaining `cₙ^{n+1} ≤ ∏cₖ ≤ (n+1)^{n+1}∏hₖ` and taking roots yields
`cₙ ≤ (n+1)·(∏hₖ)^{1/(n+1)}`, and likewise for `dₙ`. -/

/-- Elementary: if `f : ℕ → ℝ` is non-negative and non-increasing, its
`n`-th value to the power `n+1` is at most the product of its first `n+1`
values (because `f n` is the smallest of `f 0, …, f n`). -/
private lemma self_pow_le_prod {f : ℕ → ℝ} (hf0 : ∀ k, 0 ≤ f k)
    (hanti : _root_.Antitone f) (n : ℕ) :
    f n ^ (n + 1) ≤ ∏ k ∈ Finset.range (n + 1), f k := by
  calc f n ^ (n + 1)
      = ∏ _k ∈ Finset.range (n + 1), f n := by
        rw [Finset.prod_const, Finset.card_range]
    _ ≤ ∏ k ∈ Finset.range (n + 1), f k :=
        Finset.prod_le_prod (fun _ _ => hf0 n)
          (fun k hk => hanti (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)))

/-- Elementary `(n+1)`-th root step: from `a^{n+1} ≤ (n+1)^{n+1}·P` with
`a, P ≥ 0`, conclude `a ≤ (n+1)·P^{1/(n+1)}`. -/
private lemma rpow_combine {n : ℕ} {a P : ℝ} (ha : 0 ≤ a) (hP : 0 ≤ P)
    (h : a ^ (n + 1) ≤ ((n : ℝ) + 1) ^ (n + 1) * P) :
    a ≤ ((n : ℝ) + 1) * P ^ (1 / ((n : ℝ) + 1)) := by
  have hm : ((n : ℝ) + 1) = ((n + 1 : ℕ) : ℝ) := by push_cast; ring
  rw [hm] at h ⊢
  rw [one_div]
  have key : (a ^ (n + 1)) ^ (((n + 1 : ℕ) : ℝ))⁻¹
      ≤ (((n + 1 : ℕ) : ℝ) ^ (n + 1) * P) ^ (((n + 1 : ℕ) : ℝ))⁻¹ :=
    Real.rpow_le_rpow (pow_nonneg ha (n + 1)) h (by positivity)
  rwa [Real.pow_rpow_inv_natCast ha (Nat.succ_ne_zero n),
    Real.mul_rpow (by positivity) hP,
    Real.pow_rpow_inv_natCast (by positivity) (Nat.succ_ne_zero n)] at key

omit [CompleteSpace X] [CompleteSpace Y] in
/-- **Ingredient (1) of the determinant bound.** The (S3)-type bound for the
Hilbert numbers: `aₙ(B ∘ S ∘ A) ≤ ‖B‖·‖A‖·hₙ(S)` for `A : ℓ₂ → X`,
`B : Y → ℓ₂`. Immediate from the definition of `hₙ` as a supremum of
ratios `aₙ(BSA)/(‖B‖‖A‖)` (`ratio_le_hilbertNumber`); the zero cases are
handled separately since then `B ∘ S ∘ A = 0`. -/
lemma approximationNumber_comp_comp_le_mul_hilbertNumber
    (S : X →L[𝕜] Y) (A : L2 𝕜 →L[𝕜] X) (B : Y →L[𝕜] L2 𝕜) (n : ℕ) :
    approximationNumber (B.comp (S.comp A)) n ≤ ‖B‖ * ‖A‖ * hilbertNumber S n := by
  rcases eq_or_ne A 0 with rfl | hA
  · rw [ContinuousLinearMap.comp_zero, ContinuousLinearMap.comp_zero, norm_zero,
      mul_zero, zero_mul]
    simpa using approximationNumber_le_norm (0 : L2 𝕜 →L[𝕜] L2 𝕜) n
  rcases eq_or_ne B 0 with rfl | hB
  · rw [ContinuousLinearMap.zero_comp, norm_zero, zero_mul, zero_mul]
    simpa using approximationNumber_le_norm (0 : L2 𝕜 →L[𝕜] L2 𝕜) n
  · have hpos : 0 < ‖B‖ * ‖A‖ := mul_pos (norm_pos_iff.mpr hB) (norm_pos_iff.mpr hA)
    have h := ratio_le_hilbertNumber S n hA hB
    rw [div_le_iff₀ hpos] at h
    exact h.trans_eq (by ring)

/-- **`∏ aₖ(T) = ‖det T‖`** for an endomorphism of a finite-dimensional Hilbert
space. The approximation numbers are Mathlib's singular values
(`sn_eq_singularValues_of_finiteDimensional`), and `‖det T‖ = ∏ σₖ`
(`LinearMap.norm_det_eq_prod_singularValues`). This is the determinant
ingredient of the maximal difference theorem. -/
theorem prod_approximationNumber_eq_norm_det {E : Type u} [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E] [Nontrivial E] (T : E →L[𝕜] E) :
    ∏ k ∈ Finset.range (Module.finrank 𝕜 E), approximationNumber T k
      = ‖LinearMap.det (T : E →ₗ[𝕜] E)‖ := by
  rw [LinearMap.norm_det_eq_prod_singularValues]
  exact Finset.prod_congr rfl fun k _ =>
    sn_eq_singularValues_of_finiteDimensional isSNumberSequence_approximationNumber T k

omit [CompleteSpace X] [CompleteSpace Y] in
/-- **Ingredient (1), finite-dimensional form.** For finite factors
`A' : ℓ₂ⁿ⁺¹ → X`, `B' : Y → ℓ₂ⁿ⁺¹`, still `aₖ(B'∘S∘A') ≤ ‖B'‖·‖A'‖·hₖ(S)`.
Compose with the isometric section `ℓ₂ⁿ⁺¹ ↪ ℓ₂` (`exists_l2_section`, both
maps norm `≤ 1`) and apply the `ℓ₂`-form together with the (S3) ideal
property to drop the section maps. -/
lemma approximationNumber_eucl_comp_comp_le_mul_hilbertNumber (S : X →L[𝕜] Y) (n k : ℕ)
    (A' : EuclideanSpace 𝕜 (Fin (n + 1)) →L[𝕜] X)
    (B' : Y →L[𝕜] EuclideanSpace 𝕜 (Fin (n + 1))) :
    approximationNumber (B'.comp (S.comp A')) k ≤ ‖B'‖ * ‖A'‖ * hilbertNumber S k := by
  obtain ⟨jm, pm, hpj, hp1, hj1⟩ := exists_l2_section (𝕜 := 𝕜) n
  have hpj_apply : ∀ z, pm (jm z) = z := fun z => by
    rw [← ContinuousLinearMap.comp_apply, hpj, ContinuousLinearMap.id_apply]
  set AL : L2 𝕜 →L[𝕜] X := A'.comp pm with hAL
  set BL : Y →L[𝕜] L2 𝕜 := jm.comp B' with hBL
  have hMeq : B'.comp (S.comp A') = pm.comp ((BL.comp (S.comp AL)).comp jm) := by
    ext x
    simp only [hAL, hBL, ContinuousLinearMap.comp_apply]
    rw [hpj_apply x, hpj_apply (B' (S (A' x)))]
  have hak : 0 ≤ approximationNumber (BL.comp (S.comp AL)) k := approximationNumber_nonneg _ _
  calc approximationNumber (B'.comp (S.comp A')) k
      = approximationNumber (pm.comp ((BL.comp (S.comp AL)).comp jm)) k := by rw [hMeq]
    _ ≤ ‖pm‖ * approximationNumber (BL.comp (S.comp AL)) k * ‖jm‖ :=
        approximationNumber_comp_comp_le jm (BL.comp (S.comp AL)) pm k
    _ ≤ 1 * approximationNumber (BL.comp (S.comp AL)) k * 1 :=
        mul_le_mul (mul_le_mul hp1 le_rfl hak zero_le_one) hj1 (norm_nonneg _)
          (mul_nonneg zero_le_one hak)
    _ = approximationNumber (BL.comp (S.comp AL)) k := by ring
    _ ≤ ‖BL‖ * ‖AL‖ * hilbertNumber S k :=
        approximationNumber_comp_comp_le_mul_hilbertNumber S AL BL k
    _ ≤ ‖B'‖ * ‖A'‖ * hilbertNumber S k := by
        have hBLn : ‖BL‖ ≤ ‖B'‖ :=
          (ContinuousLinearMap.opNorm_comp_le jm B').trans
            (mul_le_of_le_one_left (norm_nonneg _) hj1)
        have hALn : ‖AL‖ ≤ ‖A'‖ :=
          (ContinuousLinearMap.opNorm_comp_le A' pm).trans
            (mul_le_of_le_one_right (norm_nonneg _) hp1)
        exact mul_le_mul (mul_le_mul hBLn hALn (norm_nonneg _) (norm_nonneg _)) le_rfl
          (hilbertNumber_nonneg S k) (mul_nonneg (norm_nonneg _) (norm_nonneg _))

omit [CompleteSpace X] [CompleteSpace Y] in
/-- **Determinant product bound from a factorisation.** Given finite factors
`A', B'` of norm `≤ √(n+1)` with `∏ Pₖ ≤ ‖det(B'∘S∘A')‖`, the new identity
`∏ aₖ(T) = ‖det T‖` (`prod_approximationNumber_eq_norm_det`) and ingredient (1)
give `∏ Pₖ ≤ ∏ aₖ(B'∘S∘A') ≤ ∏ ‖B'‖‖A'‖ hₖ ≤ (n+1)^{n+1} ∏ hₖ`. This isolates
the determinant accounting; only the existence of the factors (`P = cₖ` or
`dₖ`) remains. -/
lemma prod_le_pow_mul_prod_hilbertNumber_of_factorisation (S : X →L[𝕜] Y) (n : ℕ) {P : ℕ → ℝ}
    (A' : EuclideanSpace 𝕜 (Fin (n + 1)) →L[𝕜] X)
    (B' : Y →L[𝕜] EuclideanSpace 𝕜 (Fin (n + 1)))
    (hA : ‖A'‖ ≤ Real.sqrt ((n : ℝ) + 1)) (hB : ‖B'‖ ≤ Real.sqrt ((n : ℝ) + 1))
    (hdet : ∏ k ∈ Finset.range (n + 1), P k
      ≤ ‖LinearMap.det (B'.comp (S.comp A') :
          EuclideanSpace 𝕜 (Fin (n + 1)) →ₗ[𝕜] EuclideanSpace 𝕜 (Fin (n + 1)))‖) :
    ∏ k ∈ Finset.range (n + 1), P k
      ≤ ((n : ℝ) + 1) ^ (n + 1) * ∏ k ∈ Finset.range (n + 1), hilbertNumber S k := by
  haveI : Nontrivial (EuclideanSpace 𝕜 (Fin (n + 1))) :=
    Module.nontrivial_of_finrank_pos (by rw [finrank_euclideanSpace_fin]; omega)
  have hBA : ‖B'‖ * ‖A'‖ ≤ (n : ℝ) + 1 :=
    (mul_le_mul hB hA (norm_nonneg _) (Real.sqrt_nonneg _)).trans_eq
      (Real.mul_self_sqrt (by positivity))
  calc ∏ k ∈ Finset.range (n + 1), P k
      ≤ ‖LinearMap.det (B'.comp (S.comp A') :
          EuclideanSpace 𝕜 (Fin (n + 1)) →ₗ[𝕜] EuclideanSpace 𝕜 (Fin (n + 1)))‖ := hdet
    _ = ∏ k ∈ Finset.range (n + 1), approximationNumber (B'.comp (S.comp A')) k := by
        rw [← prod_approximationNumber_eq_norm_det (B'.comp (S.comp A')), finrank_euclideanSpace_fin]
    _ ≤ ∏ k ∈ Finset.range (n + 1), (‖B'‖ * ‖A'‖ * hilbertNumber S k) :=
        Finset.prod_le_prod (fun k _ => approximationNumber_nonneg _ _)
          (fun k _ => approximationNumber_eucl_comp_comp_le_mul_hilbertNumber S n k A' B')
    _ = (‖B'‖ * ‖A'‖) ^ (n + 1) * ∏ k ∈ Finset.range (n + 1), hilbertNumber S k := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]
    _ ≤ ((n : ℝ) + 1) ^ (n + 1) * ∏ k ∈ Finset.range (n + 1), hilbertNumber S k :=
        mul_le_mul_of_nonneg_right
          (pow_le_pow_left₀ (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hBA (n + 1))
          (Finset.prod_nonneg fun k _ => hilbertNumber_nonneg S k)

omit [CompleteSpace X] [CompleteSpace Y] in
/-- **Triangular determinant factorisation, Gelfand side** — a geometric `sorry`.
For `c < cₙ(S)`-type extremal subspaces one builds `A' : ℓ₂ⁿ⁺¹ → X`,
`B' : Y → ℓ₂ⁿ⁺¹` with `‖A'‖, ‖B'‖ ≤ √(n+1)` and `B'∘S∘A'` upper-triangular with
`∏ cₖ(S) ≤ ‖det(B'∘S∘A')‖`. This is the only input the Gelfand product bound
rests on. -/
theorem exists_gelfandNumber_det_factorisation (S : X →L[𝕜] Y) (n : ℕ) :
    ∃ (A' : EuclideanSpace 𝕜 (Fin (n + 1)) →L[𝕜] X)
      (B' : Y →L[𝕜] EuclideanSpace 𝕜 (Fin (n + 1))),
      ‖A'‖ ≤ Real.sqrt ((n : ℝ) + 1) ∧ ‖B'‖ ≤ Real.sqrt ((n : ℝ) + 1) ∧
      ∏ k ∈ Finset.range (n + 1), gelfandNumber S k
        ≤ ‖LinearMap.det (B'.comp (S.comp A') :
            EuclideanSpace 𝕜 (Fin (n + 1)) →ₗ[𝕜] EuclideanSpace 𝕜 (Fin (n + 1)))‖ := by
  sorry

omit [CompleteSpace X] [CompleteSpace Y] in
/-- **Product (determinant) bound, Gelfand side.** `∏ cₖ ≤ (n+1)^{n+1} ∏ hₖ`,
reduced (via `prod_le_pow_mul_prod_hilbertNumber_of_factorisation` and the
determinant identity) to the triangular factorisation
`exists_gelfandNumber_det_factorisation`. -/
theorem prod_gelfandNumber_le (S : X →L[𝕜] Y) (n : ℕ) :
    ∏ k ∈ Finset.range (n + 1), gelfandNumber S k
      ≤ ((n : ℝ) + 1) ^ (n + 1) * ∏ k ∈ Finset.range (n + 1), hilbertNumber S k := by
  obtain ⟨A', B', hA, hB, hdet⟩ := exists_gelfandNumber_det_factorisation S n
  exact prod_le_pow_mul_prod_hilbertNumber_of_factorisation S n A' B' hA hB hdet

omit [CompleteSpace X] [CompleteSpace Y] in
/-- **Triangular determinant factorisation, Kolmogorov side** — a geometric `sorry`,
dual to `exists_gelfandNumber_det_factorisation`. -/
theorem exists_kolmogorovNumber_det_factorisation (S : X →L[𝕜] Y) (n : ℕ) :
    ∃ (A' : EuclideanSpace 𝕜 (Fin (n + 1)) →L[𝕜] X)
      (B' : Y →L[𝕜] EuclideanSpace 𝕜 (Fin (n + 1))),
      ‖A'‖ ≤ Real.sqrt ((n : ℝ) + 1) ∧ ‖B'‖ ≤ Real.sqrt ((n : ℝ) + 1) ∧
      ∏ k ∈ Finset.range (n + 1), kolmogorovNumber S k
        ≤ ‖LinearMap.det (B'.comp (S.comp A') :
            EuclideanSpace 𝕜 (Fin (n + 1)) →ₗ[𝕜] EuclideanSpace 𝕜 (Fin (n + 1)))‖ := by
  sorry

omit [CompleteSpace X] [CompleteSpace Y] in
/-- **Product (determinant) bound, Kolmogorov side.** `∏ dₖ ≤ (n+1)^{n+1} ∏ hₖ`,
reduced to `exists_kolmogorovNumber_det_factorisation` as on the Gelfand side. -/
theorem prod_kolmogorovNumber_le (S : X →L[𝕜] Y) (n : ℕ) :
    ∏ k ∈ Finset.range (n + 1), kolmogorovNumber S k
      ≤ ((n : ℝ) + 1) ^ (n + 1) * ∏ k ∈ Finset.range (n + 1), hilbertNumber S k := by
  obtain ⟨A', B', hA, hB, hdet⟩ := exists_kolmogorovNumber_det_factorisation S n
  exact prod_le_pow_mul_prod_hilbertNumber_of_factorisation S n A' B' hA hB hdet

omit [CompleteSpace X] [CompleteSpace Y] in
/-- **Gelfand vs. Hilbert numbers.** `cₙ(S) ≤ (n+1)·(∏_{k=0}^n hₖ(S))^{1/(n+1)}`,
the Gelfand half of the maximal difference theorem. -/
theorem gelfandNumber_le_geomMean_hilbertNumber (S : X →L[𝕜] Y) (n : ℕ) :
    gelfandNumber S n ≤
      ((n : ℝ) + 1) *
        (∏ k ∈ Finset.range (n + 1), hilbertNumber S k) ^ (1 / ((n : ℝ) + 1)) := by
  have hpow : gelfandNumber S n ^ (n + 1)
      ≤ ∏ k ∈ Finset.range (n + 1), gelfandNumber S k :=
    self_pow_le_prod (gelfandNumber_nonneg S)
      (antitone_nat_of_succ_le (gelfandNumber_antitone S)) n
  exact rpow_combine (gelfandNumber_nonneg S n)
    (Finset.prod_nonneg fun k _ => hilbertNumber_nonneg S k)
    (hpow.trans (prod_gelfandNumber_le S n))

omit [CompleteSpace X] [CompleteSpace Y] in
/-- **Kolmogorov vs. Hilbert numbers.** `dₙ(S) ≤ (n+1)·(∏_{k=0}^n hₖ(S))^{1/(n+1)}`,
the Kolmogorov half of the maximal difference theorem. -/
theorem kolmogorovNumber_le_geomMean_hilbertNumber (S : X →L[𝕜] Y) (n : ℕ) :
    kolmogorovNumber S n ≤
      ((n : ℝ) + 1) *
        (∏ k ∈ Finset.range (n + 1), hilbertNumber S k) ^ (1 / ((n : ℝ) + 1)) := by
  have hpow : kolmogorovNumber S n ^ (n + 1)
      ≤ ∏ k ∈ Finset.range (n + 1), kolmogorovNumber S k :=
    self_pow_le_prod (kolmogorovNumber_nonneg S)
      (antitone_nat_of_succ_le (kolmogorovNumber_antitone S)) n
  exact rpow_combine (kolmogorovNumber_nonneg S n)
    (Finset.prod_nonneg fun k _ => hilbertNumber_nonneg S k)
    (hpow.trans (prod_kolmogorovNumber_le S n))

omit [CompleteSpace X] [CompleteSpace Y] in
/-- **Maximal difference theorem.** The Gelfand and Kolmogorov numbers are
bounded by the geometric mean of the Hilbert numbers:
`max(cₙ(S), dₙ(S)) ≤ (n+1)·(∏_{k=0}^n hₖ(S))^{1/(n+1)}`.
-/
theorem max_gelfandNumber_kolmogorovNumber_le_geomMean_hilbertNumber
    (S : X →L[𝕜] Y) (n : ℕ) :
    max (gelfandNumber S n) (kolmogorovNumber S n) ≤
      ((n : ℝ) + 1) *
        (∏ k ∈ Finset.range (n + 1), hilbertNumber S k) ^ (1 / ((n : ℝ) + 1)) :=
  max_le (gelfandNumber_le_geomMean_hilbertNumber S n)
    (kolmogorovNumber_le_geomMean_hilbertNumber S n)

end SNumbers
