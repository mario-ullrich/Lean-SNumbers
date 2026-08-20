/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
import SNumbers.Entropy
import SNumbers.Inequalities

/-!
# Bounding the Gelfand and Kolmogorov numbers by the entropy numbers

The entropy numbers `eₙ` are not an `s`-number sequence (they fail (S4) and
(S5), see `SNumbers.Entropy`), but they dominate the Gelfand and Kolmogorov
numbers in a precise sense, and that is what ties those two sequences to
compactness.

## The covering estimates

Everything in this file rests on two elementary observations about a finite
`ε`-net `y₁, …, y_k` of the image `S(B_X)` of the closed unit ball:

* the span of the net is a subspace of dimension `≤ k` from which `S(B_X)`
  deviates by at most `ε`, so `d_k(S) ≤ ε`
  (`kolmogorovNumber_le_of_fin_net`);
* the common kernel of norming functionals for the `yᵢ` is a closed subspace of
  codimension `≤ k` on whose unit ball `S` has norm at most `2ε`, so
  `c_k(S) ≤ 2ε` (`gelfandNumber_le_two_mul_of_fin_net`).

The second one is where Hahn–Banach enters, which is why this file works over
`RCLike 𝕜` (that is, `ℝ` or `ℂ`) rather than over a general normed field.

## Main results

* `SNumbers.kolmogorovNumber_le_of_fin_net`,
  `SNumbers.gelfandNumber_le_two_mul_of_fin_net` — the two covering estimates.
* `SNumbers.kolmogorovNumber_two_pow_le_entropyNumber` :
    `d_{2ⁿ} S ≤ eₙ S`.
* `SNumbers.gelfandNumber_two_pow_le_two_mul_entropyNumber` :
    `c_{2ⁿ} S ≤ 2 · eₙ S`.

## Implementation notes

The two dyadic bounds are exactly what is needed to transport `eₙ S → 0` to
`dₙ S → 0` and `cₙ S → 0` (done in `AddOns.Compact`): a shift of the index by a
*fixed* function of `n` survives taking limits, because both sequences are
antitone. This is worth spelling out because the sharper pointwise bounds
`max(cₙ, dₙ) ≤ (n+1)·eₙ` and `hₙ ≤ 2·eₙ` do **not** serve that purpose —
`(n+1)·eₙ` need not tend to `0` when `eₙ` does — even though they are the
better estimates for a fixed `n`.

The net is passed around as a function `Fin k → Y` rather than as the `Finset`
of `SNumbers.entropySet`, because the index `k` is exactly the index at which
the resulting bound on `d_k` / `c_k` holds. The translation between the two
forms is `exists_fin_net_of_mem_entropySet`.

## References

* A. Pietsch, *Operator ideals*, 12.3.
* A. Pietsch, *Eigenvalues and s-numbers*, 2.4.
-/

universe u

open Filter Topology
open scoped Cardinal
open ContinuousLinearMap

namespace SNumbers

variable {𝕜 : Type u} [RCLike 𝕜]
variable {X Y : Type u}
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]

/-! ### Covering estimates -/

/-- The span of `k` vectors has dimension at most `k`. -/
private lemma rank_span_range_le {k : ℕ} (y : Fin k → Y) :
    Module.rank 𝕜 (Submodule.span 𝕜 (Set.range y)) ≤ (k : Cardinal) := by
  classical
  -- Present the range as a `Finset`, so that the bound is a cast of a
  -- natural number and no universe lifting is involved.
  have hset : Set.range y = ((Finset.univ.image y : Finset Y) : Set Y) := by simp
  rw [hset]
  refine (rank_span_finset_le _).trans ?_
  have hcard : (Finset.univ.image y).card ≤ k := by
    simpa using Finset.card_image_le (s := (Finset.univ : Finset (Fin k))) (f := y)
  exact_mod_cast hcard

/-- **Covering estimate for the Kolmogorov numbers.** If the image of the closed
unit ball is covered by the `ε`-balls around `k` points `y i`, then
`d_k(S) ≤ ε`: the span `V` of the `y i` has dimension at most `k`, and
`‖π_V (S x)‖ = ‖π_V (S x - y i)‖ ≤ ‖S x - y i‖ ≤ ε` for a suitable `i`. -/
lemma kolmogorovNumber_le_of_fin_net {S : X →L[𝕜] Y} {k : ℕ} {y : Fin k → Y}
    {ε : ℝ} (hcov : ∀ x : X, ‖x‖ ≤ 1 → ∃ i, ‖S x - y i‖ ≤ ε) :
    kolmogorovNumber S k ≤ ε := by
  set V : Submodule 𝕜 Y := Submodule.span 𝕜 (Set.range y) with hV
  refine (kolmogorovNumber_le_deviation (rank_span_range_le y)).trans ?_
  show ‖V.mkQL.comp S‖ ≤ ε
  refine ContinuousLinearMap.opNorm_le_of_unit_closedBall _ fun x hx => ?_
  obtain ⟨i, hi⟩ := hcov x hx
  -- `y i` lies in `V`, so it is killed by the quotient map.
  have hzero : V.mkQL (y i) = 0 := by
    simp only [Submodule.mkQL_apply, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero]
    exact Submodule.subset_span ⟨i, rfl⟩
  calc ‖(V.mkQL.comp S) x‖
      = ‖V.mkQL (S x - y i)‖ := by
        simp only [coe_comp, Function.comp_apply, map_sub, hzero, sub_zero]
    _ ≤ ‖S x - y i‖ := V.norm_mkQL_apply_le _
    _ ≤ ε := hi

/-- **Covering estimate for the Gelfand numbers.** If the image of the closed
unit ball is covered by the `ε`-balls around `k` points `y i`, then
`c_k(S) ≤ 2ε`.

Choose norming functionals `bᵢ` for the `y i` (Hahn–Banach) and let `M` be the
common kernel of the `bᵢ ∘ S`, a closed subspace of codimension `≤ k`. For
`x ∈ M` in the unit ball pick `i` with `‖S x - y i‖ ≤ ε`; since `bᵢ (S x) = 0`,
`‖y i‖ = bᵢ (y i - S x) ≤ ε`, and therefore `‖S x‖ ≤ 2ε`. -/
lemma gelfandNumber_le_two_mul_of_fin_net {S : X →L[𝕜] Y} {k : ℕ} {y : Fin k → Y}
    {ε : ℝ} (hcov : ∀ x : X, ‖x‖ ≤ 1 → ∃ i, ‖S x - y i‖ ≤ ε) :
    gelfandNumber S k ≤ 2 * ε := by
  classical
  choose b hb_norm hb_app using fun i : Fin k => exists_dual_vector'' 𝕜 (y i)
  obtain ⟨M, hM_closed, hM_rank, hM_ker⟩ := exists_closed_codim_forall_eq_zero S b
  refine (gelfandNumber_le_deviation hM_closed hM_rank).trans ?_
  show ‖S.comp M.subtypeL‖ ≤ 2 * ε
  refine ContinuousLinearMap.opNorm_le_of_unit_closedBall _ fun z hz => ?_
  obtain ⟨i, hi⟩ := hcov (z : X) (by simpa using hz)
  -- The norming functional of `y i` vanishes on `S x`, so `‖y i‖` is small.
  have h_yi : ‖y i‖ ≤ ε := by
    have h0 : b i (S (z : X)) = 0 := hM_ker (z : X) z.2 i
    have heq : b i (y i - S (z : X)) = ((‖y i‖ : ℝ) : 𝕜) := by
      rw [map_sub, hb_app i, h0, sub_zero]
    have hnorm : ‖y i‖ = ‖b i (y i - S (z : X))‖ := by
      rw [heq, RCLike.norm_ofReal, abs_of_nonneg (norm_nonneg _)]
    rw [hnorm]
    calc ‖b i (y i - S (z : X))‖
        ≤ ‖b i‖ * ‖y i - S (z : X)‖ := (b i).le_opNorm _
      _ ≤ 1 * ‖y i - S (z : X)‖ :=
          mul_le_mul_of_nonneg_right (hb_norm i) (norm_nonneg _)
      _ = ‖S (z : X) - y i‖ := by rw [one_mul, norm_sub_rev]
      _ ≤ ε := hi
  calc ‖(S.comp M.subtypeL) z‖
      = ‖S (z : X)‖ := by simp
    _ ≤ ‖S (z : X) - y i‖ + ‖y i‖ := by
        simpa using norm_add_le (S (z : X) - y i) (y i)
    _ ≤ ε + ε := add_le_add hi h_yi
    _ = 2 * ε := by ring

/-! ### Dyadic comparison with the entropy numbers -/

/-- Repackaging of an admissible entropy radius: a cover of `S(B_X)` by at most
`2 ^ n` closed `ε`-balls, with the centres presented as a function
`Fin k → Y` where `k ≤ 2 ^ n` is the actual number of centres. -/
private lemma exists_fin_net_of_mem_entropySet {S : X →L[𝕜] Y} {n : ℕ} {ε : ℝ}
    (hε : ε ∈ entropySet S n) :
    ∃ (k : ℕ) (y : Fin k → Y), k ≤ 2 ^ n ∧
      ∀ x : X, ‖x‖ ≤ 1 → ∃ i, ‖S x - y i‖ ≤ ε := by
  classical
  obtain ⟨-, N, hN_card, hcov⟩ := hε
  refine ⟨N.card, fun i => ((N.equivFin.symm i : ↥N) : Y), hN_card, fun x hx => ?_⟩
  have hmem : S x ∈ ⋃ w ∈ (N : Set Y), Metric.closedBall w ε :=
    hcov ⟨x, mem_closedBall_zero_iff.mpr hx, rfl⟩
  simp only [Set.mem_iUnion, Metric.mem_closedBall, exists_prop] at hmem
  obtain ⟨w, hw, hdist⟩ := hmem
  refine ⟨N.equivFin ⟨w, by simpa using hw⟩, ?_⟩
  simpa [dist_eq_norm] using hdist

/-- **`d_{2ⁿ} S ≤ eₙ S`.** A cover of `S(B_X)` by `2 ^ n` balls of radius `ε`
gives a subspace of dimension at most `2 ^ n` — the span of the centres — from
which `S(B_X)` deviates by at most `ε`. -/
theorem kolmogorovNumber_two_pow_le_entropyNumber (S : X →L[𝕜] Y) (n : ℕ) :
    kolmogorovNumber S (2 ^ n) ≤ entropyNumber S n := by
  rw [entropyNumber_def]
  refine le_csInf (entropySet_nonempty S n) fun ε hε => ?_
  obtain ⟨k, y, hk, hnet⟩ := exists_fin_net_of_mem_entropySet hε
  exact (kolmogorovNumber_antitone' S hk).trans (kolmogorovNumber_le_of_fin_net hnet)

/-- **`c_{2ⁿ} S ≤ 2 · eₙ S`.** The Gelfand counterpart of
`kolmogorovNumber_two_pow_le_entropyNumber`; the factor `2` comes from the
norming-functional argument. -/
theorem gelfandNumber_two_pow_le_two_mul_entropyNumber (S : X →L[𝕜] Y) (n : ℕ) :
    gelfandNumber S (2 ^ n) ≤ 2 * entropyNumber S n := by
  have key : gelfandNumber S (2 ^ n) / 2 ≤ entropyNumber S n := by
    rw [entropyNumber_def]
    refine le_csInf (entropySet_nonempty S n) fun ε hε => ?_
    obtain ⟨k, y, hk, hnet⟩ := exists_fin_net_of_mem_entropySet hε
    have h := (gelfandNumber_antitone' S hk).trans
      (gelfandNumber_le_two_mul_of_fin_net hnet)
    linarith
  linarith

end SNumbers
