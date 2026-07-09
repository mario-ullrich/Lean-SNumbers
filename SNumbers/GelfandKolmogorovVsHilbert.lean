/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
import SNumbers.DetQuantity
import BasicResults.SVD

/-!
# The bound `max(cₙ, dₙ) ≤ e·(n+1)·hₙ` (Mityagin–Henkin–Pietsch)

For every bounded operator `S : X →L[𝕜] Y` between normed spaces over
`𝕜 ∈ {ℝ, ℂ}` and every `n`:

  `max (cₙ(S), dₙ(S)) ≤ e·(n+1)·hₙ(S)`,

where `cₙ, dₙ, hₙ` are the Gelfand, Kolmogorov and Hilbert numbers. Since
`hₙ` is the **smallest** s-number sequence, the right-hand side may be
replaced by `e·(n+1)·sₙ(S)` for any s-number sequence `s`
(`max_gelfandNumber_kolmogorovNumber_le_e_mul_sn`), in particular by the
Bernstein numbers — this proves the **Mityagin–Henkin conjecture** up to the
constant `e` (`max_gelfandNumber_kolmogorovNumber_le_e_mul_bernsteinNumber`).

The proof in fact gives the slightly sharper constant
`(n+1)^{n+1}/nⁿ ≤ e·(n+1)` (the `..._le_mul_hilbertNumber` versions).

This bound supersedes the former product route: since the sharp constants
telescope, `∏_{k=0}^n (k+1)^{k+1}/kᵏ = (n+1)^{n+1}`, the pointwise bound
`cₖ ≤ ((k+1)^{k+1}/kᵏ)·hₖ` immediately implies the product bound
`∏ cₖ ≤ (n+1)^{n+1}·∏ hₖ` and hence the **maximal difference theorem**
`max(cₙ, dₙ) ≤ (n+1)·(∏_{k=0}^n hₖ)^{1/(n+1)}` (Ullrich, *Inequalities
between s-numbers*, arXiv:2405.05509, Thm 3) with the identical constants.
Those statements, and the triangular-flag machinery that used to prove them,
have therefore been removed from the library; they can be re-derived from
`gelfandNumber_le_mul_hilbertNumber` / `kolmogorovNumber_le_mul_hilbertNumber`
in a few lines if ever needed.

## Proof outline

Everything runs through the determinant quantities `Δₖ(S)`
(`SNumbers.DetQuantity`).

1. **Oracles.** If `γ < cₙ(S)`, then for any `k ≤ n` functionals (the rows
   of an admissible `B`) there is `u ∈ B_X` with `B(Su) = 0` and
   `‖Su‖ > γ`; a Hahn–Banach functional `ρ` norms `Su`
   (`exists_gelfand_pair`). Dually for `γ < dₙ(S)`: there is `u ∈ B_X`
   whose image has distance `> γ` from `V = span(S(A(ℓ₂ᵏ)))`, and a
   functional `ρ` vanishing on `V` realises that distance
   (`exists_kolmogorov_pair`).
2. **Growth lemma.** Feeding an oracle output into the extension lemma
   (`exists_det_extension`) with the optimal weights `λ² = k/(k+1)`,
   `μ² = 1/(k+1)` gives, for `0 ≤ γ < max(cₙ, dₙ)` and `k ≤ n`:

     `(kᵏ/(k+1)^{k+1}) · γ · Δₖ(S) ≤ Δₖ₊₁(S)`

   (`mul_detNumber_le_detNumber_succ`). In particular `Δₖ(S) > 0` for all
   `k ≤ n+1` when `γ > 0` (`detNumber_pos`).
3. **Compression bound.** For any admissible pair `(A, B)` for `Δₙ₊₁` and
   `T := B∘S∘A`, the product of the top `n` approximation numbers of `T` is
   at most `Δₙ(S)`: the diagonal factorisation `B₁∘T∘A₁ = diag(a₀,…,aₙ)`
   (`SVD.IsCompactOperator.diagonalFactorisation`), compressed to the first
   `n` coordinates, is itself an admissible pair for `Δₙ`
   (`prod_approximationNumber_le_detNumber`).
4. **Upper bound.** Combining `|det T| = ∏ₖ aₖ(T)`
   (`prod_approximationNumber_eq_norm_det`) with step 3 and
   `aₙ(T) ≤ hₙ(S)` yields `Δₙ₊₁(S) ≤ hₙ(S)·Δₙ(S)`
   (`detNumber_succ_le_hilbertNumber_mul`). Note that this bounds **every**
   element of the sup defining `Δₙ₊₁`, so no near-maximiser needs to be
   selected.
5. Chaining steps 2 (at `k = n`) and 4 and cancelling `Δₙ(S) > 0` gives
   `γ·nⁿ/(n+1)^{n+1} ≤ hₙ(S)` for every `γ < cₙ(S)` (resp. `dₙ(S)`), hence
   the theorem; finally `(n+1)^{n+1}/nⁿ = (n+1)·(1+1/n)ⁿ ≤ e·(n+1)` via
   `1 + x ≤ eˣ`.

## Reference

M. Ullrich, *Another bound between s-numbers* (working note, 2026): the
bound `max(cₙ, dₙ) ≤ e·(n+1)·hₙ`, which proves the Mityagin–Henkin/Pietsch
conjecture `cₙ ≲ n·bₙ` up to the constant `e`.
-/

universe u

open ContinuousLinearMap
open scoped Pointwise

namespace SNumbers

variable {𝕜 : Type u} [RCLike 𝕜]
variable {X Y : Type u}
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]

/-! ### The two oracles -/

/-- **Gelfand oracle.** If `γ < cₙ(S)` and `k ≤ n`, then given
`B : Y → ℓ₂ᵏ` there are `u ∈ B_X` with `B(Su) = 0` and a norming functional
`ρ ∈ B_{Y'}` with `‖ρ(Su)‖ = ‖Su‖ > γ`. Indeed the common kernel of the `k`
functionals `y ↦ (By)ᵢ` composed with `S` is closed of codimension `≤ k ≤ n`,
so `S` retains norm `> γ` on it (`exists_mem_norm_gt_of_lt_gelfandNumber`);
Hahn–Banach (`exists_dual_vector''`) provides `ρ`. -/
lemma exists_gelfand_pair (S : X →L[𝕜] Y) {n k : ℕ} (hk : k ≤ n) {γ : ℝ}
    (hγ : γ < gelfandNumber S n) (B : Y →L[𝕜] EuclideanSpace 𝕜 (Fin k)) :
    ∃ (u : X) (ρ : Y →L[𝕜] 𝕜), ‖u‖ ≤ 1 ∧ ‖ρ‖ ≤ 1 ∧
      (∀ i, B (S u) i = 0) ∧ γ < ‖ρ (S u)‖ := by
  classical
  -- The coordinates of `B` as functionals on `Y`.
  set g : Fin k → (Y →L[𝕜] 𝕜) :=
    fun i => (innerSL 𝕜 (EuclideanSpace.single i (1 : 𝕜))).comp B with hg
  obtain ⟨M, hMc, hMr, hM0⟩ := exists_closed_codim_forall_eq_zero S g
  obtain ⟨u, huM, hu1, huγ⟩ := exists_mem_norm_gt_of_lt_gelfandNumber S hMc
    (hMr.trans (Nat.cast_le.mpr hk)) hγ
  obtain ⟨ρ, hρ1, hρval⟩ := exists_dual_vector'' 𝕜 (S u)
  refine ⟨u, ρ, hu1, hρ1, fun i => ?_, ?_⟩
  · have h0 := hM0 u huM i
    rw [hg, ContinuousLinearMap.comp_apply, innerSL_apply_apply,
      EuclideanSpace.inner_single_left, map_one, one_mul] at h0
    exact h0
  · rw [hρval, RCLike.norm_ofReal, abs_of_nonneg (norm_nonneg _)]
    exact huγ

/-- **Kolmogorov oracle.** If `γ < dₙ(S)` and `k ≤ n`, then given
`A : ℓ₂ᵏ → X` there are `u ∈ B_X` and `ρ ∈ B_{Y'}` vanishing on the range of
`S∘A` with `‖ρ(Su)‖ > γ`. Indeed `V := span{S(A eⱼ)}` has dimension
`≤ k ≤ n`, so some `u ∈ B_X` has `‖π_V(Su)‖ > γ`
(`exists_norm_mkQL_gt_of_lt_kolmogorovNumber`); a Hahn–Banach functional on
`Y ⧸ V` realising that quotient norm pulls back to `ρ`. -/
lemma exists_kolmogorov_pair (S : X →L[𝕜] Y) {n k : ℕ} (hk : k ≤ n) {γ : ℝ}
    (hγ : γ < kolmogorovNumber S n) (A : EuclideanSpace 𝕜 (Fin k) →L[𝕜] X) :
    ∃ (u : X) (ρ : Y →L[𝕜] 𝕜), ‖u‖ ≤ 1 ∧ ‖ρ‖ ≤ 1 ∧
      (∀ j, ρ (S (A (EuclideanSpace.single j (1 : 𝕜)))) = 0) ∧ γ < ‖ρ (S u)‖ := by
  classical
  set V : Submodule 𝕜 Y := Submodule.span 𝕜
    ↑(Finset.image (fun j : Fin k => S (A (EuclideanSpace.single j (1 : 𝕜))))
      Finset.univ) with hVdef
  haveI : FiniteDimensional 𝕜 V := FiniteDimensional.span_of_finite 𝕜 (Finset.finite_toSet _)
  haveI : IsClosed (V : Set Y) := V.closed_of_finiteDimensional
  have hVrank : Module.rank 𝕜 V ≤ (n : Cardinal) := by
    rw [hVdef]
    refine (rank_span_finset_le _).trans (Nat.cast_le.mpr ?_)
    exact (Finset.card_image_le.trans_eq
      (by rw [Finset.card_univ, Fintype.card_fin])).trans hk
  obtain ⟨u, hu1, huγ⟩ := exists_norm_mkQL_gt_of_lt_kolmogorovNumber S hVrank hγ
  obtain ⟨h, hh1, hhval⟩ := exists_dual_vector'' 𝕜 (V.mkQL (S u))
  refine ⟨u, h.comp V.mkQL, hu1, ?_, fun j => ?_, ?_⟩
  · exact (h.opNorm_comp_le V.mkQL).trans
      (mul_le_one₀ hh1 (norm_nonneg _) V.norm_mkQL_le)
  · have hmem : S (A (EuclideanSpace.single j (1 : 𝕜))) ∈ V := by
      rw [hVdef]
      exact Submodule.subset_span
        (Finset.mem_coe.mpr (Finset.mem_image_of_mem _ (Finset.mem_univ j)))
    rw [ContinuousLinearMap.comp_apply, V.mkQL_apply, V.mkQ_apply,
      (Submodule.Quotient.mk_eq_zero V).mpr hmem, map_zero]
  · rw [ContinuousLinearMap.comp_apply, hhval, RCLike.norm_ofReal,
      abs_of_nonneg (norm_nonneg _)]
    exact huγ

/-! ### The growth lemma -/

/-- `0 < nⁿ` in `ℝ` (with the convention `0⁰ = 1`). -/
private lemma pow_self_pos (n : ℕ) : (0 : ℝ) < (n : ℝ) ^ n := by
  cases n with
  | zero => norm_num
  | succ m => exact pow_pos (by exact_mod_cast Nat.succ_pos m) _

/-- The per-step growth factor `kᵏ/(k+1)^{k+1}` is positive. -/
private lemma growth_ratio_pos (k : ℕ) :
    (0 : ℝ) < (k : ℝ) ^ k / ((k : ℝ) + 1) ^ (k + 1) :=
  div_pos (pow_self_pos k) (pow_pos (by positivity) _)

/-- **Growth lemma (one step).** If `0 ≤ γ` is below `cₙ(S)` or below
`dₙ(S)`, then for every `k ≤ n`

  `(kᵏ/(k+1)^{k+1}) · γ · Δₖ(S) ≤ Δₖ₊₁(S)`.

For each admissible pair `(A, B)` for `Δₖ`, the appropriate oracle provides
`(u, ρ)` with `‖ρ(Su)‖ > γ` and the triangularity needed by the extension
lemma; the weights `λ² = k/(k+1)`, `μ² = 1/(k+1)` maximise `λ^{2k}μ²` and
give exactly the factor `kᵏ/(k+1)^{k+1}`. -/
lemma mul_detNumber_le_detNumber_succ (S : X →L[𝕜] Y) {n k : ℕ} (hk : k ≤ n)
    {γ : ℝ} (hγ0 : 0 ≤ γ)
    (hγ : γ < gelfandNumber S n ∨ γ < kolmogorovNumber S n) :
    (k : ℝ) ^ k / ((k : ℝ) + 1) ^ (k + 1) * γ * detNumber S k
      ≤ detNumber S (k + 1) := by
  set c : ℝ := (k : ℝ) ^ k / ((k : ℝ) + 1) ^ (k + 1) with hc
  have hc0 : 0 ≤ c := (growth_ratio_pos k).le
  -- Each admissible value `r` for `Δₖ` satisfies `c·γ·r ≤ Δₖ₊₁`.
  have hkey : ∀ r ∈ detSet S k, c * γ * r ≤ detNumber S (k + 1) := by
    rintro r ⟨A, B, hA, hB, rfl⟩
    -- The oracle, in either case.
    obtain ⟨u, ρ, hu, hρ, htri, hβ⟩ :
        ∃ (u : X) (ρ : Y →L[𝕜] 𝕜), ‖u‖ ≤ 1 ∧ ‖ρ‖ ≤ 1 ∧
          ((∀ i, B (S u) i = 0) ∨
            (∀ j, ρ (S (A (EuclideanSpace.single j (1 : 𝕜)))) = 0)) ∧
          γ < ‖ρ (S u)‖ := by
      rcases hγ with hγc | hγd
      · obtain ⟨u, ρ, h1, h2, h3, h4⟩ := exists_gelfand_pair S hk hγc B
        exact ⟨u, ρ, h1, h2, Or.inl h3, h4⟩
      · obtain ⟨u, ρ, h1, h2, h3, h4⟩ := exists_kolmogorov_pair S hk hγd A
        exact ⟨u, ρ, h1, h2, Or.inr h3, h4⟩
    -- The optimal weights.
    have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    set lam : ℝ := Real.sqrt ((k : ℝ) / ((k : ℝ) + 1)) with hlamdef
    set mu : ℝ := Real.sqrt (1 / ((k : ℝ) + 1)) with hmudef
    have hlam2 : lam ^ 2 = (k : ℝ) / ((k : ℝ) + 1) :=
      Real.sq_sqrt (by positivity)
    have hmu2 : mu ^ 2 = 1 / ((k : ℝ) + 1) := Real.sq_sqrt (by positivity)
    have hlm : lam ^ 2 + mu ^ 2 = 1 := by
      rw [hlam2, hmu2]; field_simp
    obtain ⟨A', B', hA', hB', hdet⟩ := exists_det_extension S hA hB hu hρ
      (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) hlm htri
    -- `λ^{2k}·μ² = kᵏ/(k+1)^{k+1}`.
    have hcval : lam ^ (2 * k) * mu ^ 2 = c := by
      rw [pow_mul, hlam2, hmu2, div_pow, div_mul_div_comm, mul_one, hc, pow_succ]
    calc c * γ * ‖LinearMap.det (B.comp (S.comp A) :
            EuclideanSpace 𝕜 (Fin k) →ₗ[𝕜] EuclideanSpace 𝕜 (Fin k))‖
        ≤ c * ‖ρ (S u)‖ * ‖LinearMap.det (B.comp (S.comp A) :
            EuclideanSpace 𝕜 (Fin k) →ₗ[𝕜] EuclideanSpace 𝕜 (Fin k))‖ := by
          gcongr
      _ = ‖LinearMap.det (B'.comp (S.comp A') :
            EuclideanSpace 𝕜 (Fin (k + 1)) →ₗ[𝕜] EuclideanSpace 𝕜 (Fin (k + 1)))‖ := by
          rw [hdet, hcval]
      _ ≤ detNumber S (k + 1) := norm_det_le_detNumber S hA' hB'
  -- Pass to the supremum over the admissible values.
  have hsmul : (c * γ) • detNumber S k ≤ detNumber S (k + 1) := by
    rw [detNumber, ← Real.sSup_smul_of_nonneg (mul_nonneg hc0 hγ0)]
    refine csSup_le ((detSet_nonempty S k).smul_set) ?_
    rintro x ⟨r, hr, rfl⟩
    simpa using hkey r hr
  simpa using hsmul

/-- **Positivity of the determinant quantities.** If `0 < γ` lies below
`cₙ(S)` or below `dₙ(S)`, then `Δₖ(S) > 0` for all `k ≤ n + 1`, by induction
from `Δ₀ = 1` via the growth lemma. -/
lemma detNumber_pos (S : X →L[𝕜] Y) {n : ℕ} {γ : ℝ} (hγ0 : 0 < γ)
    (hγ : γ < gelfandNumber S n ∨ γ < kolmogorovNumber S n) :
    ∀ k, k ≤ n + 1 → 0 < detNumber S k := by
  intro k
  induction k with
  | zero => intro _; rw [detNumber_zero]; exact one_pos
  | succ m ih =>
    intro hm
    have hm' : m ≤ n := Nat.lt_succ_iff.mp hm
    have hpos : 0 < (m : ℝ) ^ m / ((m : ℝ) + 1) ^ (m + 1) * γ * detNumber S m :=
      mul_pos (mul_pos (growth_ratio_pos m) hγ0) (ih (hm'.trans (Nat.le_succ n)))
    exact hpos.trans_le (mul_detNumber_le_detNumber_succ S hm' hγ0.le hγ)

/-! ### The compression bound and the upper bound `Δₙ₊₁ ≤ hₙ·Δₙ` -/

/-- **Compression bound.** For contractions `A : ℓ₂ⁿ⁺¹ → X`,
`B : Y → ℓ₂ⁿ⁺¹` and `T := B∘S∘A`, the product of the top `n` approximation
numbers of `T` is at most `Δₙ(S)`: the diagonal factorisation
`B₁∘T∘A₁ = diag(a₀(T),…,aₙ(T))` through contractions
(`SVD.IsCompactOperator.diagonalFactorisation`), compressed to the first `n`
coordinates by `padFin`/`projFin`, realises `∏_{k<n} aₖ(T)` as an admissible
determinant for `Δₙ(S)`. -/
lemma prod_approximationNumber_le_detNumber (S : X →L[𝕜] Y) {n : ℕ}
    {A : EuclideanSpace 𝕜 (Fin (n + 1)) →L[𝕜] X}
    {B : Y →L[𝕜] EuclideanSpace 𝕜 (Fin (n + 1))}
    (hA : ‖A‖ ≤ 1) (hB : ‖B‖ ≤ 1) :
    ∏ i ∈ Finset.range n, approximationNumber (B.comp (S.comp A)) i
      ≤ detNumber S n := by
  classical
  haveI : Nontrivial (EuclideanSpace 𝕜 (Fin (n + 1))) :=
    Module.nontrivial_of_finrank_pos (by rw [finrank_euclideanSpace_fin]; omega)
  set T := B.comp (S.comp A) with hTdef
  have hTc : IsCompactOperator T := isCompactOperator_of_locallyCompactSpace_rng T
  obtain ⟨A₁, B₁, hA₁, hB₁, hdiag⟩ := SVD.IsCompactOperator.diagonalFactorisation hTc n
  have hle : n ≤ n + 1 := Nat.le_succ n
  have hcast : ∀ i : Fin n, Fin.castLE hle i = Fin.castSucc i := fun i => rfl
  -- The compressed admissible pair.
  set A₂ : EuclideanSpace 𝕜 (Fin n) →L[𝕜] X :=
    (A.comp A₁).comp (padFin (p := 2)) with hA₂def
  set B₂ : Y →L[𝕜] EuclideanSpace 𝕜 (Fin n) :=
    (projFin (p := 2) hle).comp (B₁.comp B) with hB₂def
  have hA₂n : ‖A₂‖ ≤ 1 := by
    refine (opNorm_comp_le _ _).trans (mul_le_one₀ ?_ (norm_nonneg _)
      (norm_padFin_clm_le hle))
    exact (opNorm_comp_le _ _).trans (mul_le_one₀ hA (norm_nonneg _) hA₁)
  have hB₂n : ‖B₂‖ ≤ 1 := by
    refine (opNorm_comp_le _ _).trans (mul_le_one₀ (norm_projFin_clm_le hle)
      (norm_nonneg _) ?_)
    exact (opNorm_comp_le _ _).trans (mul_le_one₀ hB₁ (norm_nonneg _) hB)
  -- `padFin`/`projFin` act on standard basis vectors as expected.
  have hpad_single : ∀ j : Fin n,
      padFin (p := 2) (EuclideanSpace.single j (1 : 𝕜))
        = EuclideanSpace.single (Fin.castSucc j) (1 : 𝕜) := by
    intro j
    ext i
    rw [padFin_apply, PiLp.single_apply]
    by_cases hi : (i : ℕ) < n
    · rw [dif_pos hi, PiLp.single_apply]
      refine if_congr ?_ rfl rfl
      rw [Fin.ext_iff, Fin.ext_iff, Fin.val_castSucc]
    · rw [dif_neg hi, if_neg fun h => hi (by rw [h, Fin.val_castSucc]; exact j.isLt)]
  have hproj_single : ∀ j : Fin n,
      projFin (p := 2) hle (EuclideanSpace.single (Fin.castSucc j) (1 : 𝕜))
        = EuclideanSpace.single j (1 : 𝕜) := by
    intro j
    ext i
    rw [projFin_apply, PiLp.single_apply, PiLp.single_apply, hcast i]
    exact if_congr Fin.castSucc_inj.symm.symm rfl rfl
  -- The compressed operator is diagonal with entries `a₀(T), …, a_{n-1}(T)`.
  have hD : ∀ j : Fin n, (B₂.comp (S.comp A₂)) (EuclideanSpace.single j (1 : 𝕜))
      = (approximationNumber T (j : ℕ) : 𝕜) • EuclideanSpace.single j (1 : 𝕜) := by
    intro j
    have h1 : (B₂.comp (S.comp A₂)) (EuclideanSpace.single j (1 : 𝕜))
        = projFin (p := 2) hle
            (B₁ (T (A₁ (EuclideanSpace.single (Fin.castSucc j) (1 : 𝕜))))) := by
      rw [hA₂def, hB₂def, hTdef]
      simp only [ContinuousLinearMap.comp_apply, hpad_single j]
    rw [h1, hdiag (Fin.castSucc j), map_smul, hproj_single j, Fin.val_castSucc]
  -- Its determinant is the product of the diagonal entries.
  have hdet : LinearMap.det (B₂.comp (S.comp A₂) :
        EuclideanSpace 𝕜 (Fin n) →ₗ[𝕜] EuclideanSpace 𝕜 (Fin n))
      = ∏ j : Fin n, (approximationNumber T (j : ℕ) : 𝕜) := by
    set b := EuclideanSpace.basisFun (Fin n) 𝕜 with hb
    rw [← LinearMap.det_toMatrix b.toBasis]
    have hmat : LinearMap.toMatrix b.toBasis b.toBasis (B₂.comp (S.comp A₂) :
          EuclideanSpace 𝕜 (Fin n) →ₗ[𝕜] EuclideanSpace 𝕜 (Fin n))
        = Matrix.diagonal (fun j : Fin n => (approximationNumber T (j : ℕ) : 𝕜)) := by
      ext i j
      rw [LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,
        OrthonormalBasis.coe_toBasis, hb, EuclideanSpace.basisFun_repr,
        EuclideanSpace.basisFun_apply, ContinuousLinearMap.coe_coe, hD j,
        PiLp.smul_apply, PiLp.single_apply, smul_eq_mul,
        Matrix.diagonal_apply]
      by_cases hij : i = j
      · subst hij; rw [if_pos rfl, if_pos rfl, mul_one]
      · rw [if_neg hij, if_neg hij, mul_zero]
    rw [hmat, Matrix.det_diagonal]
  -- Conclude.
  have hnorm : ‖LinearMap.det (B₂.comp (S.comp A₂) :
        EuclideanSpace 𝕜 (Fin n) →ₗ[𝕜] EuclideanSpace 𝕜 (Fin n))‖
      = ∏ i ∈ Finset.range n, approximationNumber T i := by
    rw [hdet, norm_prod, ← Fin.prod_univ_eq_prod_range (fun i => approximationNumber T i) n]
    exact Finset.prod_congr rfl fun j _ => by
      rw [RCLike.norm_ofReal, abs_of_nonneg (approximationNumber_nonneg _ _)]
  calc ∏ i ∈ Finset.range n, approximationNumber T i
      = ‖LinearMap.det (B₂.comp (S.comp A₂) :
          EuclideanSpace 𝕜 (Fin n) →ₗ[𝕜] EuclideanSpace 𝕜 (Fin n))‖ := hnorm.symm
    _ ≤ detNumber S n := norm_det_le_detNumber S hA₂n hB₂n

/-- **Upper bound `Δₙ₊₁(S) ≤ hₙ(S)·Δₙ(S)`.** For every admissible pair for
`Δₙ₊₁` and `T := B∘S∘A`, split `|det T| = ∏_{k≤n} aₖ(T)` into the top `n`
factors (at most `Δₙ(S)`, by the compression bound) and the last factor
`aₙ(T) ≤ hₙ(S)`. This bounds **every** element of the supremum defining
`Δₙ₊₁(S)`, so no near-maximiser is needed. -/
lemma detNumber_succ_le_hilbertNumber_mul (S : X →L[𝕜] Y) (n : ℕ) :
    detNumber S (n + 1) ≤ hilbertNumber S n * detNumber S n := by
  refine csSup_le (detSet_nonempty S (n + 1)) ?_
  rintro r ⟨A, B, hA, hB, rfl⟩
  haveI : Nontrivial (EuclideanSpace 𝕜 (Fin (n + 1))) :=
    Module.nontrivial_of_finrank_pos (by rw [finrank_euclideanSpace_fin]; omega)
  have h1 : ‖LinearMap.det (B.comp (S.comp A) :
        EuclideanSpace 𝕜 (Fin (n + 1)) →ₗ[𝕜] EuclideanSpace 𝕜 (Fin (n + 1)))‖
      = ∏ i ∈ Finset.range (n + 1), approximationNumber (B.comp (S.comp A)) i := by
    have h := prod_approximationNumber_eq_norm_det (B.comp (S.comp A))
    rw [finrank_euclideanSpace_fin] at h
    exact h.symm
  have h2 : ∏ i ∈ Finset.range n, approximationNumber (B.comp (S.comp A)) i
      ≤ detNumber S n := prod_approximationNumber_le_detNumber S hA hB
  have h3 : approximationNumber (B.comp (S.comp A)) n ≤ hilbertNumber S n := by
    have h := approximationNumber_eucl_comp_comp_le_mul_hilbertNumber S n n A B
    calc approximationNumber (B.comp (S.comp A)) n
        ≤ ‖B‖ * ‖A‖ * hilbertNumber S n := h
      _ ≤ 1 * hilbertNumber S n :=
          mul_le_mul_of_nonneg_right (mul_le_one₀ hB (norm_nonneg _) hA)
            (hilbertNumber_nonneg S n)
      _ = hilbertNumber S n := one_mul _
  rw [h1, Finset.prod_range_succ]
  calc (∏ i ∈ Finset.range n, approximationNumber (B.comp (S.comp A)) i) *
        approximationNumber (B.comp (S.comp A)) n
      ≤ detNumber S n * hilbertNumber S n :=
        mul_le_mul h2 h3 (approximationNumber_nonneg _ _) (detNumber_nonneg S n)
    _ = hilbertNumber S n * detNumber S n := mul_comm _ _

/-! ### The main theorems -/

/-- **Gelfand vs. Hilbert numbers, sharp constant.**
`cₙ(S) ≤ ((n+1)^{n+1}/nⁿ)·hₙ(S)`. -/
theorem gelfandNumber_le_mul_hilbertNumber (S : X →L[𝕜] Y) (n : ℕ) :
    gelfandNumber S n ≤ ((n : ℝ) + 1) ^ (n + 1) / (n : ℝ) ^ n * hilbertNumber S n := by
  by_contra hcon
  rw [not_le] at hcon
  have hR0 : 0 ≤ ((n : ℝ) + 1) ^ (n + 1) / (n : ℝ) ^ n * hilbertNumber S n :=
    mul_nonneg (div_nonneg (by positivity) (pow_self_pos n).le)
      (hilbertNumber_nonneg S n)
  obtain ⟨γ, hγR, hγc⟩ := exists_between hcon
  have hγ0 : 0 < γ := lt_of_le_of_lt hR0 hγR
  have hor : γ < gelfandNumber S n ∨ γ < kolmogorovNumber S n := Or.inl hγc
  have hΔ : 0 < detNumber S n := detNumber_pos S hγ0 hor n (Nat.le_succ n)
  have hchain : (n : ℝ) ^ n / ((n : ℝ) + 1) ^ (n + 1) * γ * detNumber S n
      ≤ hilbertNumber S n * detNumber S n :=
    (mul_detNumber_le_detNumber_succ S le_rfl hγ0.le hor).trans
      (detNumber_succ_le_hilbertNumber_mul S n)
  have hkey : (n : ℝ) ^ n / ((n : ℝ) + 1) ^ (n + 1) * γ ≤ hilbertNumber S n :=
    le_of_mul_le_mul_right hchain hΔ
  have h1 : (n : ℝ) ^ n * γ ≤ hilbertNumber S n * ((n : ℝ) + 1) ^ (n + 1) := by
    rw [div_mul_eq_mul_div,
      div_le_iff₀ (pow_pos (by positivity : (0 : ℝ) < (n : ℝ) + 1) (n + 1))] at hkey
    exact hkey
  have h2 : γ ≤ ((n : ℝ) + 1) ^ (n + 1) / (n : ℝ) ^ n * hilbertNumber S n := by
    rw [div_mul_eq_mul_div, le_div_iff₀ (pow_self_pos n)]
    calc γ * (n : ℝ) ^ n = (n : ℝ) ^ n * γ := mul_comm _ _
      _ ≤ hilbertNumber S n * ((n : ℝ) + 1) ^ (n + 1) := h1
      _ = ((n : ℝ) + 1) ^ (n + 1) * hilbertNumber S n := mul_comm _ _
  exact absurd h2 (not_le.mpr hγR)

/-- **Kolmogorov vs. Hilbert numbers, sharp constant.**
`dₙ(S) ≤ ((n+1)^{n+1}/nⁿ)·hₙ(S)`. -/
theorem kolmogorovNumber_le_mul_hilbertNumber (S : X →L[𝕜] Y) (n : ℕ) :
    kolmogorovNumber S n
      ≤ ((n : ℝ) + 1) ^ (n + 1) / (n : ℝ) ^ n * hilbertNumber S n := by
  by_contra hcon
  rw [not_le] at hcon
  have hR0 : 0 ≤ ((n : ℝ) + 1) ^ (n + 1) / (n : ℝ) ^ n * hilbertNumber S n :=
    mul_nonneg (div_nonneg (by positivity) (pow_self_pos n).le)
      (hilbertNumber_nonneg S n)
  obtain ⟨γ, hγR, hγd⟩ := exists_between hcon
  have hγ0 : 0 < γ := lt_of_le_of_lt hR0 hγR
  have hor : γ < gelfandNumber S n ∨ γ < kolmogorovNumber S n := Or.inr hγd
  have hΔ : 0 < detNumber S n := detNumber_pos S hγ0 hor n (Nat.le_succ n)
  have hchain : (n : ℝ) ^ n / ((n : ℝ) + 1) ^ (n + 1) * γ * detNumber S n
      ≤ hilbertNumber S n * detNumber S n :=
    (mul_detNumber_le_detNumber_succ S le_rfl hγ0.le hor).trans
      (detNumber_succ_le_hilbertNumber_mul S n)
  have hkey : (n : ℝ) ^ n / ((n : ℝ) + 1) ^ (n + 1) * γ ≤ hilbertNumber S n :=
    le_of_mul_le_mul_right hchain hΔ
  have h1 : (n : ℝ) ^ n * γ ≤ hilbertNumber S n * ((n : ℝ) + 1) ^ (n + 1) := by
    rw [div_mul_eq_mul_div,
      div_le_iff₀ (pow_pos (by positivity : (0 : ℝ) < (n : ℝ) + 1) (n + 1))] at hkey
    exact hkey
  have h2 : γ ≤ ((n : ℝ) + 1) ^ (n + 1) / (n : ℝ) ^ n * hilbertNumber S n := by
    rw [div_mul_eq_mul_div, le_div_iff₀ (pow_self_pos n)]
    calc γ * (n : ℝ) ^ n = (n : ℝ) ^ n * γ := mul_comm _ _
      _ ≤ hilbertNumber S n * ((n : ℝ) + 1) ^ (n + 1) := h1
      _ = ((n : ℝ) + 1) ^ (n + 1) * hilbertNumber S n := mul_comm _ _
  exact absurd h2 (not_le.mpr hγR)

/-- **Main theorem, sharp constant.**
`max(cₙ(S), dₙ(S)) ≤ ((n+1)^{n+1}/nⁿ)·hₙ(S)`. -/
theorem max_gelfandNumber_kolmogorovNumber_le_mul_hilbertNumber
    (S : X →L[𝕜] Y) (n : ℕ) :
    max (gelfandNumber S n) (kolmogorovNumber S n)
      ≤ ((n : ℝ) + 1) ^ (n + 1) / (n : ℝ) ^ n * hilbertNumber S n :=
  max_le (gelfandNumber_le_mul_hilbertNumber S n)
    (kolmogorovNumber_le_mul_hilbertNumber S n)

/-! ### The constant `(n+1)^{n+1}/nⁿ ≤ e·(n+1)` -/

/-- `(n+1)^{n+1}/nⁿ = (n+1)·(1+1/n)ⁿ ≤ e·(n+1)`, from `1 + x ≤ eˣ` at
`x = 1/n` raised to the `n`-th power. -/
private lemma ratio_le_exp_mul (n : ℕ) :
    ((n : ℝ) + 1) ^ (n + 1) / (n : ℝ) ^ n ≤ Real.exp 1 * ((n : ℝ) + 1) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · norm_num
  · have hN : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have h1 : 1 + 1 / (n : ℝ) ≤ Real.exp (1 / (n : ℝ)) := by
      have := Real.add_one_le_exp (1 / (n : ℝ)); linarith
    have h2 : (1 + 1 / (n : ℝ)) ^ n ≤ Real.exp 1 := by
      calc (1 + 1 / (n : ℝ)) ^ n
          ≤ Real.exp (1 / (n : ℝ)) ^ n := pow_le_pow_left₀ (by positivity) h1 n
        _ = Real.exp ((n : ℝ) * (1 / (n : ℝ))) := (Real.exp_nat_mul _ n).symm
        _ = Real.exp 1 := by rw [mul_one_div, div_self hN.ne']
    have h3 : ((n : ℝ) + 1) ^ n ≤ Real.exp 1 * (n : ℝ) ^ n := by
      have hfac : (n : ℝ) + 1 = (n : ℝ) * (1 + 1 / (n : ℝ)) := by field_simp
      calc ((n : ℝ) + 1) ^ n = (n : ℝ) ^ n * (1 + 1 / (n : ℝ)) ^ n := by
            rw [hfac, mul_pow]
        _ ≤ (n : ℝ) ^ n * Real.exp 1 := mul_le_mul_of_nonneg_left h2 (by positivity)
        _ = Real.exp 1 * (n : ℝ) ^ n := mul_comm _ _
    rw [div_le_iff₀ (pow_self_pos n)]
    calc ((n : ℝ) + 1) ^ (n + 1) = ((n : ℝ) + 1) ^ n * ((n : ℝ) + 1) := pow_succ _ _
      _ ≤ Real.exp 1 * (n : ℝ) ^ n * ((n : ℝ) + 1) :=
          mul_le_mul_of_nonneg_right h3 (by positivity)
      _ = Real.exp 1 * ((n : ℝ) + 1) * (n : ℝ) ^ n := by ring

/-- **Main theorem.** `max(cₙ(S), dₙ(S)) ≤ e·(n+1)·hₙ(S)`: the Gelfand and
Kolmogorov numbers exceed the (smallest) s-numbers `hₙ` by at most a factor
linear in `n`. -/
theorem max_gelfandNumber_kolmogorovNumber_le_e_mul_hilbertNumber
    (S : X →L[𝕜] Y) (n : ℕ) :
    max (gelfandNumber S n) (kolmogorovNumber S n)
      ≤ Real.exp 1 * ((n : ℝ) + 1) * hilbertNumber S n :=
  (max_gelfandNumber_kolmogorovNumber_le_mul_hilbertNumber S n).trans
    (mul_le_mul_of_nonneg_right (ratio_le_exp_mul n) (hilbertNumber_nonneg S n))

/-- **Main theorem for arbitrary s-numbers.** Since the Hilbert numbers are
the smallest s-number sequence (`hilbertNumber_le_sn`), the bound holds with
`hₙ` replaced by any s-number sequence:
`max(cₙ(S), dₙ(S)) ≤ e·(n+1)·sₙ(S)`. -/
theorem max_gelfandNumber_kolmogorovNumber_le_e_mul_sn {s : Family 𝕜}
    (hs : IsSNumberSequence s) (S : X →L[𝕜] Y) (n : ℕ) :
    max (gelfandNumber S n) (kolmogorovNumber S n)
      ≤ Real.exp 1 * ((n : ℝ) + 1) * s S n :=
  (max_gelfandNumber_kolmogorovNumber_le_e_mul_hilbertNumber S n).trans
    (mul_le_mul_of_nonneg_left (hilbertNumber_le_sn hs S n) (by positivity))

/-- **The Mityagin–Henkin conjecture, up to the constant `e`.** The Gelfand
and Kolmogorov numbers are bounded by the Bernstein numbers:
`max(cₙ(S), dₙ(S)) ≤ e·(n+1)·bₙ(S)`. -/
theorem max_gelfandNumber_kolmogorovNumber_le_e_mul_bernsteinNumber
    (S : X →L[𝕜] Y) (n : ℕ) :
    max (gelfandNumber S n) (kolmogorovNumber S n)
      ≤ Real.exp 1 * ((n : ℝ) + 1) * bernsteinNumber S n :=
  max_gelfandNumber_kolmogorovNumber_le_e_mul_sn
    isSNumberSequence_bernsteinNumber S n

end SNumbers
