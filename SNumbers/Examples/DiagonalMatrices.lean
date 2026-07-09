/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
import SNumbers.Approximation
import SNumbers.Bernstein
import SNumbers.Gelfand
import SNumbers.Kolmogorov
import SNumbers.Hilbert
import SNumbers.PiLpCoordinates
import Mathlib.Analysis.Normed.Lp.PiLp

/-!
# Example: s-numbers of diagonal operators

This file is a worked **example** illustrating the abstract s-number theory on a
concrete family of operators: the **diagonal operators**

`D_σ : ℓ^p_m → ℓ^p_m`,  `D_σ x = (σ_i · x_i)_i`,

where `σ : Fin m → 𝕜` is the diagonal and the domain/codomain are the
finite-dimensional sequence spaces `ℓ^p_m = PiLp p (fun _ : Fin m => 𝕜)`.

We treat the case where domain and codomain carry the **same** exponent `p`
(`q = p`).

## Main contents

* `DiagCLM p σ` — the diagonal operator as a continuous linear map, with operator
  norm `norm_DiagCLM : ‖D_σ‖ = ⨆ i, ‖σ i‖`.
* `projFin` / `padFin` — the coordinate projection and embedding between `ℓ^p_n`
  and `ℓ^p_m`, both contractions (`norm_projFin_clm_le`, `norm_padFin_clm_le`).
* `sn_DiagCLM_eq` — the main result: for every **strict** s-number sequence `s`,
  `sₙ(D_σ) = ‖σ_n‖` (the `(n+1)`-th largest entry) when the diagonal is
  non-increasing in modulus and `n < m`. Specialised to the named examples:
  `approximationNumber_DiagCLM_eq`, `gelfandNumber_DiagCLM_eq`,
  `kolmogorovNumber_DiagCLM_eq`, `bernsteinNumber_DiagCLM_eq`.
* `hilbertNumber_DiagCLM_le` — for the Hilbert numbers only the bound
  `hₙ(D_σ) ≤ ‖σ_n‖` holds (equality can fail for `p ≠ 2`).
* `sn_id_piLp` — the unit diagonal `σ ≡ 1` is the identity, with `sₙ(id) = 1`
  for `n < m` directly from (S5').

## References

* A. Pietsch, *Eigenvalues and s-numbers*, Cambridge Univ. Press, 1987.
-/

universe u

open scoped ENNReal
open ContinuousLinearMap

namespace SNumbers

variable {𝕜 : Type u} [RCLike 𝕜] {m : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-! ## A monotonicity lemma for the `L^p` norm

The `L^p` norm on a finite product is monotone under coordinatewise domination
of the norms. -/

/-- If `‖x i‖ ≤ ‖y i‖` for every coordinate `i`, then `‖x‖ ≤ ‖y‖` in `PiLp p`.
Proved by the `p = ∞` (suprema) and `1 ≤ p.toReal` (sums of `p`-th powers)
cases of the explicit norm formula. -/
lemma piLp_norm_mono {ι : Type*} [Fintype ι] {β : ι → Type*}
    [∀ i, SeminormedAddCommGroup (β i)] {x y : PiLp p β}
    (h : ∀ i, ‖x i‖ ≤ ‖y i‖) : ‖x‖ ≤ ‖y‖ := by
  rcases p.dichotomy with (rfl | hp)
  · rw [PiLp.norm_eq_ciSup, PiLp.norm_eq_ciSup]
    exact ciSup_mono (Finite.bddAbove_range _) h
  · have hp0 : 0 < p.toReal := zero_lt_one.trans_le hp
    rw [PiLp.norm_eq_sum hp0, PiLp.norm_eq_sum hp0]
    have hsum : (∑ i, ‖x i‖ ^ p.toReal) ≤ ∑ i, ‖y i‖ ^ p.toReal :=
      Finset.sum_le_sum fun i _ => Real.rpow_le_rpow (norm_nonneg _) (h i) hp0.le
    exact Real.rpow_le_rpow (Finset.sum_nonneg fun i _ => Real.rpow_nonneg (norm_nonneg _) _)
      hsum (one_div_nonneg.mpr hp0.le)

/-! ## Stage 0 — the diagonal operator and its norm -/

/-- The **diagonal operator** `D_σ : ℓ^p_m → ℓ^p_m`, `x ↦ (σ_i · x_i)`, as a
continuous linear map. The domain is finite-dimensional, so continuity is
automatic (`LinearMap.toContinuousLinearMap`). -/
noncomputable def DiagCLM (p : ℝ≥0∞) [Fact (1 ≤ p)] (σ : Fin m → 𝕜) :
    PiLp p (fun _ : Fin m => 𝕜) →L[𝕜] PiLp p (fun _ : Fin m => 𝕜) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x => WithLp.toLp p (fun i => σ i • x i)
      map_add' := fun x y => by
        ext i; simp [mul_add]
      map_smul' := fun c x => by
        ext i; simp [mul_left_comm] }

@[simp] lemma DiagCLM_apply (σ : Fin m → 𝕜) (x : PiLp p (fun _ : Fin m => 𝕜))
    (i : Fin m) : (DiagCLM p σ x) i = σ i • x i := rfl

/-- **Operator norm of a diagonal operator** (same exponent `p` on both sides):
`‖D_σ‖ = ⨆ i, ‖σ i‖`, the largest modulus of a diagonal entry. The supremum is
attained at some coordinate `j₀`; the upper bound dominates `D_σ` coordinatewise
by the scalar multiple `σ j₀ • ·`, and the lower bound tests `D_σ` on the basis
vector `e_{j₀}`. -/
theorem norm_DiagCLM [Nonempty (Fin m)] (σ : Fin m → 𝕜) :
    ‖DiagCLM p σ‖ = ⨆ i, ‖σ i‖ := by
  obtain ⟨j₀, hj₀⟩ := Finite.exists_max (fun i => ‖σ i‖)
  have hMeq : (⨆ i, ‖σ i‖) = ‖σ j₀‖ :=
    le_antisymm (ciSup_le hj₀) (le_ciSup (Finite.bddAbove_range fun i => ‖σ i‖) j₀)
  rw [hMeq]
  refine le_antisymm ?_ ?_
  · -- Upper bound: `‖D_σ x‖ ≤ ‖σ j₀‖ * ‖x‖` for all `x`.
    refine opNorm_le_bound _ (norm_nonneg _) fun x => ?_
    calc ‖DiagCLM p σ x‖
        ≤ ‖σ j₀ • x‖ := by
          refine piLp_norm_mono fun i => ?_
          rw [DiagCLM_apply, PiLp.smul_apply, norm_smul, norm_smul]
          exact mul_le_mul_of_nonneg_right (hj₀ i) (norm_nonneg _)
      _ = ‖σ j₀‖ * ‖x‖ := norm_smul _ _
  · -- Lower bound: test on the basis vector `e_{j₀} = single p j₀ 1`.
    set e : PiLp p (fun _ : Fin m => 𝕜) := PiLp.single p j₀ (1 : 𝕜) with he_def
    have hDe : DiagCLM p σ e = PiLp.single p j₀ (σ j₀) := by
      ext k
      rcases eq_or_ne k j₀ with rfl | hk
      · simp [he_def]
      · simp [he_def, hk]
    have he : ‖e‖ = 1 := by rw [he_def, PiLp.norm_single, norm_one]
    have hbound := (DiagCLM p σ).le_opNorm e
    rw [hDe, PiLp.norm_single, he, mul_one] at hbound
    exact hbound

/-! ## Coordinate embedding and projection between `ℓ^p_n` and `ℓ^p_m`

To compute the s-numbers we relate `ℓ^p_m` to the lower-dimensional `ℓ^p_n`
via the coordinate maps `projFin` (keep the first `n` coordinates) and
`padFin` (extend by zeros), both contractions with `projFin ∘ padFin = id`.
They now live in `SNumbers.PiLpCoordinates` (they are also used by the
determinant quantities in `SNumbers.DetQuantity`); only the two rank
lemmas specific to this example remain here. -/

omit [Fact (1 ≤ p)] in
/-- The dimension of `ℓ^p_k = PiLp p (Fin k → 𝕜)` is `k`. -/
lemma finrank_piLp (k : ℕ) :
    Module.finrank 𝕜 (PiLp p (fun _ : Fin k => 𝕜)) = k := by
  rw [(WithLp.linearEquiv p 𝕜 (Fin k → 𝕜)).finrank_eq, Module.finrank_pi 𝕜, Fintype.card_fin]

/-- The rank of the identity on `ℓ^p_k` is `k` (as a `Cardinal`). Used to bound
the rank of finite-rank approximants that factor through `ℓ^p_k`. -/
lemma rank_id_piLp (k : ℕ) :
    (ContinuousLinearMap.id 𝕜 (PiLp p (fun _ : Fin k => 𝕜))).rank = (k : Cardinal) := by
  have h1 : (ContinuousLinearMap.id 𝕜 (PiLp p (fun _ : Fin k => 𝕜))).rank
      = Module.rank 𝕜 (PiLp p (fun _ : Fin k => 𝕜)) := by
    rw [ContinuousLinearMap.rank, ContinuousLinearMap.coe_id]
    show Module.rank 𝕜 (LinearMap.range (LinearMap.id : _ →ₗ[𝕜] _)) = _
    rw [LinearMap.range_id]; exact Submodule.topEquiv.rank_eq
  rw [h1, ← Module.finrank_eq_rank, finrank_piLp]

/-! ## Stage 2 — the upper bound `aₙ(D_σ) ≤ σ_{n+1}` for every s-number

We assume the diagonal is arranged in non-increasing order of modulus
(`Antitone fun i => ‖σ i‖`), so the `(n+1)`-th largest entry is `‖σ_n‖`.
Truncating `D_σ` to its top `n` coordinates yields a rank-`≤ n` approximant
whose residual is the diagonal of the remaining entries, of norm `‖σ_n‖`.
Since the approximation numbers are the largest s-numbers, the bound transfers
to **every** s-number sequence. -/

/-- **Upper bound.** If the diagonal is non-increasing in modulus, the `n`-th
approximation number of `D_σ : ℓ^p_m → ℓ^p_m` is at most `‖σ_n‖` (the
`(n+1)`-th largest entry), for `n < m`. -/
theorem approximationNumber_DiagCLM_le {σ : Fin m → 𝕜}
    (hσ : _root_.Antitone fun i => ‖σ i‖) {n : ℕ} (hn : n < m) :
    approximationNumber (DiagCLM p σ) n ≤ ‖σ ⟨n, hn⟩‖ := by
  haveI : Nonempty (Fin m) := ⟨⟨n, hn⟩⟩
  -- The rank-`≤ n` approximant `L = D_σ ∘ Pₙ`, written as `B ∘ id_{ℓ^p_n} ∘ A`
  -- so its rank is bounded by `dim ℓ^p_n = n`.
  set A : PiLp p (fun _ : Fin m => 𝕜) →L[𝕜] PiLp p (fun _ : Fin n => 𝕜) :=
    projFin hn.le with hA
  set B : PiLp p (fun _ : Fin n => 𝕜) →L[𝕜] PiLp p (fun _ : Fin m => 𝕜) :=
    (DiagCLM p σ).comp padFin with hB
  set L := B.comp ((ContinuousLinearMap.id 𝕜 (PiLp p (fun _ : Fin n => 𝕜))).comp A) with hL
  -- The residual diagonal `ρ`: the entries from index `n` on.
  set ρ : Fin m → 𝕜 := fun i => if (i : ℕ) < n then 0 else σ i with hρ
  have hLrank : L.rank ≤ (n : Cardinal) :=
    (ContinuousLinearMap.rank_comp_comp_le A _ B).trans_eq (rank_id_piLp n)
  -- `D_σ - L = DiagCLM ρ`.
  have hres : DiagCLM p σ - L = DiagCLM p ρ := by
    ext x i
    simp only [hL, hA, hB, ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.id_apply, DiagCLM_apply, PiLp.sub_apply]
    rw [padFin_projFin_apply]
    by_cases hi : (i : ℕ) < n <;> simp [hρ, hi]
  -- The residual norm is `⨆_{i ≥ n} ‖σ i‖ = ‖σ_n‖`.
  have hsup : (⨆ i, ‖ρ i‖) = ‖σ ⟨n, hn⟩‖ := by
    refine le_antisymm (ciSup_le fun i => ?_) ?_
    · by_cases hi : (i : ℕ) < n
      · simp [hρ, hi]
      · have hle : (⟨n, hn⟩ : Fin m) ≤ i := by
          simp only [Fin.le_def]; omega
        simpa [hρ, hi] using hσ hle
    · have : ‖σ ⟨n, hn⟩‖ = ‖ρ ⟨n, hn⟩‖ := by simp [hρ]
      rw [this]
      exact le_ciSup (Finite.bddAbove_range fun i => ‖ρ i‖) (⟨n, hn⟩ : Fin m)
  calc approximationNumber (DiagCLM p σ) n
      ≤ ‖DiagCLM p σ - L‖ := approximationNumber_le_norm_sub hLrank
    _ = ‖DiagCLM p ρ‖ := by rw [hres]
    _ = ⨆ i, ‖ρ i‖ := norm_DiagCLM ρ
    _ = ‖σ ⟨n, hn⟩‖ := hsup

/-! ## Stage 3 — the lower bound `σ_{n+1} ≤ sₙ(D_σ)` for strict s-numbers

For the lower bound we factor the identity on `ℓ^p_{n+1}` (whose dimension
`n+1 > n` forces `sₙ(id) = 1` by the strict normalisation (S5')) through `D_σ`:

`id_{ℓ^p_{n+1}} = B ∘ D_σ ∘ A`,

with `A = padFin` the isometric embedding of the top `n+1` coordinates
(`‖A‖ ≤ 1`) and `B` the projection followed by division by the diagonal entries
(`‖B‖ ≤ ‖σ_n‖⁻¹`). The (S3) ideal property then gives
`1 = sₙ(id) ≤ ‖B‖ · sₙ(D_σ) · ‖A‖ ≤ ‖σ_n‖⁻¹ · sₙ(D_σ)`, i.e. `‖σ_n‖ ≤ sₙ(D_σ)`.
This needs (S5'), so it holds for every **strict** s-number sequence — the
approximation, Bernstein, Gelfand, and Kolmogorov numbers. -/

/-- **Lower bound.** For every *strict* s-number sequence `s` and a diagonal
non-increasing in modulus, `‖σ_n‖ ≤ sₙ(D_σ)` (`n < m`). -/
theorem le_sn_DiagCLM {s : Family 𝕜} (hs : IsStrictSNumberSequence s)
    {σ : Fin m → 𝕜} (hσ : _root_.Antitone fun i => ‖σ i‖) {n : ℕ} (hn : n < m) :
    ‖σ ⟨n, hn⟩‖ ≤ s (DiagCLM p σ) n := by
  rcases eq_or_ne ‖σ ⟨n, hn⟩‖ 0 with h0 | h0
  · rw [h0]; exact hs.nonneg _ _
  have hpos : 0 < ‖σ ⟨n, hn⟩‖ := (norm_nonneg _).lt_of_ne (Ne.symm h0)
  have hnm : n + 1 ≤ m := hn
  haveI : Nonempty (Fin (n + 1)) := ⟨⟨0, Nat.succ_pos n⟩⟩
  -- The top `n+1` entries dominate `‖σ_n‖`, hence are nonzero.
  have hdom : ∀ j : Fin (n + 1), ‖σ ⟨n, hn⟩‖ ≤ ‖σ (Fin.castLE hnm j)‖ := by
    intro j
    refine hσ ?_
    simp only [Fin.le_def, Fin.val_castLE]
    omega
  have hne : ∀ j : Fin (n + 1), σ (Fin.castLE hnm j) ≠ 0 := fun j hj => by
    have := hdom j; rw [hj, norm_zero] at this; exact absurd this (not_le.mpr hpos)
  -- The factorisation `id = B ∘ D_σ ∘ A`.
  set A : PiLp p (fun _ : Fin (n + 1) => 𝕜) →L[𝕜] PiLp p (fun _ : Fin m => 𝕜) :=
    padFin with hA
  set B : PiLp p (fun _ : Fin m => 𝕜) →L[𝕜] PiLp p (fun _ : Fin (n + 1) => 𝕜) :=
    (DiagCLM p fun j => (σ (Fin.castLE hnm j))⁻¹).comp (projFin hnm) with hB
  have hfact : B.comp ((DiagCLM p σ).comp A)
      = ContinuousLinearMap.id 𝕜 (PiLp p (fun _ : Fin (n + 1) => 𝕜)) := by
    ext w j
    simp only [hB, hA, ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
      DiagCLM_apply, projFin_apply]
    rw [padFin_castLE, smul_smul, inv_mul_cancel₀ (hne j), one_smul]
  -- Norm bounds on the factors.
  have hAle : ‖A‖ ≤ 1 := by rw [hA]; exact norm_padFin_clm_le hnm
  have hBle : ‖B‖ ≤ ‖σ ⟨n, hn⟩‖⁻¹ := by
    rw [hB]
    calc ‖(DiagCLM p fun j => (σ (Fin.castLE hnm j))⁻¹).comp (projFin hnm)‖
        ≤ ‖DiagCLM p fun j => (σ (Fin.castLE hnm j))⁻¹‖ * ‖projFin hnm‖ :=
          ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ (⨆ j, ‖(σ (Fin.castLE hnm j))⁻¹‖) * 1 := by
          rw [norm_DiagCLM]
          exact mul_le_mul_of_nonneg_left (norm_projFin_clm_le hnm)
            (Real.iSup_nonneg fun j => norm_nonneg _)
      _ = ⨆ j, ‖(σ (Fin.castLE hnm j))⁻¹‖ := mul_one _
      _ ≤ ‖σ ⟨n, hn⟩‖⁻¹ := by
          refine ciSup_le fun j => ?_
          rw [norm_inv]
          exact inv_anti₀ hpos (hdom j)
  -- Assemble via (S3) and (S5').
  have hideal := hs.ideal A (DiagCLM p σ) B n
  rw [hfact, hs.strictly_normalised_at_id n (by rw [finrank_piLp]; omega)] at hideal
  have hsnn : 0 ≤ s (DiagCLM p σ) n := hs.nonneg _ _
  have hchain : (1 : ℝ) ≤ ‖σ ⟨n, hn⟩‖⁻¹ * s (DiagCLM p σ) n := by
    calc (1 : ℝ) ≤ ‖B‖ * s (DiagCLM p σ) n * ‖A‖ := hideal
      _ ≤ ‖σ ⟨n, hn⟩‖⁻¹ * s (DiagCLM p σ) n * 1 :=
          mul_le_mul (mul_le_mul_of_nonneg_right hBle hsnn) hAle (norm_nonneg _)
            (mul_nonneg (inv_nonneg.mpr (norm_nonneg _)) hsnn)
      _ = ‖σ ⟨n, hn⟩‖⁻¹ * s (DiagCLM p σ) n := mul_one _
  have hfinal := mul_le_mul_of_nonneg_left hchain (norm_nonneg (σ ⟨n, hn⟩))
  rwa [mul_one, ← mul_assoc, mul_inv_cancel₀ (ne_of_gt hpos), one_mul] at hfinal

/-! ## Stage 4 — the s-numbers of a diagonal operator

Combining the upper bound (Stage 2, valid for every s-number) with the lower
bound (Stage 3, valid for every *strict* s-number) gives the exact value
`sₙ(D_σ) = ‖σ_n‖` for every strict s-number sequence, hence simultaneously for
the approximation, Gelfand, Kolmogorov, and Bernstein numbers. The Hilbert
numbers, only known to satisfy (S5) (not (S5')), are merely bounded above; for
`p ≠ 2` the inequality `hₙ(D_σ) ≤ ‖σ_n‖` is strict in general. -/

/-- **Main result.** For every *strict* s-number sequence `s` and a diagonal
operator `D_σ : ℓ^p_m → ℓ^p_m` whose entries are non-increasing in modulus,
`sₙ(D_σ) = ‖σ_n‖` (the `(n+1)`-th largest entry), for `n < m`. -/
theorem sn_DiagCLM_eq {s : Family 𝕜} (hs : IsStrictSNumberSequence s)
    {σ : Fin m → 𝕜} (hσ : _root_.Antitone fun i => ‖σ i‖) {n : ℕ} (hn : n < m) :
    s (DiagCLM p σ) n = ‖σ ⟨n, hn⟩‖ :=
  le_antisymm
    ((sn_le_approximationNumber hs.toIsSNumberSequence (DiagCLM p σ) n).trans
      (approximationNumber_DiagCLM_le hσ hn))
    (le_sn_DiagCLM hs hσ hn)

/-- The approximation numbers of a diagonal operator: `aₙ(D_σ) = ‖σ_n‖`. -/
theorem approximationNumber_DiagCLM_eq {σ : Fin m → 𝕜}
    (hσ : _root_.Antitone fun i => ‖σ i‖) {n : ℕ} (hn : n < m) :
    approximationNumber (DiagCLM p σ) n = ‖σ ⟨n, hn⟩‖ :=
  le_antisymm (approximationNumber_DiagCLM_le hσ hn)
    (le_sn_DiagCLM isStrictSNumberSequence_approximationNumber hσ hn)

/-- The Gelfand numbers of a diagonal operator: `cₙ(D_σ) = ‖σ_n‖`. -/
theorem gelfandNumber_DiagCLM_eq {σ : Fin m → 𝕜}
    (hσ : _root_.Antitone fun i => ‖σ i‖) {n : ℕ} (hn : n < m) :
    gelfandNumber (DiagCLM p σ) n = ‖σ ⟨n, hn⟩‖ :=
  sn_DiagCLM_eq isStrictSNumberSequence_gelfandNumber hσ hn

/-- The Kolmogorov numbers of a diagonal operator: `dₙ(D_σ) = ‖σ_n‖`. -/
theorem kolmogorovNumber_DiagCLM_eq {σ : Fin m → 𝕜}
    (hσ : _root_.Antitone fun i => ‖σ i‖) {n : ℕ} (hn : n < m) :
    kolmogorovNumber (DiagCLM p σ) n = ‖σ ⟨n, hn⟩‖ :=
  sn_DiagCLM_eq isStrictSNumberSequence_kolmogorovNumber hσ hn

/-- The Bernstein numbers of a diagonal operator: `bₙ(D_σ) = ‖σ_n‖`. -/
theorem bernsteinNumber_DiagCLM_eq {σ : Fin m → 𝕜}
    (hσ : _root_.Antitone fun i => ‖σ i‖) {n : ℕ} (hn : n < m) :
    bernsteinNumber (DiagCLM p σ) n = ‖σ ⟨n, hn⟩‖ :=
  sn_DiagCLM_eq isStrictSNumberSequence_bernsteinNumber hσ hn

/-- The Hilbert numbers of a diagonal operator satisfy `hₙ(D_σ) ≤ ‖σ_n‖`. Unlike
the strict s-numbers above, equality can fail for `p ≠ 2`: the Hilbert numbers
measure the Hilbertian part of `ℓ^p`, which is genuinely smaller. -/
theorem hilbertNumber_DiagCLM_le {σ : Fin m → 𝕜}
    (hσ : _root_.Antitone fun i => ‖σ i‖) {n : ℕ} (hn : n < m) :
    hilbertNumber (DiagCLM p σ) n ≤ ‖σ ⟨n, hn⟩‖ :=
  (sn_le_approximationNumber isSNumberSequence_hilbertNumber (DiagCLM p σ) n).trans
    (approximationNumber_DiagCLM_le hσ hn)

/-! ## The unit diagonal (identity operator)

The simplest case `σ ≡ 1` is the identity `id : ℓ^p_m → ℓ^p_m`. Here no norm
machinery is needed: `sₙ(id) = 1` for `n < m` is exactly the strict
normalisation (S5'), and `sₙ(id) = 0` for `n ≥ m` is the rank axiom (S4). -/

/-- The unit diagonal is the identity operator. -/
@[simp] lemma DiagCLM_one :
    DiagCLM p (fun _ : Fin m => (1 : 𝕜)) = ContinuousLinearMap.id 𝕜 (PiLp p (fun _ : Fin m => 𝕜)) := by
  ext x i; simp

/-- For every strict s-number sequence, the identity on `ℓ^p_m` has `sₙ(id) = 1`
whenever `n < m` (directly from (S5'), via `dim ℓ^p_m = m`). -/
theorem sn_id_piLp {s : Family 𝕜} (hs : IsStrictSNumberSequence s) {n : ℕ} (hn : n < m) :
    s (ContinuousLinearMap.id 𝕜 (PiLp p (fun _ : Fin m => 𝕜))) n = 1 :=
  hs.strictly_normalised_at_id n (by rw [finrank_piLp]; exact hn)

end SNumbers
