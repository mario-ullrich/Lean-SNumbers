/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
import SNumbers.Helpers
import Mathlib.Analysis.Normed.Module.RieszLemma
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Kolmogorov numbers `d_n`

`d_n S = inf_{V ⊆ Y, dim V ≤ n} sup_{x ∈ B_X} d(S x, V)`,

i.e. the smallest worst-case error one can achieve by approximating the image
of the unit ball of `X` under `S` by a subspace `V ⊆ Y` of dimension at most
`n`.
-/

universe u

open scoped Cardinal
open ContinuousLinearMap

namespace SNumbers

-- Kolmogorov numbers require `DenselyNormedField` (rather than just
-- `NontriviallyNormedField`) so that `‖S‖ = sSup {‖S x‖ : ‖x‖ ≤ 1}` holds —
-- needed for axiom (S1) `s 0 S = ‖S‖`. Both `ℝ` and `ℂ` are `DenselyNormedField`,
-- so this matches the practical scope of Pietsch's framework.
variable {𝕜 : Type u} [DenselyNormedField 𝕜]
variable {X Y : Type u}
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]

/-- The deviation of `S` from a subspace `V ⊆ Y`:

`sup_{x ∈ B_X} inf_{y ∈ V} ‖S x - y‖`. -/
noncomputable def deviationFromSubspace (S : X →L[𝕜] Y) (V : Submodule 𝕜 Y) : ℝ :=
  sSup {r | ∃ x : X, ‖x‖ ≤ 1 ∧ r = sInf {s | ∃ y ∈ V, s = ‖S x - y‖}}

/-- The `n`-th **Kolmogorov number** of a continuous linear map.

`d_n S = inf_{V ⊆ Y, dim V ≤ n} deviationFromSubspace S V`. -/
noncomputable def kolmogorovNumber (S : X →L[𝕜] Y) (n : ℕ) : ℝ :=
  sInf {r | ∃ V : Submodule 𝕜 Y,
      Module.rank 𝕜 V ≤ (n : Cardinal) ∧ r = deviationFromSubspace S V}

/-! ### Helpers for the inner distance set `{‖S x - y‖ | y ∈ V}` -/

private lemma innerSet_nonempty (S : X →L[𝕜] Y) (V : Submodule 𝕜 Y) (x : X) :
    {s | ∃ y ∈ V, s = ‖S x - y‖}.Nonempty :=
  ⟨‖S x‖, 0, V.zero_mem, by simp⟩

private lemma innerSet_bddBelow (S : X →L[𝕜] Y) (V : Submodule 𝕜 Y) (x : X) :
    BddBelow {s | ∃ y ∈ V, s = ‖S x - y‖} :=
  ⟨0, by rintro _ ⟨y, _, rfl⟩; exact norm_nonneg _⟩

/-- `inf_{y ∈ V} ‖S x - y‖ ≥ 0`. -/
private lemma innerInf_nonneg (S : X →L[𝕜] Y) (V : Submodule 𝕜 Y) (x : X) :
    0 ≤ sInf {s | ∃ y ∈ V, s = ‖S x - y‖} :=
  Real.sInf_nonneg fun _ ⟨_, _, h⟩ => h.symm ▸ norm_nonneg _

/-- `inf_{y ∈ V} ‖S x - y‖ ≤ ‖S x‖` (taking `y = 0 ∈ V`). -/
private lemma innerInf_le_norm_apply (S : X →L[𝕜] Y) (V : Submodule 𝕜 Y) (x : X) :
    sInf {s | ∃ y ∈ V, s = ‖S x - y‖} ≤ ‖S x‖ :=
  csInf_le (innerSet_bddBelow S V x) ⟨0, V.zero_mem, by simp⟩

/-- If `S x ∈ V`, then `inf_{y ∈ V} ‖S x - y‖ = 0`. -/
private lemma innerInf_eq_zero_of_mem (S : X →L[𝕜] Y) (V : Submodule 𝕜 Y) (x : X)
    (hx : (S x) ∈ V) : sInf {s | ∃ y ∈ V, s = ‖S x - y‖} = 0 := by
  refine le_antisymm ?_ (innerInf_nonneg S V x)
  have h_zero_mem : (0 : ℝ) ∈ {s | ∃ y ∈ V, s = ‖S x - y‖} :=
    ⟨S x, hx, by rw [sub_self, norm_zero]⟩
  exact csInf_le (innerSet_bddBelow S V x) h_zero_mem

/-! ### Helpers for the deviation (outer `sSup`) -/

private lemma deviationSet_nonempty (S : X →L[𝕜] Y) (V : Submodule 𝕜 Y) :
    {r | ∃ x : X, ‖x‖ ≤ 1 ∧
        r = sInf {s | ∃ y ∈ V, s = ‖S x - y‖}}.Nonempty :=
  ⟨_, 0, by simp, rfl⟩

private lemma deviationSet_bddAbove (S : X →L[𝕜] Y) (V : Submodule 𝕜 Y) :
    BddAbove {r | ∃ x : X, ‖x‖ ≤ 1 ∧
        r = sInf {s | ∃ y ∈ V, s = ‖S x - y‖}} := by
  refine ⟨‖S‖, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  calc sInf _
      ≤ ‖S x‖ := innerInf_le_norm_apply S V x
    _ ≤ ‖S‖ * ‖x‖ := S.le_opNorm x
    _ ≤ ‖S‖ * 1 := mul_le_mul_of_nonneg_left hx (norm_nonneg _)
    _ = ‖S‖ := mul_one _

/-- `0 ≤ deviationFromSubspace S V`. -/
lemma deviationFromSubspace_nonneg (S : X →L[𝕜] Y) (V : Submodule 𝕜 Y) :
    0 ≤ deviationFromSubspace S V := by
  refine le_csSup (deviationSet_bddAbove S V) ⟨0, by simp, ?_⟩
  exact (innerInf_eq_zero_of_mem S V 0 (by simp)).symm

/-- `deviationFromSubspace S V ≤ ‖S‖`. -/
lemma deviationFromSubspace_le_norm (S : X →L[𝕜] Y) (V : Submodule 𝕜 Y) :
    deviationFromSubspace S V ≤ ‖S‖ :=
  csSup_le (deviationSet_nonempty S V) <| by
    rintro _ ⟨x, hx, rfl⟩
    calc sInf _
        ≤ ‖S x‖ := innerInf_le_norm_apply S V x
      _ ≤ ‖S‖ * ‖x‖ := S.le_opNorm x
      _ ≤ ‖S‖ * 1 := mul_le_mul_of_nonneg_left hx (norm_nonneg _)
      _ = ‖S‖ := mul_one _

/-! ### `kolmogorovNumber` against an admissible subspace -/

/-- An admissible subspace gives an upper bound for `kolmogorovNumber`.
The set on which we take `sInf` is bounded below by `0` because every
`deviationFromSubspace` value is ≥ 0 (`deviationFromSubspace_nonneg`). -/
lemma kolmogorovNumber_le_deviation {S : X →L[𝕜] Y} {n : ℕ} {V : Submodule 𝕜 Y}
    (hV : Module.rank 𝕜 V ≤ (n : Cardinal)) :
    kolmogorovNumber S n ≤ deviationFromSubspace S V :=
  csInf_le ⟨0, by rintro _ ⟨W, _, rfl⟩; exact deviationFromSubspace_nonneg S W⟩
    ⟨V, hV, rfl⟩

/-! ### (S1) Non-negativity -/

lemma kolmogorovNumber_nonneg (S : X →L[𝕜] Y) (n : ℕ) :
    0 ≤ kolmogorovNumber S n :=
  Real.sInf_nonneg <| by
    rintro _ ⟨V, _, rfl⟩; exact deviationFromSubspace_nonneg S V

/-! ### (S1) Antitone in `n` -/

lemma kolmogorovNumber_antitone (S : X →L[𝕜] Y) (n : ℕ) :
    kolmogorovNumber S (n + 1) ≤ kolmogorovNumber S n := by
  -- Every subspace of rank ≤ n is also of rank ≤ n+1, so the set we infimise
  -- over for `n+1` includes the one for `n`; hence its `sInf` is no larger.
  refine csInf_le_csInf
    ⟨0, by rintro _ ⟨W, _, rfl⟩; exact deviationFromSubspace_nonneg S W⟩
    ⟨_, ⊥, by rw [rank_bot]; exact bot_le, rfl⟩ ?_
  rintro _ ⟨V, hV, rfl⟩
  exact ⟨V, hV.trans (by exact_mod_cast Nat.le_succ n), rfl⟩

/-! ### (S4) Vanishing on low-rank operators -/

lemma kolmogorovNumber_eq_zero_of_rank_le {S : X →L[𝕜] Y} {n : ℕ}
    (hS : S.rank ≤ (n : Cardinal)) :
    kolmogorovNumber S n = 0 := by
  refine le_antisymm ?_ (kolmogorovNumber_nonneg S n)
  -- Take V = range S; every S x lies in V, so deviation(S, V) = 0.
  have hV_rank : Module.rank 𝕜 (LinearMap.range (S : X →ₗ[𝕜] Y)) ≤ (n : Cardinal) := hS
  refine (kolmogorovNumber_le_deviation hV_rank).trans ?_
  -- Show deviation(S, range S) ≤ 0; combined with nonneg, equals 0.
  refine csSup_le (deviationSet_nonempty S _) ?_
  rintro _ ⟨x, _, rfl⟩
  exact (innerInf_eq_zero_of_mem S _ x (LinearMap.mem_range_self _ x)).le

/-! ### (S1) `kolmogorovNumber S 0 = ‖S‖` -/

/-- The deviation from `⊥` equals the operator norm. -/
private lemma deviationFromSubspace_bot (S : X →L[𝕜] Y) :
    deviationFromSubspace S ⊥ = ‖S‖ := by
  -- For `V = ⊥` only `y = 0` is in `V`, so `inf_y ‖S x − y‖ = ‖S x‖`. The
  -- deviation set is therefore `(fun x ↦ ‖S x‖) '' closedBall 0 1`, whose
  -- `sSup` is `‖S‖` by the standard sup characterisation of the operator norm.
  have h_inner : ∀ x : X, sInf {s | ∃ y ∈ (⊥ : Submodule 𝕜 Y), s = ‖S x - y‖} = ‖S x‖ := by
    intro x
    have h_singleton : {s | ∃ y ∈ (⊥ : Submodule 𝕜 Y), s = ‖S x - y‖} = {‖S x‖} := by
      ext s
      simp only [Submodule.mem_bot, Set.mem_setOf_eq, Set.mem_singleton_iff,
        exists_eq_left, sub_zero]
    rw [h_singleton, csInf_singleton]
  have h_set_eq :
      {r | ∃ x : X, ‖x‖ ≤ 1 ∧ r = sInf {s | ∃ y ∈ (⊥ : Submodule 𝕜 Y), s = ‖S x - y‖}}
        = (fun x => ‖S x‖) '' Metric.closedBall 0 1 := by
    ext r
    simp only [Set.mem_setOf_eq, Set.mem_image, Metric.mem_closedBall, dist_zero_right]
    constructor
    · rintro ⟨x, hx, rfl⟩; exact ⟨x, hx, (h_inner x).symm⟩
    · rintro ⟨x, hx, rfl⟩; exact ⟨x, hx, (h_inner x).symm⟩
  unfold deviationFromSubspace
  rw [h_set_eq, ContinuousLinearMap.sSup_unitClosedBall_eq_norm]

lemma kolmogorovNumber_zero_eq_norm (S : X →L[𝕜] Y) :
    kolmogorovNumber S 0 = ‖S‖ := by
  -- For n = 0, only V = ⊥ satisfies dim V ≤ 0; so the kolmogorov set is the singleton `{‖S‖}`.
  refine le_antisymm ?_ ?_
  · -- ≤: take V = ⊥
    have h_rank : Module.rank 𝕜 (⊥ : Submodule 𝕜 Y) ≤ ((0 : ℕ) : Cardinal) := by
      rw [rank_bot]; exact_mod_cast Nat.zero_le 0
    exact (kolmogorovNumber_le_deviation h_rank).trans_eq (deviationFromSubspace_bot S)
  · -- ≥: every admissible V satisfies V = ⊥, so deviation(S, V) = ‖S‖.
    refine le_csInf ⟨_, ⊥, by rw [rank_bot]; exact bot_le, rfl⟩ ?_
    rintro _ ⟨V, hV, rfl⟩
    have hV_bot : V = ⊥ := by
      rw [← Submodule.rank_eq_zero]
      exact le_antisymm (by exact_mod_cast hV) (Cardinal.zero_le _)
    rw [hV_bot, deviationFromSubspace_bot]

/-! ### (S2) Subadditivity -/

/-- Per-subspace (S2) bound: `deviation(S + T, V) ≤ deviation(S, V) + ‖T‖`.

Pointwise triangle inequality: for any unit-ball `x` and any `y ∈ V`,
`‖(S+T) x − y‖ ≤ ‖S x − y‖ + ‖T x‖ ≤ ‖S x − y‖ + ‖T‖`. Taking the
infimum over `y` and the supremum over `x` yields the claim. -/
lemma deviationFromSubspace_add_le (S T : X →L[𝕜] Y) (V : Submodule 𝕜 Y) :
    deviationFromSubspace (S + T) V ≤ deviationFromSubspace S V + ‖T‖ := by
  -- The deviation on the LHS is a `sSup`. To bound it from above, we show
  -- every element of the underlying set is bounded by the RHS.
  refine csSup_le (deviationSet_nonempty (S + T) V) ?_
  rintro _ ⟨x, hx, rfl⟩
  -- We are now bounding the inner infimum at `x`, for `‖x‖ ≤ 1`.
  -- First, `‖T x‖ ≤ ‖T‖` because `x` lies in the unit ball.
  have h_Tx : ‖T x‖ ≤ ‖T‖ :=
    (T.le_opNorm x).trans <| by
      rw [mul_comm]; exact mul_le_of_le_one_left (norm_nonneg _) hx
  -- The triangle inequality at the level of inner infima:
  --   inf_{y ∈ V} ‖(S+T) x − y‖ ≤ inf_{y ∈ V} ‖S x − y‖ + ‖T x‖.
  -- This rests on the pointwise triangle inequality
  --   ‖(S+T) x − y‖ ≤ ‖S x − y‖ + ‖T x‖
  -- (since `(S+T) x − y = (S x − y) + T x`), then taking the infimum over `y`.
  have h_inner :
      sInf {s | ∃ y ∈ V, s = ‖(S + T) x - y‖} ≤
        sInf {s | ∃ y ∈ V, s = ‖S x - y‖} + ‖T x‖ := by
    -- Equivalent goal: `inf_{(S+T) x} − ‖T x‖ ≤ inf_{S x}`.
    rw [← sub_le_iff_le_add]
    refine le_csInf (innerSet_nonempty S V x) ?_
    rintro _ ⟨y, hy, rfl⟩
    -- For this fixed `y ∈ V`:
    have h_norm : ‖(S + T) x - y‖ ≤ ‖S x - y‖ + ‖T x‖ := by
      have heq : (S + T) x - y = (S x - y) + T x := by simp only [add_apply]; abel
      rw [heq]; exact norm_add_le _ _
    -- The same `y` is a witness in the `(S+T) x` inner set:
    have h_lo : sInf {s | ∃ y' ∈ V, s = ‖(S + T) x - y'‖} ≤ ‖(S + T) x - y‖ :=
      csInf_le (innerSet_bddBelow (S + T) V x) ⟨y, hy, rfl⟩
    linarith
  -- Bound the inner inf at `S x` by the deviation `deviation(S, V)`, since
  -- `x` is in the unit ball and the deviation is the sup over such `x`.
  have h_dev_S : sInf {s | ∃ y ∈ V, s = ‖S x - y‖} ≤ deviationFromSubspace S V :=
    le_csSup (deviationSet_bddAbove S V) ⟨x, hx, rfl⟩
  -- Combine: inner inf at `(S+T) x` ≤ inner inf at `S x` + ‖T x‖
  --       ≤ deviation(S, V) + ‖T‖.
  linarith

lemma kolmogorovNumber_add_le (S T : X →L[𝕜] Y) (n : ℕ) :
    kolmogorovNumber (S + T) n ≤ kolmogorovNumber S n + ‖T‖ := by
  -- Triangle-inequality proof, one step at a time.
  --
  -- Goal: `d_n(S+T) ≤ d_n(S) + ‖T‖`.
  -- Equivalently: `d_n(S+T) − ‖T‖ ≤ d_n(S)`.
  rw [← sub_le_iff_le_add]
  -- `d_n(S)` is the infimum over admissible `V`. To bound it from below,
  -- we show `d_n(S+T) − ‖T‖` is a lower bound on every value in the set.
  refine le_csInf ⟨_, ⊥, by rw [rank_bot]; exact bot_le, rfl⟩ ?_
  rintro _ ⟨V, hV, rfl⟩
  -- Now the goal is: `d_n(S+T) − ‖T‖ ≤ deviation(S, V)` for this specific `V`.
  -- We prove it from two steps:
  -- Step 1: `d_n(S+T) ≤ deviation(S+T, V)` because `V` is admissible at `n`.
  have h1 : kolmogorovNumber (S + T) n ≤ deviationFromSubspace (S + T) V :=
    kolmogorovNumber_le_deviation hV
  -- Step 2: `deviation(S+T, V) ≤ deviation(S, V) + ‖T‖` by the triangle
  -- inequality applied per `x`: `‖(S+T) x − y‖ ≤ ‖S x − y‖ + ‖T x‖`.
  have h2 : deviationFromSubspace (S + T) V ≤ deviationFromSubspace S V + ‖T‖ :=
    deviationFromSubspace_add_le S T V
  -- Chain `h1` and `h2`, rearrange to `d_n(S+T) − ‖T‖ ≤ deviation(S, V)`.
  linarith

/-! ### (S3) Ideal property

The proof uses `V' = B(V) ⊆ Z` (which has rank ≤ rank V ≤ n) as the
admissible subspace for `B ∘ S ∘ A`. The residual at `w ∈ B_W` is bounded by

  `‖B‖ · inf_{y ∈ V} ‖S(A w) - y‖`

via submultiplicativity of `B`. The remaining step — showing
`inf_{y ∈ V} ‖S(A w) - y‖ ≤ ‖A‖ · deviation(S, V)` — requires the scalar-field
density of `DenselyNormedField` to find `c ∈ 𝕜` with `‖c‖ ≈ 1/‖A‖`, scale
`A w` into the unit ball of `X`, and unwind via the homogeneity
`inf_y ‖S(c x) - y‖ = ‖c‖ · inf_y ‖S x - y‖` (using `c · V = V`). -/

variable {W Z : Type u}
variable [NormedAddCommGroup W] [NormedSpace 𝕜 W]
variable [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]

/-- Homogeneity of the inner infimum in `x`: scaling the argument by `c ≠ 0`
scales the infimum by `‖c‖`. Uses that `c • V = V` for a `𝕜`-subspace and
`c ≠ 0`. -/
private lemma innerInf_smul (S : X →L[𝕜] Y) (V : Submodule 𝕜 Y) (x : X)
    {c : 𝕜} (hc : c ≠ 0) :
    sInf {s | ∃ y ∈ V, s = ‖S (c • x) - y‖}
      = ‖c‖ * sInf {s | ∃ y ∈ V, s = ‖S x - y‖} := by
  -- Strategy: the distance set at `c • x` is the image of the distance set at
  -- `x` under `t ↦ ‖c‖ * t` (using the bijection `y ↔ c • y'` on `V`). Then
  -- `sInf` commutes with this scaling because `‖c‖ > 0`.
  have hc_pos : 0 < ‖c‖ := norm_pos_iff.mpr hc
  -- Name the two distance sets.
  set A := {s : ℝ | ∃ y ∈ V, s = ‖S (c • x) - y‖} with hA_def
  set B := {s : ℝ | ∃ y ∈ V, s = ‖S x - y‖} with hB_def
  -- Step 1: show `A = (fun t => ‖c‖ * t) '' B` by exhibiting the bijection
  -- `y ↔ c • y'` between `V` and `V` (which sends `‖S(c•x) - y‖` to `‖c‖·‖S x - y'‖`).
  have h_set_eq : A = (fun t : ℝ => ‖c‖ * t) '' B := by
    ext s
    simp only [hA_def, hB_def, Set.mem_setOf_eq, Set.mem_image]
    refine ⟨?_, ?_⟩
    · -- Forward: given `s = ‖S(c•x) - y‖` with `y ∈ V`, set `y' := c⁻¹ • y ∈ V`.
      rintro ⟨y, hy, rfl⟩
      have hy' : c⁻¹ • y ∈ V := V.smul_mem _ hy
      -- Algebraic identity: `S(c•x) - y = c • (S x - c⁻¹ • y)`.
      have h_smul : S (c • x) - y = c • (S x - c⁻¹ • y) := by
        have hcy : c • (c⁻¹ • y) = y := by
          rw [smul_smul, mul_inv_cancel₀ hc, one_smul]
        rw [smul_sub, ContinuousLinearMap.map_smul, hcy]
      -- Hence `‖S(c•x) - y‖ = ‖c‖ * ‖S x - c⁻¹ • y‖`.
      refine ⟨‖S x - c⁻¹ • y‖, ⟨c⁻¹ • y, hy', rfl⟩, ?_⟩
      rw [h_smul, norm_smul]
    · -- Reverse: given `s = ‖c‖ * ‖S x - y'‖` with `y' ∈ V`, take `y := c • y' ∈ V`.
      rintro ⟨t, ⟨y', hy', rfl⟩, rfl⟩
      have hcy' : c • y' ∈ V := V.smul_mem _ hy'
      -- Algebraic identity: `S(c•x) - c•y' = c • (S x - y')`.
      have h_smul : S (c • x) - c • y' = c • (S x - y') := by
        rw [ContinuousLinearMap.map_smul, smul_sub]
      refine ⟨c • y', hcy', ?_⟩
      rw [h_smul, norm_smul]
  -- Step 2: `sInf ((fun t => ‖c‖ * t) '' B) = ‖c‖ * sInf B`.
  rw [h_set_eq]
  have h_nonempty : B.Nonempty := innerSet_nonempty S V x
  have h_bdd : BddBelow B := innerSet_bddBelow S V x
  -- The image set is bounded below by 0 (each element is `‖c‖ · t` with `t ≥ 0`).
  have h_img_bdd : BddBelow ((fun t : ℝ => ‖c‖ * t) '' B) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨t, ht, rfl⟩
    have ht_nn : 0 ≤ t := by
      obtain ⟨y, _, rfl⟩ := ht
      exact norm_nonneg _
    exact mul_nonneg hc_pos.le ht_nn
  refine le_antisymm ?_ ?_
  · -- `sInf image ≤ ‖c‖ * sInf B`: divide both sides by `‖c‖ > 0`, then show
    -- `sInf image / ‖c‖ ≤ t` for every `t ∈ B`.
    rw [← div_le_iff₀' hc_pos]
    refine le_csInf h_nonempty ?_
    intro t ht
    -- For this `t ∈ B`, the value `‖c‖ * t` is in the image, so it dominates `sInf image`.
    have h_in_img : ‖c‖ * t ∈ (fun t : ℝ => ‖c‖ * t) '' B := ⟨t, ht, rfl⟩
    have h_inf_le : sInf ((fun t : ℝ => ‖c‖ * t) '' B) ≤ ‖c‖ * t :=
      csInf_le h_img_bdd h_in_img
    rw [div_le_iff₀' hc_pos]
    exact h_inf_le
  · -- `‖c‖ * sInf B ≤ sInf image`: each element of the image is `‖c‖ * t`
    -- with `t ≥ sInf B`, so `‖c‖ * sInf B ≤ ‖c‖ * t` (using `‖c‖ ≥ 0`).
    refine le_csInf (h_nonempty.image _) ?_
    rintro _ ⟨t, ht, rfl⟩
    have h_inf_le_t : sInf B ≤ t := csInf_le h_bdd ht
    exact mul_le_mul_of_nonneg_left h_inf_le_t hc_pos.le

/-- Key density step: for `‖w‖ ≤ 1`, the inner infimum at `S (A w)` is
bounded by `‖A‖ · deviationFromSubspace S V`. -/
private lemma innerInf_apply_le_norm_mul_deviation
    (A : W →L[𝕜] X) (S : X →L[𝕜] Y) (V : Submodule 𝕜 Y)
    {w : W} (hw : ‖w‖ ≤ 1) :
    sInf {s | ∃ y ∈ V, s = ‖S (A w) - y‖} ≤ ‖A‖ * deviationFromSubspace S V := by
  set α := sInf {s | ∃ y ∈ V, s = ‖S (A w) - y‖}
  set β := deviationFromSubspace S V with hβ
  by_cases hAw : A w = 0
  · -- Trivial case `A w = 0`: then `S(A w) = 0`, so `α ≤ ‖S(A w)‖ = 0 ≤ ‖A‖ · β`.
    have h_norm : ‖S (A w)‖ = 0 := by rw [hAw, map_zero, norm_zero]
    have h_alpha_le_0 : α ≤ 0 :=
      (innerInf_le_norm_apply S V (A w)).trans_eq h_norm
    have h_rhs_nonneg : 0 ≤ ‖A‖ * β :=
      mul_nonneg (norm_nonneg _) (deviationFromSubspace_nonneg _ _)
    exact h_alpha_le_0.trans h_rhs_nonneg
  · -- Main case `A w ≠ 0`. We use density of `‖𝕜‖` to scale `A w` into the
    -- unit ball of `X`, then apply homogeneity (`innerInf_smul`).
    have hAw_pos : 0 < ‖A w‖ := norm_pos_iff.mpr hAw
    have hα_nonneg : 0 ≤ α := innerInf_nonneg S V (A w)
    -- `‖A w‖ ≤ ‖A‖` since `‖w‖ ≤ 1`.
    have h_Aw_le : ‖A w‖ ≤ ‖A‖ :=
      (A.le_opNorm w).trans (by
        rw [mul_comm]; exact mul_le_of_le_one_left (norm_nonneg _) hw)
    -- Plan: for every `0 < ε < 1`, show `α * (1 - ε) ≤ ‖A‖ * β`. Then apply
    -- `le_of_mul_one_sub_le_of_nonneg` to conclude `α ≤ ‖A‖ * β`.
    have key : ∀ ε : ℝ, 0 < ε → ε < 1 →
        α * (1 - ε) ≤ ‖A‖ * β := by
      intro ε hε hε1
      -- Step 1: density of `‖𝕜‖` produces `c ∈ 𝕜` with
      -- `(1 - ε) / ‖A w‖ < ‖c‖ < 1 / ‖A w‖`.
      have hlt : (1 - ε) / ‖A w‖ < 1 / ‖A w‖ := by
        apply (div_lt_div_iff_of_pos_right hAw_pos).mpr
        linarith
      have h_lb_nn : 0 ≤ (1 - ε) / ‖A w‖ :=
        div_nonneg (by linarith) hAw_pos.le
      obtain ⟨c, hc_lb, hc_ub⟩ :=
        NormedField.exists_lt_norm_lt 𝕜 h_lb_nn hlt
      have hc_pos : 0 < ‖c‖ := lt_of_le_of_lt h_lb_nn hc_lb
      have hc_ne : c ≠ 0 := norm_pos_iff.mp hc_pos
      -- Step 2: `‖c • A w‖ < 1`, so `c • A w` lies in the closed unit ball of `X`.
      have h_cAw_lt_one : ‖c • A w‖ < 1 := by
        rw [norm_smul]
        have h_ub : ‖c‖ < 1 / ‖A w‖ := hc_ub
        have h_mul : ‖c‖ * ‖A w‖ < 1 / ‖A w‖ * ‖A w‖ :=
          mul_lt_mul_of_pos_right h_ub hAw_pos
        rwa [div_mul_cancel₀ _ hAw_pos.ne'] at h_mul
      -- Step 3: by homogeneity (`innerInf_smul`),
      -- `inf_y ‖S(c • A w) - y‖ = ‖c‖ * α`.
      have h_homogeneity :
          sInf {s | ∃ y ∈ V, s = ‖S (c • A w) - y‖} = ‖c‖ * α :=
        innerInf_smul S V (A w) hc_ne
      -- Step 4: `c • A w` is a witness for the deviation supremum, so
      -- `inf_y ‖S(c • A w) - y‖ ≤ β`.
      have h_inner_le_β :
          sInf {s | ∃ y ∈ V, s = ‖S (c • A w) - y‖} ≤ β :=
        le_csSup (deviationSet_bddAbove S V) ⟨c • A w, h_cAw_lt_one.le, rfl⟩
      -- Combining steps 3+4: `‖c‖ * α ≤ β`.
      have h_c_alpha_le_beta : ‖c‖ * α ≤ β := h_homogeneity ▸ h_inner_le_β
      -- Step 5: from `‖c‖ > (1 - ε) / ‖A w‖` and `α ≥ 0`,
      -- `((1 - ε) / ‖A w‖) * α ≤ ‖c‖ * α ≤ β`.
      have h_step1 : (1 - ε) / ‖A w‖ * α ≤ ‖c‖ * α :=
        mul_le_mul_of_nonneg_right hc_lb.le hα_nonneg
      have h_step2 : (1 - ε) / ‖A w‖ * α ≤ β := h_step1.trans h_c_alpha_le_beta
      -- Step 6: multiply both sides by `‖A w‖ > 0` and simplify.
      have h_step3 : (1 - ε) / ‖A w‖ * α * ‖A w‖ ≤ β * ‖A w‖ :=
        mul_le_mul_of_nonneg_right h_step2 hAw_pos.le
      have h_simplify : (1 - ε) / ‖A w‖ * α * ‖A w‖ = (1 - ε) * α := by
        field_simp
      rw [h_simplify] at h_step3
      -- Step 7: bound `β * ‖A w‖ ≤ β * ‖A‖`.
      have h_step4 : β * ‖A w‖ ≤ β * ‖A‖ :=
        mul_le_mul_of_nonneg_left h_Aw_le (deviationFromSubspace_nonneg _ _)
      -- Combine the chain: `(1 - ε) * α ≤ β * ‖A‖`, equivalent to the goal.
      have h_final : (1 - ε) * α ≤ β * ‖A‖ := h_step3.trans h_step4
      linarith
    -- Take `ε → 0` via the generic helper.
    exact le_of_mul_one_sub_le_of_nonneg hα_nonneg key

/-- Per-subspace (S3) bound: `deviation(B ∘ S ∘ A, B(V)) ≤ ‖B‖ * ‖A‖ * deviation(S, V)`. -/
private lemma deviationFromSubspace_comp_comp_map_le
    (A : W →L[𝕜] X) (S : X →L[𝕜] Y) (B : Y →L[𝕜] Z) (V : Submodule 𝕜 Y) :
    deviationFromSubspace (B.comp (S.comp A)) (V.map (B : Y →ₗ[𝕜] Z))
      ≤ ‖B‖ * ‖A‖ * deviationFromSubspace S V := by
  refine csSup_le (deviationSet_nonempty (B.comp (S.comp A)) _) ?_
  rintro _ ⟨w, hw, rfl⟩
  -- We bound the inner infimum at `w` against `B(V)` from above by chaining:
  --   inf_z ‖BSA w - z‖ ≤ ‖B‖ · inf_y ‖S(A w) - y‖ ≤ ‖B‖ · ‖A‖ · deviation(S, V).
  -- The second step is `innerInf_apply_le_norm_mul_deviation`. The first step
  -- comes from the per-`y` bound below: choosing `z = B y` for `y ∈ V`.
  --
  -- Step 1: for each `y ∈ V`, `B y` is a candidate `z` with the right bound.
  have h_per_y : ∀ y ∈ V,
      sInf {s | ∃ z ∈ V.map (B : Y →ₗ[𝕜] Z), s = ‖B.comp (S.comp A) w - z‖}
        ≤ ‖B‖ * ‖S (A w) - y‖ := by
    intro y hy
    -- The infimum is at most `‖BSA w - B y‖`.
    have h_witness :
        sInf {s | ∃ z ∈ V.map (B : Y →ₗ[𝕜] Z), s = ‖B.comp (S.comp A) w - z‖}
          ≤ ‖B.comp (S.comp A) w - B y‖ :=
      csInf_le (innerSet_bddBelow _ _ _) ⟨B y, ⟨y, hy, rfl⟩, rfl⟩
    -- Algebra: `BSA w - B y = B(S(A w) - y)`.
    have h_eq : B.comp (S.comp A) w - B y = B (S (A w) - y) := by
      simp [ContinuousLinearMap.coe_comp', map_sub]
    rw [h_eq] at h_witness
    -- Apply `‖B v‖ ≤ ‖B‖ · ‖v‖` to `v = S(A w) - y`.
    exact h_witness.trans (B.le_opNorm _)
  -- Step 2: take infimum over `y ∈ V` to get `inf_z ≤ ‖B‖ · inf_y`. We split
  -- on `‖B‖ = 0` (where the bound is trivial via `y = 0`) versus `‖B‖ > 0`
  -- (where we divide by `‖B‖` and use `le_csInf`).
  have h_B_inner :
      sInf {s | ∃ z ∈ V.map (B : Y →ₗ[𝕜] Z), s = ‖B.comp (S.comp A) w - z‖}
        ≤ ‖B‖ * sInf {s | ∃ y ∈ V, s = ‖S (A w) - y‖} := by
    by_cases hB0 : ‖B‖ = 0
    · -- When `‖B‖ = 0`: the RHS is 0. Apply `h_per_y` at `y = 0 ∈ V`,
      -- which shows the LHS is also `≤ ‖B‖ * ‖…‖ = 0`.
      rw [hB0, zero_mul]
      have h_app : sInf {s | ∃ z ∈ V.map (B : Y →ₗ[𝕜] Z), s = ‖B.comp (S.comp A) w - z‖}
          ≤ ‖B‖ * ‖S (A w) - 0‖ := h_per_y 0 V.zero_mem
      rw [hB0, zero_mul] at h_app
      exact h_app
    · -- When `‖B‖ > 0`: divide by `‖B‖` and use `le_csInf`.
      have hB_pos : 0 < ‖B‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hB0)
      rw [← div_le_iff₀' hB_pos]
      refine le_csInf (innerSet_nonempty S V (A w)) ?_
      rintro _ ⟨y, hy, rfl⟩
      rw [div_le_iff₀' hB_pos]
      exact h_per_y y hy
  -- Step 3: invoke the density lemma.
  have h_AS : sInf {s | ∃ y ∈ V, s = ‖S (A w) - y‖} ≤ ‖A‖ * deviationFromSubspace S V :=
    innerInf_apply_le_norm_mul_deviation A S V hw
  -- Step 4: chain the two bounds.
  have h_chain : ‖B‖ * sInf {s | ∃ y ∈ V, s = ‖S (A w) - y‖}
      ≤ ‖B‖ * (‖A‖ * deviationFromSubspace S V) :=
    mul_le_mul_of_nonneg_left h_AS (norm_nonneg _)
  have h_assoc : ‖B‖ * (‖A‖ * deviationFromSubspace S V)
      = ‖B‖ * ‖A‖ * deviationFromSubspace S V := by ring
  calc sInf {s | ∃ z ∈ V.map (B : Y →ₗ[𝕜] Z), s = ‖B.comp (S.comp A) w - z‖}
      ≤ ‖B‖ * sInf {s | ∃ y ∈ V, s = ‖S (A w) - y‖} := h_B_inner
    _ ≤ ‖B‖ * (‖A‖ * deviationFromSubspace S V) := h_chain
    _ = ‖B‖ * ‖A‖ * deviationFromSubspace S V := h_assoc

lemma kolmogorovNumber_comp_comp_le
    (A : W →L[𝕜] X) (S : X →L[𝕜] Y) (B : Y →L[𝕜] Z) (n : ℕ) :
    kolmogorovNumber (B.comp (S.comp A)) n ≤
      ‖B‖ * kolmogorovNumber S n * ‖A‖ := by
  -- For each `V` (rank ≤ n), `B(V)` has rank ≤ n and the per-V deviation
  -- bound gives `d_n(BSA) ≤ ‖B‖ * ‖A‖ * deviation(S, V)`. Take inf over `V`
  -- via `Real.sInf_smul_of_nonneg` (same trick as for the approximation
  -- numbers — multiplying a `sInf` by a non-negative scalar commutes).
  have hkey : ∀ V : Submodule 𝕜 Y, Module.rank 𝕜 V ≤ (n : Cardinal) →
      kolmogorovNumber (B.comp (S.comp A)) n ≤ ‖B‖ * ‖A‖ * deviationFromSubspace S V :=
    fun V hV =>
      (kolmogorovNumber_le_deviation ((rank_map_le _ _).trans hV)).trans
        (deviationFromSubspace_comp_comp_map_le A S B V)
  -- Pull `‖B‖ * ‖A‖` out of the infimum: `c * sInf X = sInf (c • X)` for
  -- `c ≥ 0`. So `‖B‖ * ‖A‖ * d_n(S) = sInf ((‖B‖ * ‖A‖) • {deviation(S,V)})`.
  -- Then `d_n(BSA)` is a lower bound for the scaled set, by `hkey`.
  have h_inf : kolmogorovNumber (B.comp (S.comp A)) n
                ≤ ‖B‖ * ‖A‖ * kolmogorovNumber S n := by
    show _ ≤ (‖B‖ * ‖A‖) • sInf
      {r | ∃ V : Submodule 𝕜 Y,
            Module.rank 𝕜 V ≤ (n : Cardinal) ∧ r = deviationFromSubspace S V}
    rw [← Real.sInf_smul_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))]
    have hne : {r | ∃ V : Submodule 𝕜 Y,
                  Module.rank 𝕜 V ≤ (n : Cardinal) ∧
                  r = deviationFromSubspace S V}.Nonempty :=
      ⟨_, ⊥, by rw [rank_bot]; exact bot_le, rfl⟩
    refine le_csInf (hne.image _) ?_
    rintro _ ⟨_, ⟨V, hV, rfl⟩, rfl⟩
    exact hkey V hV
  -- Final reorder `‖B‖ * ‖A‖ * d_n = ‖B‖ * d_n * ‖A‖` is just commutativity.
  exact h_inf.trans_eq (by ring)

/-! ### (S5') Strict normalisation `s n (id_X) = 1` whenever `dim X > n`

We prove the stronger statement directly via Riesz's lemma. The key idea:
* `≤ 1`: take `V = ⊥`. Then `deviation(id, ⊥) = ‖id‖ = 1` (since `X` is
  nontrivial, as `0 < dim X`).
* `≥ 1`: for any admissible `V` (with `dim V ≤ n < dim X`), `V` is a proper
  finite-dimensional, hence closed, subspace of `X`. Riesz's lemma gives,
  for any `r < 1`, an `x₀ ∉ V` with `r * ‖x₀‖ ≤ ‖x₀ - y‖` for all `y ∈ V`.
  Density of `‖𝕜‖` then lets us scale `x₀` into the closed unit ball with
  norm arbitrarily close to `1`, so the inner infimum at the scaled point
  is at least `r * (1 - δ)` for any `δ > 0`. Taking limits gives `≥ 1`.

The classical (S5) on `EuclideanSpace 𝕜 (Fin (n + 1))` is then a direct
specialisation, since `Module.finrank 𝕜 (EuclideanSpace 𝕜 (Fin (n + 1))) = n + 1`. -/

/-- (S5') Strict normalisation: `kolmogorovNumber (id_X) n = 1` whenever
`n < Module.finrank 𝕜 X`. -/
lemma kolmogorovNumber_strict {X : Type u} [NormedAddCommGroup X]
    [NormedSpace 𝕜 X] [CompleteSpace 𝕜] (n : ℕ) (h : n < Module.finrank 𝕜 X) :
    kolmogorovNumber (ContinuousLinearMap.id 𝕜 X) n = 1 := by
  -- `X` is finite-dimensional and nontrivial.
  have h_finrank_pos : 0 < Module.finrank 𝕜 X :=
    Nat.lt_of_le_of_lt (Nat.zero_le _) h
  haveI : FiniteDimensional 𝕜 X := .of_finrank_pos h_finrank_pos
  haveI : Nontrivial X := Module.nontrivial_of_finrank_pos h_finrank_pos
  -- ## Step A: `‖id‖ = 1`.
  have h_id_norm : ‖ContinuousLinearMap.id 𝕜 X‖ = 1 := norm_id
  set I := ContinuousLinearMap.id 𝕜 X with hI_def
  -- ## Upper bound: `kolmogorovNumber I n ≤ 1`.
  -- Take `V = ⊥`. Then `deviation(I, ⊥) = ‖I‖ = 1`.
  have h_le : kolmogorovNumber I n ≤ 1 := by
    have h_rank_bot : Module.rank 𝕜 (⊥ : Submodule 𝕜 X) ≤ (n : Cardinal) := by
      rw [rank_bot]; exact Cardinal.zero_le _
    calc kolmogorovNumber I n
        ≤ deviationFromSubspace I ⊥ := kolmogorovNumber_le_deviation h_rank_bot
      _ = ‖I‖ := deviationFromSubspace_bot _
      _ = 1 := h_id_norm
  -- ## Lower bound: `1 ≤ kolmogorovNumber I n`.
  -- It suffices to show `1 ≤ deviation(I, V)` for every admissible `V` (rank ≤ n).
  have h_dev_ge : ∀ V : Submodule 𝕜 X, Module.rank 𝕜 V ≤ (n : Cardinal) →
      1 ≤ deviationFromSubspace I V := by
    intro V hV
    -- `V` has finrank ≤ n < finrank X, so `V` is a proper subspace.
    have hV_finrank_le : Module.finrank 𝕜 V ≤ n := Module.finrank_le_of_rank_le hV
    have hV_finrank_lt : Module.finrank 𝕜 V < Module.finrank 𝕜 X :=
      lt_of_le_of_lt hV_finrank_le h
    have hV_ne_top : V ≠ ⊤ := by
      intro hV_top
      have h_eq : Module.finrank 𝕜 V = Module.finrank 𝕜 X := by
        rw [hV_top, finrank_top]
      exact (h_eq ▸ hV_finrank_lt).ne rfl
    -- `V` is closed (finite-dimensional in a complete space) and proper.
    have hV_closed : IsClosed (V : Set X) := V.closed_of_finiteDimensional
    have hV_exists : ∃ x : X, x ∉ V :=
      SetLike.exists_not_mem_of_ne_top V hV_ne_top
    -- We show `1 - ε ≤ deviation(I, V)` for every `0 < ε < 1`, then take `ε → 0`.
    have h_aux : ∀ ε : ℝ, 0 < ε → ε < 1 → 1 - ε ≤ deviationFromSubspace I V := by
      intro ε hε hε1
      -- ## Step B: pick `r := 1 - ε/2`, `δ := ε/2`, with `r·(1-δ) ≥ 1 - ε`.
      set r : ℝ := 1 - ε / 2 with hr_def
      set δ : ℝ := ε / 2 with hδ_def
      have hε2_pos : 0 < ε / 2 := by positivity
      have hr_pos : 0 < r := by simp [hr_def]; linarith
      have hr_lt1 : r < 1 := by simp [hr_def]; linarith
      have hδ_pos : 0 < δ := hε2_pos
      -- The key inequality: `r·(1-δ) = (1 - ε/2)² = 1 - ε + (ε/2)² ≥ 1 - ε`.
      have hr_mul_one_sub_δ : (1 - ε) ≤ r * (1 - δ) := by
        have h_expand : r * (1 - δ) = 1 - ε + (ε / 2) * (ε / 2) := by
          simp only [hr_def, hδ_def]; ring
        have h_sq_nn : 0 ≤ (ε / 2) * (ε / 2) := mul_nonneg hε2_pos.le hε2_pos.le
        rw [h_expand]; linarith
      -- ## Step C: Riesz's lemma at level `r` produces `x₀ ∉ V` with
      -- `r · ‖x₀‖ ≤ ‖x₀ - y‖` for every `y ∈ V`.
      obtain ⟨x₀, hx₀_ne, hx₀_dist⟩ :=
        riesz_lemma (𝕜 := 𝕜) (E := X) (F := V) hV_closed hV_exists hr_lt1
      have hx₀_ne_zero : x₀ ≠ 0 := fun h0 => hx₀_ne (h0 ▸ V.zero_mem)
      have hx₀_norm_pos : 0 < ‖x₀‖ := norm_pos_iff.mpr hx₀_ne_zero
      -- ## Step D: density of `‖𝕜‖` gives `c ∈ 𝕜` with
      -- `(1 - δ) / ‖x₀‖ < ‖c‖ < 1 / ‖x₀‖`. Then `‖c • x₀‖ < 1`.
      have h_lb_nn : 0 ≤ (1 - δ) / ‖x₀‖ :=
        div_nonneg (by linarith) hx₀_norm_pos.le
      have h_lt : (1 - δ) / ‖x₀‖ < 1 / ‖x₀‖ := by
        apply (div_lt_div_iff_of_pos_right hx₀_norm_pos).mpr
        linarith
      obtain ⟨c, hc_lb, hc_ub⟩ :=
        NormedField.exists_lt_norm_lt 𝕜 h_lb_nn h_lt
      have hc_norm_pos : 0 < ‖c‖ := lt_of_le_of_lt h_lb_nn hc_lb
      have hc_ne : c ≠ 0 := norm_pos_iff.mp hc_norm_pos
      have h_cx0_lt : ‖c • x₀‖ < 1 := by
        rw [norm_smul]
        have h_mul : ‖c‖ * ‖x₀‖ < 1 / ‖x₀‖ * ‖x₀‖ :=
          mul_lt_mul_of_pos_right hc_ub hx₀_norm_pos
        rwa [div_mul_cancel₀ _ hx₀_norm_pos.ne'] at h_mul
      -- ## Step E: chain inequalities through deviation.
      -- (E.1) Homogeneity at `c • x₀`:
      --       inf_y ‖I(c•x₀) - y‖ = ‖c‖ · inf_y ‖I x₀ - y‖.
      have h_homogeneity :
          sInf {s | ∃ y ∈ V, s = ‖I (c • x₀) - y‖}
            = ‖c‖ * sInf {s | ∃ y ∈ V, s = ‖I x₀ - y‖} :=
        innerInf_smul I V x₀ hc_ne
      -- (E.2) Riesz's bound on the inner inf at `x₀`:
      --       inf_y ‖I x₀ - y‖ ≥ r · ‖x₀‖.
      have h_riesz : r * ‖x₀‖ ≤ sInf {s | ∃ y ∈ V, s = ‖I x₀ - y‖} := by
        refine le_csInf (innerSet_nonempty I V x₀) ?_
        rintro _ ⟨y, hy, rfl⟩
        simpa [hI_def, ContinuousLinearMap.id_apply] using hx₀_dist y hy
      -- (E.3) `c • x₀ ∈ closedBall 0 1`, so the inner inf at `c • x₀` is
      --       bounded above by `deviation(I, V)`.
      have h_inner_le_dev :
          sInf {s | ∃ y ∈ V, s = ‖I (c • x₀) - y‖}
            ≤ deviationFromSubspace I V :=
        le_csSup (deviationSet_bddAbove I V) ⟨c • x₀, h_cx0_lt.le, rfl⟩
      -- (E.4) Combine (E.1)–(E.3): `‖c‖ · (r · ‖x₀‖) ≤ deviation(I, V)`.
      have h_step1 : ‖c‖ * (r * ‖x₀‖) ≤ ‖c‖ * sInf {s | ∃ y ∈ V, s = ‖I x₀ - y‖} :=
        mul_le_mul_of_nonneg_left h_riesz hc_norm_pos.le
      have h_step2 : ‖c‖ * sInf {s | ∃ y ∈ V, s = ‖I x₀ - y‖}
          = sInf {s | ∃ y ∈ V, s = ‖I (c • x₀) - y‖} := h_homogeneity.symm
      have h_chain : ‖c‖ * (r * ‖x₀‖) ≤ deviationFromSubspace I V :=
        (h_step1.trans_eq h_step2).trans h_inner_le_dev
      -- (E.5) Replace `‖c‖` by `(1 - δ) / ‖x₀‖` (from `hc_lb`), simplify the
      --       arithmetic to get `r · (1 - δ) ≤ deviation(I, V)`.
      have h_r_x0_nn : 0 ≤ r * ‖x₀‖ := mul_nonneg hr_pos.le hx₀_norm_pos.le
      have h_lb_step :
          (1 - δ) / ‖x₀‖ * (r * ‖x₀‖) ≤ ‖c‖ * (r * ‖x₀‖) :=
        mul_le_mul_of_nonneg_right hc_lb.le h_r_x0_nn
      have h_simplify : (1 - δ) / ‖x₀‖ * (r * ‖x₀‖) = r * (1 - δ) := by
        field_simp
      rw [h_simplify] at h_lb_step
      -- (E.6) Combine: `1 - ε ≤ r · (1 - δ) ≤ ‖c‖ · (r · ‖x₀‖) ≤ deviation(I, V)`.
      have h_combined : r * (1 - δ) ≤ deviationFromSubspace I V :=
        h_lb_step.trans h_chain
      linarith
    -- Take `ε → 0` via the generic helper, specialised to `α = 1`.
    refine le_of_mul_one_sub_le_of_nonneg (by norm_num) (fun ε hε hε1 => ?_)
    rw [one_mul]; exact h_aux ε hε hε1
  -- Combine: `kolmogorovNumber I n ≥ 1` since every admissible deviation is ≥ 1.
  have h_ge : 1 ≤ kolmogorovNumber I n := by
    refine le_csInf ⟨_, ⊥, by rw [rank_bot]; exact bot_le, rfl⟩ ?_
    rintro _ ⟨V, hV, rfl⟩
    exact h_dev_ge V hV
  exact le_antisymm h_le h_ge

/-- (S5) Normalisation on `id_{ℓ₂^{n+1}}`: a special case of (S5'). -/
lemma kolmogorovNumber_id_euclidean [CompleteSpace 𝕜] (n : ℕ) :
    kolmogorovNumber
      (ContinuousLinearMap.id 𝕜 (EuclideanSpace 𝕜 (Fin (n + 1)))) n = 1 := by
  -- `EuclideanSpace 𝕜 (Fin (n + 1))` is linearly equivalent to `Fin (n + 1) → 𝕜`,
  -- whose `finrank` is `n + 1` by `Module.finrank_pi`.
  have h_finrank : Module.finrank 𝕜 (EuclideanSpace 𝕜 (Fin (n + 1))) = n + 1 := by
    rw [(WithLp.linearEquiv 2 𝕜 (Fin (n + 1) → 𝕜)).finrank_eq, Module.finrank_pi 𝕜]
    exact Fintype.card_fin _
  have h : n < Module.finrank 𝕜 (EuclideanSpace 𝕜 (Fin (n + 1))) := by
    rw [h_finrank]; exact Nat.lt_succ_self n
  exact kolmogorovNumber_strict n h

/-! ### Summary: Kolmogorov numbers form an s-number sequence -/

/-- Kolmogorov numbers form an s-number sequence. -/
theorem isSNumberSequence_kolmogorovNumber [CompleteSpace 𝕜] :
    IsSNumberSequence (𝕜 := 𝕜)
        (fun {_X _Y} _ _ _ _ S n => kolmogorovNumber S n) where
  nonneg := fun S n => kolmogorovNumber_nonneg S n
  norm_at_zero := fun S => kolmogorovNumber_zero_eq_norm S
  antitone := fun S n => kolmogorovNumber_antitone S n
  subadditive := fun S T n => kolmogorovNumber_add_le S T n
  ideal := fun A S B n => kolmogorovNumber_comp_comp_le A S B n
  vanishes_on_low_rank := fun _ _ h => kolmogorovNumber_eq_zero_of_rank_le h
  normalised_at_id := fun n => kolmogorovNumber_id_euclidean n

/-- Kolmogorov numbers form a *strict* s-number sequence: in addition to (S1)–(S5)
they also satisfy (S5'), the strong normalisation `s n (id_X) = 1` for every
finite-dimensional `X` with `dim X > n`. -/
theorem isStrictSNumberSequence_kolmogorovNumber [CompleteSpace 𝕜] :
    IsStrictSNumberSequence (𝕜 := 𝕜)
        (fun {_X _Y} _ _ _ _ S n => kolmogorovNumber S n) where
  toIsSNumberSequence := isSNumberSequence_kolmogorovNumber
  strictly_normalised_at_id := fun n h => kolmogorovNumber_strict n h

end SNumbers
