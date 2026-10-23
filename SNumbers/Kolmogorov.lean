/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import SNumbers.ContinuousLinearMapRank
public import SNumbers.QuotientMapNorms
public import Mathlib.Analysis.Normed.Module.RieszLemma
public import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Kolmogorov numbers `d_n`

The Kolmogorov numbers `d_n S` of a continuous linear map `S : X →L[𝕜] Y`
between normed `𝕜`-vector spaces measure the worst-case error of
approximating the image `S(B_X)` by an `n`-dimensional subspace of `Y`.

The classical definition is

  `d_n S = inf_{V ⊆ Y, dim V ≤ n} sup_{x ∈ B_X} inf_{y ∈ V} ‖S x - y‖`,

which we recast in terms of operator norms on quotient spaces:

  `d_n S = inf_{V ⊆ Y, dim V ≤ n} ‖π_V ∘ S‖`,

where `π_V : Y →L[𝕜] (Y ⧸ V)` is the canonical quotient map. The inner
`inf_y ‖S x − y‖` is exactly the quotient norm `‖[S x]‖_{Y/V}`, and the
outer `sup_{‖x‖ ≤ 1}` is the operator norm of the composition.

The development requires `[NontriviallyNormedField 𝕜]` throughout, plus
`[CompleteSpace 𝕜]` for (S5') (Riesz needs finite-dim subspaces of a
complete-field normed space to be closed). It does **not** require
`[DenselyNormedField 𝕜]` (the quotient form `‖[y]‖_{Y/⊥} = ‖y‖` for
`V = ⊥` avoids the density-of-norm scaling) and **not**
`[CompleteSpace X]`, so the Kolmogorov numbers here are defined for every
normed space `X`.

## Alternative: Pietsch's lifting identity

The companion file `SNumbers.KolmogorovLifting` gives an alternative
development via Pietsch's identity `d_n S = a_n(S ∘ Q_X)`, where
`Q_X : ℓ¹(B_X) →L[𝕜] X` is the canonical summation surjection. That
development is shorter (many axioms become one-liners over `a_n`) but
requires `[CompleteSpace X]` because `Q_X` is an infinite series in `X`,
and is therefore restricted to **Banach spaces**. The two definitions
agree on Banach spaces.

## Main results

* `SNumbers.kolmogorovNumber_additive` : `d_{n+m}(S + T) ≤ d_n S + d_m T`, using the sum
  `V ⊔ U` of the two subspaces.
* `SNumbers.kolmogorovNumber_multiplicative` : `d_{n+m}(S ∘ T) ≤ d_n S * d_m T`, using
  `V ⊔ S(U)`.
* `SNumbers.kolmogorovNumber_add_le`, `SNumbers.kolmogorovNumber_comp_comp_le` : (S2) and
  (S3), as the cases with one index `0`.
* `SNumbers.isStrictSNumberSequence_kolmogorovNumber` : the Kolmogorov numbers form a
  strict s-number sequence; `additive_kolmogorovNumber` and
  `multiplicative_kolmogorovNumber` state additivity and multiplicativity for the family.
-/

@[expose] public section

universe u

open scoped Cardinal
open ContinuousLinearMap

namespace SNumbers

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]
variable {W X Y Z : Type u}
variable [NormedAddCommGroup W] [NormedSpace 𝕜 W]
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
variable [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]

/-! ### Definitions -/

/-- Quotient form of the deviation: `‖π_V ∘ S‖`, where `π_V` is the
quotient projection `Y →L[𝕜] Y ⧸ V`. -/
noncomputable def deviationFromSubspace (S : X →L[𝕜] Y) (V : Submodule 𝕜 Y) : ℝ :=
  ‖V.mkQL.comp S‖

/-- The set of admissible deviations at stage `n`: the numbers
`‖π_V ∘ S‖` for subspaces `V ⊆ Y` of dimension at most `n`. The `n`-th
Kolmogorov number is its infimum. -/
def kolmogorovSet (S : X →L[𝕜] Y) (n : ℕ) : Set ℝ :=
  {r | ∃ V : Submodule 𝕜 Y,
      Module.rank 𝕜 V ≤ (n : Cardinal) ∧ r = deviationFromSubspace S V}

/-- Quotient form of the `n`-th Kolmogorov number. -/
noncomputable def kolmogorovNumber (S : X →L[𝕜] Y) (n : ℕ) : ℝ :=
  sInf (kolmogorovSet S n)

lemma kolmogorovNumber_def (S : X →L[𝕜] Y) (n : ℕ) :
    kolmogorovNumber S n = sInf (kolmogorovSet S n) := rfl

/-! ### Basic facts about `deviationFromSubspace` -/

lemma deviationFromSubspace_nonneg (S : X →L[𝕜] Y) (V : Submodule 𝕜 Y) :
    0 ≤ deviationFromSubspace S V :=
  norm_nonneg (V.mkQL.comp S)

lemma deviationFromSubspace_le_norm (S : X →L[𝕜] Y) (V : Submodule 𝕜 Y) :
    deviationFromSubspace S V ≤ ‖S‖ := by
  unfold deviationFromSubspace
  calc ‖V.mkQL.comp S‖
      ≤ ‖V.mkQL‖ * ‖S‖ := opNorm_comp_le _ _
    _ ≤ 1 * ‖S‖ := mul_le_mul_of_nonneg_right V.norm_mkQL_le (norm_nonneg _)
    _ = ‖S‖ := one_mul _

/-! ### Basic facts about `kolmogorovSet` -/

/-- The set of admissible deviations is non-empty: the zero subspace `⊥` has
dimension `0 ≤ n`, so it is admissible at every stage. -/
lemma kolmogorovSet_nonempty (S : X →L[𝕜] Y) (n : ℕ) :
    (kolmogorovSet S n).Nonempty :=
  ⟨_, ⊥, by rw [rank_bot]; exact bot_le, rfl⟩

/-- The set of admissible deviations is bounded below by `0`. -/
lemma bddBelow_kolmogorovSet (S : X →L[𝕜] Y) (n : ℕ) :
    BddBelow (kolmogorovSet S n) :=
  ⟨0, by rintro _ ⟨V, _, rfl⟩; exact deviationFromSubspace_nonneg S V⟩

lemma kolmogorovNumber_le_deviation {S : X →L[𝕜] Y} {n : ℕ} {V : Submodule 𝕜 Y}
    (hV : Module.rank 𝕜 V ≤ (n : Cardinal)) :
    kolmogorovNumber S n ≤ deviationFromSubspace S V :=
  csInf_le (bddBelow_kolmogorovSet S n) ⟨V, hV, rfl⟩

/-- Lower bound for the Kolmogorov number: if `f` is a lower bound for the
quotient deviation over every admissible (dimension `≤ n`) subspace, then
`f ≤ d_n(S)`. Dual to `le_gelfandNumber`. -/
lemma le_kolmogorovNumber {S : X →L[𝕜] Y} {n : ℕ} {f : ℝ}
    (h : ∀ V : Submodule 𝕜 Y, Module.rank 𝕜 V ≤ (n : Cardinal) →
        f ≤ deviationFromSubspace S V) :
    f ≤ kolmogorovNumber S n :=
  le_csInf (kolmogorovSet_nonempty S n) <| by
    rintro _ ⟨V, hV, rfl⟩; exact h V hV

/-! ## (S1c) Non-negativity -/

lemma kolmogorovNumber_nonneg (S : X →L[𝕜] Y) (n : ℕ) :
    0 ≤ kolmogorovNumber S n :=
  Real.sInf_nonneg <| by
    rintro _ ⟨V, _, rfl⟩; exact deviationFromSubspace_nonneg S V

/-! ## (S1b) Antitone in `n` -/

/-- Raising `n` allows subspaces of larger dimension, hence more deviations
become admissible. -/
lemma kolmogorovSet_subset (S : X →L[𝕜] Y) {n m : ℕ} (h : n ≤ m) :
    kolmogorovSet S n ⊆ kolmogorovSet S m := by
  rintro _ ⟨V, hV, rfl⟩
  exact ⟨V, hV.trans (by exact_mod_cast h), rfl⟩

/-- If `n ≤ m`, then `d_m S ≤ d_n S`. -/
lemma kolmogorovNumber_antitone' (S : X →L[𝕜] Y) {n m : ℕ} (h : n ≤ m) :
    kolmogorovNumber S m ≤ kolmogorovNumber S n :=
  csInf_le_csInf (bddBelow_kolmogorovSet S m) (kolmogorovSet_nonempty S n)
    (kolmogorovSet_subset S h)

lemma kolmogorovNumber_antitone (S : X →L[𝕜] Y) (n : ℕ) :
    kolmogorovNumber S (n + 1) ≤ kolmogorovNumber S n :=
  kolmogorovNumber_antitone' S (Nat.le_succ n)

/-! ## (S1a) Value at `n = 0`: `kolmogorovNumber S 0 = ‖S‖`

The bound `‖V.mkQL ∘ S‖ ≤ ‖S‖` holds in general (since `‖V.mkQL‖ ≤ 1`),
but the matching lower bound `‖S‖ ≤ ‖(⊥).mkQL ∘ S‖` requires that
`Y ⧸ ⊥` is isometric to `Y`, i.e. `‖[y]‖ = ‖y‖` for the trivial
subspace. We get this from `Submodule.Quotient.norm_mk_lt`: a
representative `y'` of `[y]` with `‖y'‖ < ‖[y]‖ + ε` must satisfy
`y' - y ∈ ⊥`, i.e. `y' = y`. -/

/-- The quotient-norm bound `‖[y]‖ = ‖y‖` for the trivial submodule. -/
private lemma norm_mk_bot (y : Y) :
    ‖((⊥ : Submodule 𝕜 Y).mkQ y : Y ⧸ (⊥ : Submodule 𝕜 Y))‖ = ‖y‖ := by
  refine le_antisymm ?_ ?_
  · simpa using _root_.Submodule.Quotient.norm_mk_le (S := (⊥ : Submodule 𝕜 Y)) y
  · refine le_of_forall_pos_le_add fun ε hε => ?_
    obtain ⟨y', hy'_eq, hy'_lt⟩ :=
      Submodule.Quotient.norm_mk_lt
        ((⊥ : Submodule 𝕜 Y).mkQ y : Y ⧸ (⊥ : Submodule 𝕜 Y)) hε
    -- `Submodule.Quotient.mk y' = mkQ y` and `mkQ y' = mkQ y`, so `y' - y ∈ ⊥ = {0}`.
    have h_eq : y' = y := by
      have hker : y' - y ∈ (⊥ : Submodule 𝕜 Y) := by
        rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_sub, hy'_eq]
        change (⊥ : Submodule 𝕜 Y).mkQ y - (⊥ : Submodule 𝕜 Y).mkQ y = 0
        simp
      rwa [Submodule.mem_bot, sub_eq_zero] at hker
    have h_norm_eq : ‖y‖ = ‖y'‖ := by rw [h_eq]
    rw [h_norm_eq]
    exact hy'_lt.le

private lemma deviationFromSubspace_bot (S : X →L[𝕜] Y) :
    deviationFromSubspace S (⊥ : Submodule 𝕜 Y) = ‖S‖ := by
  unfold deviationFromSubspace
  refine le_antisymm ?_ ?_
  · -- `‖(⊥).mkQL ∘ S‖ ≤ ‖S‖`: pointwise `‖[S x]‖ = ‖S x‖ ≤ ‖S‖ * ‖x‖`.
    refine opNorm_le_bound _ (norm_nonneg _) fun x => ?_
    rw [coe_comp, Function.comp_apply, Submodule.mkQL_apply, norm_mk_bot]
    exact S.le_opNorm x
  · -- `‖S‖ ≤ ‖(⊥).mkQL ∘ S‖`: pointwise `‖S x‖ = ‖[S x]‖ ≤ ‖(⊥).mkQL ∘ S‖ * ‖x‖`.
    refine opNorm_le_bound _
      (norm_nonneg ((⊥ : Submodule 𝕜 Y).mkQL.comp S)) fun x => ?_
    rw [← norm_mk_bot (𝕜 := 𝕜) (S x)]
    change ‖((⊥ : Submodule 𝕜 Y).mkQL.comp S) x‖ ≤ _
    exact ((⊥ : Submodule 𝕜 Y).mkQL.comp S).le_opNorm x

lemma kolmogorovNumber_zero_eq_norm (S : X →L[𝕜] Y) :
    kolmogorovNumber S 0 = ‖S‖ := by
  refine le_antisymm ?_ ?_
  · have h_rank : Module.rank 𝕜 (⊥ : Submodule 𝕜 Y) ≤ ((0 : ℕ) : Cardinal) := by
      rw [rank_bot]; exact_mod_cast Nat.zero_le 0
    exact (kolmogorovNumber_le_deviation h_rank).trans_eq (deviationFromSubspace_bot S)
  · refine le_csInf (kolmogorovSet_nonempty S 0) ?_
    rintro _ ⟨V, hV, rfl⟩
    have hV_bot : V = ⊥ := by
      rw [← Submodule.rank_eq_zero]
      exact le_antisymm (by exact_mod_cast hV) zero_le
    rw [hV_bot, deviationFromSubspace_bot]

/-- Upper bound by the operator norm: `d_n S ≤ ‖S‖`, since `d_n S ≤ d_0 S = ‖S‖`. -/
lemma kolmogorovNumber_le_norm (S : X →L[𝕜] Y) (n : ℕ) :
    kolmogorovNumber S n ≤ ‖S‖ :=
  (antitone_nat_of_succ_le (kolmogorovNumber_antitone S) (Nat.zero_le n)).trans_eq
    (kolmogorovNumber_zero_eq_norm S)


/-! ## Additivity and multiplicativity

The strong forms of (S2) and (S3), in which subspaces are chosen for both operators:

* if `V` is admissible for `S` (dimension `≤ n`) and `U` for `T` (dimension `≤ m`),
  then `V ⊔ U` is admissible for `S + T` at stage `n + m`, and enlarging the subspace
  does not increase the quotient norms (`deviationFromSubspace_anti`);
* for `T : X → Y` and `S : Y → Z`, if `V ⊆ Z` is admissible for `S` and `U ⊆ Y` for `T`,
  then `V ⊔ S(U)` is admissible for `S ∘ T` at stage `n + m`: the map
  `y ↦ [S y]_{V ⊔ S(U)}` vanishes on `U`, so it factors through `Y/U` with norm at
  most `‖π_V ∘ S‖`. -/

/-- Enlarging the subspace does not increase the quotient norm:
`V ≤ V' ⇒ ‖π_{V'} ∘ S‖ ≤ ‖π_V ∘ S‖`, since `π_{V'}` factors through `π_V` with a
contraction. -/
lemma deviationFromSubspace_anti (S : X →L[𝕜] Y) {V V' : Submodule 𝕜 Y} (h : V ≤ V') :
    deviationFromSubspace S V' ≤ deviationFromSubspace S V := by
  -- `π_{V'}` vanishes on `V`, so it descends to `Y/V`
  have h_ker : V ≤ LinearMap.ker (V'.mkQL : Y →ₗ[𝕜] Y ⧸ V') := by
    intro v hv
    show V'.mkQL v = 0
    rw [Submodule.mkQL_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact h hv
  have hfac : V'.mkQL.comp S = (V.liftQL V'.mkQL h_ker).comp (V.mkQL.comp S) := by
    ext x
    exact (V.liftQL_mkQL V'.mkQL h_ker (S x)).symm
  show ‖V'.mkQL.comp S‖ ≤ ‖V.mkQL.comp S‖
  rw [hfac]
  calc ‖(V.liftQL V'.mkQL h_ker).comp (V.mkQL.comp S)‖
      ≤ ‖V.liftQL V'.mkQL h_ker‖ * ‖V.mkQL.comp S‖ := opNorm_comp_le _ _
    _ ≤ 1 * ‖V.mkQL.comp S‖ :=
        mul_le_mul_of_nonneg_right ((V.norm_liftQL_le _ h_ker).trans V'.norm_mkQL_le)
          (norm_nonneg _)
    _ = ‖V.mkQL.comp S‖ := one_mul _

/-- The triangle inequality for quotient norms:
`‖π_V ∘ (S + T)‖ ≤ ‖π_V ∘ S‖ + ‖π_V ∘ T‖`. -/
lemma deviationFromSubspace_add_le (S T : X →L[𝕜] Y) (V : Submodule 𝕜 Y) :
    deviationFromSubspace (S + T) V ≤
      deviationFromSubspace S V + deviationFromSubspace T V := by
  unfold deviationFromSubspace
  rw [ContinuousLinearMap.comp_add]
  exact norm_add_le _ _

/-- Per-subspace multiplicativity: for `T : X → Y`, `S : Y → Z`, `V ⊆ Z` and `U ⊆ Y`,
`‖π_{V ⊔ S(U)} ∘ S ∘ T‖ ≤ ‖π_V ∘ S‖ · ‖π_U ∘ T‖`. -/
lemma deviationFromSubspace_comp_sup_map_le (S : Y →L[𝕜] Z) (T : X →L[𝕜] Y)
    (V : Submodule 𝕜 Z) (U : Submodule 𝕜 Y) :
    deviationFromSubspace (S.comp T) (V ⊔ U.map (S : Y →ₗ[𝕜] Z)) ≤
      deviationFromSubspace S V * deviationFromSubspace T U := by
  set L : Submodule 𝕜 Z := V ⊔ U.map (S : Y →ₗ[𝕜] Z) with hL
  set SL : Y →L[𝕜] Z ⧸ L := L.mkQL.comp S with hSL
  -- `y ↦ [S y]_L` vanishes on `U`, since `S(U) ⊆ L`
  have h_ker : U ≤ LinearMap.ker (SL : Y →ₗ[𝕜] Z ⧸ L) := by
    intro w hw
    show L.mkQL (S w) = 0
    rw [Submodule.mkQL_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact (le_sup_right : U.map (S : Y →ₗ[𝕜] Z) ≤ L) (Submodule.mem_map_of_mem hw)
  -- and its norm is at most `‖π_V ∘ S‖`, since `V ≤ L`
  have h_SL : ‖SL‖ ≤ deviationFromSubspace S V :=
    deviationFromSubspace_anti S (le_sup_left : V ≤ L)
  have hfac : L.mkQL.comp (S.comp T) = (U.liftQL SL h_ker).comp (U.mkQL.comp T) := by
    ext x
    exact (U.liftQL_mkQL SL h_ker (T x)).symm
  show ‖L.mkQL.comp (S.comp T)‖ ≤ _
  rw [hfac]
  calc ‖(U.liftQL SL h_ker).comp (U.mkQL.comp T)‖
      ≤ ‖U.liftQL SL h_ker‖ * ‖U.mkQL.comp T‖ := opNorm_comp_le _ _
    _ ≤ deviationFromSubspace S V * deviationFromSubspace T U :=
        mul_le_mul_of_nonneg_right ((U.norm_liftQL_le SL h_ker).trans h_SL) (norm_nonneg _)

/-- **Additivity of the Kolmogorov numbers**: `d_{n+m}(S + T) ≤ dₙ(S) + d_m(T)`. -/
theorem kolmogorovNumber_additive (S T : X →L[𝕜] Y) (n m : ℕ) :
    kolmogorovNumber (S + T) (n + m) ≤ kolmogorovNumber S n + kolmogorovNumber T m := by
  -- one admissible subspace for each operator
  have hkey : ∀ V : Submodule 𝕜 Y, Module.rank 𝕜 V ≤ (n : Cardinal) →
      ∀ U : Submodule 𝕜 Y, Module.rank 𝕜 U ≤ (m : Cardinal) →
      kolmogorovNumber (S + T) (n + m) ≤
        deviationFromSubspace S V + deviationFromSubspace T U := by
    intro V hV U hU
    have h_rank : Module.rank 𝕜 ↥(V ⊔ U) ≤ ((n + m : ℕ) : Cardinal) := by
      rw [Nat.cast_add]
      exact (Submodule.rank_add_le_rank_add_rank V U).trans (add_le_add hV hU)
    calc kolmogorovNumber (S + T) (n + m)
        ≤ deviationFromSubspace (S + T) (V ⊔ U) := kolmogorovNumber_le_deviation h_rank
      _ ≤ deviationFromSubspace S (V ⊔ U) + deviationFromSubspace T (V ⊔ U) :=
          deviationFromSubspace_add_le S T _
      _ ≤ deviationFromSubspace S V + deviationFromSubspace T U :=
          add_le_add (deviationFromSubspace_anti S le_sup_left)
            (deviationFromSubspace_anti T le_sup_right)
  -- infimum over `V`, then over `U`
  rw [← sub_le_iff_le_add]
  refine le_kolmogorovNumber fun V hV => ?_
  rw [sub_le_comm]
  refine le_kolmogorovNumber fun U hU => ?_
  linarith [hkey V hV U hU]

/-- **Multiplicativity of the Kolmogorov numbers**: for `T : X → Y` and `S : Y → Z`,
`d_{n+m}(S ∘ T) ≤ dₙ(S) · d_m(T)`. -/
theorem kolmogorovNumber_multiplicative (S : Y →L[𝕜] Z) (T : X →L[𝕜] Y) (n m : ℕ) :
    kolmogorovNumber (S.comp T) (n + m) ≤ kolmogorovNumber S n * kolmogorovNumber T m := by
  -- one admissible subspace for each operator
  have hkey : ∀ V : Submodule 𝕜 Z, Module.rank 𝕜 V ≤ (n : Cardinal) →
      ∀ U : Submodule 𝕜 Y, Module.rank 𝕜 U ≤ (m : Cardinal) →
      kolmogorovNumber (S.comp T) (n + m) ≤
        deviationFromSubspace S V * deviationFromSubspace T U := by
    intro V hV U hU
    have h_rank : Module.rank 𝕜 ↥(V ⊔ U.map (S : Y →ₗ[𝕜] Z)) ≤
        ((n + m : ℕ) : Cardinal) := by
      rw [Nat.cast_add]
      exact (Submodule.rank_add_le_rank_add_rank _ _).trans
        (add_le_add hV ((rank_map_le _ _).trans hU))
    exact (kolmogorovNumber_le_deviation h_rank).trans
      (deviationFromSubspace_comp_sup_map_le S T V U)
  -- For fixed `V`, take the infimum over `U`, pulling `‖π_V ∘ S‖ ≥ 0` inside it.
  have h1 : ∀ V : Submodule 𝕜 Z, Module.rank 𝕜 V ≤ (n : Cardinal) →
      kolmogorovNumber (S.comp T) (n + m) ≤
        deviationFromSubspace S V * kolmogorovNumber T m := by
    intro V hV
    show _ ≤ deviationFromSubspace S V • sInf (kolmogorovSet T m)
    rw [← Real.sInf_smul_of_nonneg (deviationFromSubspace_nonneg S V)]
    refine le_csInf ((kolmogorovSet_nonempty T m).image _) ?_
    rintro _ ⟨_, ⟨U, hU, rfl⟩, rfl⟩
    exact hkey V hV U hU
  -- Then take the infimum over `V`, pulling `d_m(T) ≥ 0` inside it.
  rw [mul_comm]
  show _ ≤ kolmogorovNumber T m • sInf (kolmogorovSet S n)
  rw [← Real.sInf_smul_of_nonneg (kolmogorovNumber_nonneg T m)]
  refine le_csInf ((kolmogorovSet_nonempty S n).image _) ?_
  rintro _ ⟨_, ⟨V, hV, rfl⟩, rfl⟩
  show _ ≤ kolmogorovNumber T m * deviationFromSubspace S V
  rw [mul_comm]
  exact h1 V hV

/-! ## (S2) Subadditivity -/

/-- (S2) `d_n (S + T) ≤ d_n S + ‖T‖`: additivity with `m = 0`, since `d_0 T = ‖T‖`. -/
lemma kolmogorovNumber_add_le (S T : X →L[𝕜] Y) (n : ℕ) :
    kolmogorovNumber (S + T) n ≤ kolmogorovNumber S n + ‖T‖ := by
  have h := kolmogorovNumber_additive S T n 0
  rwa [Nat.add_zero, kolmogorovNumber_zero_eq_norm] at h

/-! ## (S3) Ideal property

The ideal property is multiplicativity applied twice with one index `0`. The
per-subspace bound `deviationFromSubspace_comp_comp_map_le` treats it directly, with the
single subspace `B(V)`: for `w : W` it chains three `le_opNorm` applications, one for the
descent of `B` to a map `Y/V →L[𝕜] Z/B(V)` (constructed inline via `V.liftQL`), one for
`V.mkQL.comp S`, and one for `A`. -/

/-- (S3) `d_n (B ∘ S ∘ A) ≤ ‖B‖ * d_n S * ‖A‖`: multiplicativity applied twice with one
index `0`, since `d_0 = ‖·‖`. -/
lemma kolmogorovNumber_comp_comp_le
    (A : W →L[𝕜] X) (S : X →L[𝕜] Y) (B : Y →L[𝕜] Z) (n : ℕ) :
    kolmogorovNumber (B.comp (S.comp A)) n ≤
      ‖B‖ * kolmogorovNumber S n * ‖A‖ := by
  have hSA : kolmogorovNumber (S.comp A) n ≤ kolmogorovNumber S n * ‖A‖ := by
    have h := kolmogorovNumber_multiplicative S A n 0
    rwa [Nat.add_zero, kolmogorovNumber_zero_eq_norm] at h
  have hB : kolmogorovNumber (B.comp (S.comp A)) n ≤
      ‖B‖ * kolmogorovNumber (S.comp A) n := by
    have h := kolmogorovNumber_multiplicative B (S.comp A) 0 n
    rwa [Nat.zero_add, kolmogorovNumber_zero_eq_norm] at h
  calc kolmogorovNumber (B.comp (S.comp A)) n
      ≤ ‖B‖ * kolmogorovNumber (S.comp A) n := hB
    _ ≤ ‖B‖ * (kolmogorovNumber S n * ‖A‖) :=
        mul_le_mul_of_nonneg_left hSA (norm_nonneg B)
    _ = ‖B‖ * kolmogorovNumber S n * ‖A‖ := (mul_assoc _ _ _).symm

/-- Per-subspace (S3) bound:
`deviation(B ∘ S ∘ A, B(V)) ≤ ‖B‖ * ‖A‖ * deviation(S, V)`. -/
lemma deviationFromSubspace_comp_comp_map_le
    (A : W →L[𝕜] X) (S : X →L[𝕜] Y) (B : Y →L[𝕜] Z) (V : Submodule 𝕜 Y) :
    deviationFromSubspace (B.comp (S.comp A)) (V.map (B : Y →ₗ[𝕜] Z))
      ≤ ‖B‖ * ‖A‖ * deviationFromSubspace S V := by
  unfold deviationFromSubspace
  -- The CLM `(V.map B).mkQL ∘ B : Y →L[𝕜] Z/(V.map B)` has `V` in its
  -- kernel: for `v ∈ V`, `B v ∈ V.map B`, hence `[B v]_{Z/(V.map B)} = 0`.
  -- It therefore descends through `V.mkQL` via `V.liftQL` to a CLM
  -- `Y/V →L[𝕜] Z/(V.map B)` whose norm is bounded by `‖B‖`.
  set BL : Y →L[𝕜] (Z ⧸ V.map (B : Y →ₗ[𝕜] Z)) :=
    (V.map (B : Y →ₗ[𝕜] Z)).mkQL.comp B with hBL_def
  have h_ker :
      V ≤ LinearMap.ker (BL : Y →ₗ[𝕜] (Z ⧸ V.map (B : Y →ₗ[𝕜] Z))) := by
    intro v hv
    show (V.map (B : Y →ₗ[𝕜] Z)).mkQL (B v) = 0
    rw [Submodule.mkQL_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact ⟨v, hv, rfl⟩
  have h_BL_norm : ‖BL‖ ≤ ‖B‖ := by
    rw [hBL_def]
    calc ‖(V.map (B : Y →ₗ[𝕜] Z)).mkQL.comp B‖
        ≤ ‖(V.map (B : Y →ₗ[𝕜] Z)).mkQL‖ * ‖B‖ := opNorm_comp_le _ _
      _ ≤ 1 * ‖B‖ := mul_le_mul_of_nonneg_right
          (V.map (B : Y →ₗ[𝕜] Z)).norm_mkQL_le (norm_nonneg _)
      _ = ‖B‖ := one_mul _
  have h_lift_norm : ‖V.liftQL BL h_ker‖ ≤ ‖B‖ :=
    (V.norm_liftQL_le BL h_ker).trans h_BL_norm
  -- Pointwise bound on `w : W`.
  have h_bound_nn : 0 ≤ ‖B‖ * ‖A‖ * ‖V.mkQL.comp S‖ :=
    mul_nonneg (mul_nonneg (norm_nonneg B) (norm_nonneg A))
      (norm_nonneg (V.mkQL.comp S))
  refine opNorm_le_bound _ h_bound_nn fun w => ?_
  show ‖(V.map (B : Y →ₗ[𝕜] Z)).mkQL (B (S (A w)))‖ ≤
       ‖B‖ * ‖A‖ * ‖V.mkQL.comp S‖ * ‖w‖
  -- Apply the descent: `BL (S (A w)) = V.liftQL BL _ (V.mkQL (S (A w)))`.
  have h_apply : (V.map (B : Y →ₗ[𝕜] Z)).mkQL (B (S (A w)))
      = V.liftQL BL h_ker (V.mkQL (S (A w))) :=
    (V.liftQL_mkQL BL h_ker (S (A w))).symm
  rw [h_apply]
  calc ‖V.liftQL BL h_ker (V.mkQL (S (A w)))‖
      ≤ ‖V.liftQL BL h_ker‖ * ‖(V.mkQL.comp S) (A w)‖ :=
        (V.liftQL BL h_ker).le_opNorm _
    _ ≤ ‖B‖ * ‖(V.mkQL.comp S) (A w)‖ :=
        mul_le_mul_of_nonneg_right h_lift_norm (norm_nonneg _)
    _ ≤ ‖B‖ * (‖V.mkQL.comp S‖ * ‖A w‖) :=
        mul_le_mul_of_nonneg_left ((V.mkQL.comp S).le_opNorm (A w))
          (norm_nonneg B)
    _ ≤ ‖B‖ * (‖V.mkQL.comp S‖ * (‖A‖ * ‖w‖)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (A.le_opNorm w)
            (norm_nonneg (V.mkQL.comp S)))
          (norm_nonneg B)
    _ = ‖B‖ * ‖A‖ * ‖V.mkQL.comp S‖ * ‖w‖ := by ring

/-! ## (S4) Vanishing on operators of rank at most `n` -/

lemma kolmogorovNumber_eq_zero_of_rank_le {S : X →L[𝕜] Y} {n : ℕ}
    (hS : S.rank ≤ (n : Cardinal)) :
    kolmogorovNumber S n = 0 := by
  refine le_antisymm ?_ (kolmogorovNumber_nonneg S n)
  -- Take `V = range S`. Then `V.mkQL ∘ S = 0`, so `deviation = 0`.
  set V : Submodule 𝕜 Y := LinearMap.range (S : X →ₗ[𝕜] Y) with hV_def
  have hV_rank : Module.rank 𝕜 V ≤ (n : Cardinal) := hS
  refine (kolmogorovNumber_le_deviation hV_rank).trans ?_
  -- `V.mkQL.comp S = 0` because every `S x ∈ V`, so `[S x] = 0` in `Y/V`.
  have h_comp_zero : V.mkQL.comp S = 0 := by
    ext x
    simp only [coe_comp, Function.comp_apply, zero_apply,
      Submodule.mkQL_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact LinearMap.mem_range_self (S : X →ₗ[𝕜] Y) x
  show ‖V.mkQL.comp S‖ ≤ 0
  rw [h_comp_zero]; exact le_of_eq (ContinuousLinearMap.opNorm_zero)


/-! ## (S5') Strict normalisation `kolmogorovNumber (id_X) n = 1` whenever `dim X > n`

For any closed proper finite-dim `V ⊆ X`, Riesz's lemma gives
`x₀ ∉ V` with `(1 − ε) * ‖x₀‖ ≤ ‖x₀ − y‖` for every `y ∈ V`. The infimum
on the RHS is exactly `‖V.mkQL x₀‖`. Combining with `le_opNorm` and
cancelling `‖x₀‖ > 0` gives `(1 − ε) ≤ ‖V.mkQL‖`. Letting ε → 0 finishes
the lower bound. The upper bound `‖V.mkQL.comp id‖ = ‖V.mkQL‖ ≤ 1` is
already in `Submodule.norm_mkQL_le`. -/

variable [CompleteSpace 𝕜]

private lemma one_le_norm_mkQL_of_proper {X : Type u} [NormedAddCommGroup X]
    [NormedSpace 𝕜 X] {V : Submodule 𝕜 X} [FiniteDimensional 𝕜 V] (hV_ne_top : V ≠ ⊤) :
    (1 : ℝ) ≤ ‖V.mkQL‖ := by
  have hV_closed : IsClosed (V : Set X) := V.closed_of_finiteDimensional
  have hV_exists : ∃ x : X, x ∉ V := SetLike.exists_not_mem_of_ne_top V hV_ne_top
  -- Limit `r → 1`: enough to show `1 ≤ ‖V.mkQL‖ + ε` for every `ε > 0`. The
  -- `ε ≥ 1` case is trivial (RHS ≥ 0 + 1); for `ε ∈ (0, 1)` we run Riesz at
  -- level `1 − ε`.
  refine le_of_forall_pos_le_add fun ε hε => ?_
  by_cases hε1 : 1 ≤ ε
  · linarith [norm_nonneg V.mkQL]
  have hε1' : ε < 1 := lt_of_not_ge hε1
  have h_aux : (1 - ε : ℝ) < 1 := by linarith
  obtain ⟨x₀, hx₀_ne, hx₀_dist⟩ := riesz_lemma hV_closed hV_exists h_aux
  have hx₀_ne_zero : x₀ ≠ 0 := fun h0 => hx₀_ne (h0 ▸ V.zero_mem)
  have hx₀_norm_pos : 0 < ‖x₀‖ := norm_pos_iff.mpr hx₀_ne_zero
  -- `‖V.mkQL x₀‖ = infDist x₀ V ≥ (1 − ε) · ‖x₀‖` via Riesz.
  have h_quot_ge : (1 - ε) * ‖x₀‖ ≤ ‖V.mkQL x₀‖ := by
    have h_norm_eq : ‖V.mkQL x₀‖ = Metric.infDist x₀ V :=
      QuotientAddGroup.norm_mk (S := V.toAddSubgroup) x₀
    rw [h_norm_eq, Metric.le_infDist ⟨0, V.zero_mem⟩]
    intro y hy
    rw [dist_eq_norm]
    exact hx₀_dist y hy
  -- `‖V.mkQL‖ · ‖x₀‖ ≥ ‖V.mkQL x₀‖ ≥ (1 − ε) · ‖x₀‖`. Cancel `‖x₀‖ > 0`,
  -- then rearrange.
  have h_op : ‖V.mkQL x₀‖ ≤ ‖V.mkQL‖ * ‖x₀‖ := V.mkQL.le_opNorm x₀
  have h_chain : (1 - ε) * ‖x₀‖ ≤ ‖V.mkQL‖ * ‖x₀‖ := h_quot_ge.trans h_op
  linarith [le_of_mul_le_mul_right h_chain hx₀_norm_pos]

/-- (S5') Strict normalisation: `kolmogorovNumber (id_X) n = 1` whenever
`n < Module.finrank 𝕜 X`. -/
lemma kolmogorovNumber_strict {X : Type u} [NormedAddCommGroup X]
    [NormedSpace 𝕜 X] (n : ℕ) (h : n < Module.finrank 𝕜 X) :
    kolmogorovNumber (ContinuousLinearMap.id 𝕜 X) n = 1 := by
  have h_finrank_pos : 0 < Module.finrank 𝕜 X :=
    Nat.lt_of_le_of_lt (Nat.zero_le _) h
  have : FiniteDimensional 𝕜 X := .of_finrank_pos h_finrank_pos
  have : Nontrivial X := Module.nontrivial_of_finrank_pos h_finrank_pos
  set I := ContinuousLinearMap.id 𝕜 X with hI_def
  refine le_antisymm ?_ ?_
  · -- `≤ 1`: take `V = ⊥`. `deviation(I, ⊥) = ‖I‖ = 1`.
    have h_rank_bot : Module.rank 𝕜 (⊥ : Submodule 𝕜 X) ≤ (n : Cardinal) := by
      rw [rank_bot]; exact zero_le
    calc kolmogorovNumber I n
        ≤ deviationFromSubspace I ⊥ := kolmogorovNumber_le_deviation h_rank_bot
      _ = ‖I‖ := deviationFromSubspace_bot _
      _ = 1 := norm_id
  · -- `≥ 1`: every admissible `V` is proper, so `‖V.mkQL‖ ≥ 1`, and
    -- `deviation(I, V) = ‖V.mkQL.comp I‖ = ‖V.mkQL‖`.
    refine le_csInf (kolmogorovSet_nonempty I n) ?_
    rintro _ ⟨V, hV, rfl⟩
    have hV_finrank_le : Module.finrank 𝕜 V ≤ n := Module.finrank_le_of_rank_le hV
    have hV_finrank_lt : Module.finrank 𝕜 V < Module.finrank 𝕜 X :=
      lt_of_le_of_lt hV_finrank_le h
    have hV_ne_top : V ≠ ⊤ := by
      intro h_top
      rw [h_top, finrank_top] at hV_finrank_lt
      exact lt_irrefl _ hV_finrank_lt
    have : FiniteDimensional 𝕜 V := FiniteDimensional.finiteDimensional_submodule V
    have h_dev_eq : deviationFromSubspace I V = ‖V.mkQL‖ := by
      show ‖V.mkQL.comp I‖ = ‖V.mkQL‖
      rw [hI_def, ContinuousLinearMap.comp_id]
    rw [h_dev_eq]
    exact one_le_norm_mkQL_of_proper hV_ne_top

/-- (S5) Normalisation on `id_{ℓ₂^{n+1}}`: a special case of (S5'). -/
lemma kolmogorovNumber_id_euclidean (n : ℕ) :
    kolmogorovNumber
      (ContinuousLinearMap.id 𝕜 (EuclideanSpace 𝕜 (Fin (n + 1)))) n = 1 := by
  have h : n < Module.finrank 𝕜 (EuclideanSpace 𝕜 (Fin (n + 1))) := by
    rw [finrank_euclideanSpace_fin' (n + 1)]; exact Nat.lt_succ_self n
  exact kolmogorovNumber_strict n h

/-! ## Summary: Kolmogorov numbers (quotient form) form a strict s-number sequence -/

theorem isSNumberSequence_kolmogorovNumber :
    IsSNumberSequence (𝕜 := 𝕜)
        (fun {_X _Y} _ _ _ _ S n => kolmogorovNumber S n) where
  nonneg := fun S n => kolmogorovNumber_nonneg S n
  norm_at_zero := fun S => kolmogorovNumber_zero_eq_norm S
  antitone := fun S n => kolmogorovNumber_antitone S n
  subadditive := fun S T n => kolmogorovNumber_add_le S T n
  ideal := fun A S B n => kolmogorovNumber_comp_comp_le A S B n
  vanishes_on_low_rank := fun _ _ h => kolmogorovNumber_eq_zero_of_rank_le h
  normalised_at_id := fun n => kolmogorovNumber_id_euclidean n

theorem isStrictSNumberSequence_kolmogorovNumber :
    IsStrictSNumberSequence (𝕜 := 𝕜)
        (fun {_X _Y} _ _ _ _ S n => kolmogorovNumber S n) where
  toIsSNumberSequence := isSNumberSequence_kolmogorovNumber
  strictly_normalised_at_id := fun n h => kolmogorovNumber_strict n h

omit [CompleteSpace 𝕜] in
/-- The Kolmogorov numbers are additive: `d_{n+m}(S + T) ≤ dₙ(S) + d_m(T)`. -/
theorem additive_kolmogorovNumber :
    Additive (𝕜 := 𝕜) (fun {_X _Y} _ _ _ _ S n => kolmogorovNumber S n) :=
  fun S T n m => kolmogorovNumber_additive S T n m

omit [CompleteSpace 𝕜] in
/-- The Kolmogorov numbers are multiplicative: `d_{n+m}(S ∘ T) ≤ dₙ(S) · d_m(T)`. -/
theorem multiplicative_kolmogorovNumber :
    Multiplicative (𝕜 := 𝕜) (fun {_X _Y} _ _ _ _ S n => kolmogorovNumber S n) :=
  fun S T n m => kolmogorovNumber_multiplicative S T n m

end SNumbers
