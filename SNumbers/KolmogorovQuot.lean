/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
import SNumbers.Helpers
import Mathlib.Analysis.Normed.Module.RieszLemma
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Group.Quotient

/-!
# Kolmogorov numbers `d_n` — explicit quotient-space development

This file gives a **fully explicit, self-contained** development of the
Kolmogorov numbers, exposing every step of the construction (quotient
norm, deviation, lifted operator on quotients, Riesz lemma). It is
intended as the *reference* / pedagogical version: long but transparent.

The companion file `SNumbers.Kolmogorov` provides a much shorter
treatment via Pietsch's identity `d_n(S) = a_n(S ∘ Q)`, which delegates
most axioms to the approximation-number theory. Use that file for
concise reasoning; use this one when you want to see the underlying
quotient-space mechanics.

## What this file does

The classical definition

  `d_n S = inf_{V ⊆ Y, dim V ≤ n} sup_{x ∈ B_X} inf_{y ∈ V} ‖S x - y‖`

is recast as

  `d_n S = inf_{V ⊆ Y, dim V ≤ n} ‖π_V ∘ S‖`

where `π_V : Y →L[𝕜] (Y ⧸ V)` is the quotient map: the inner
`inf_y ‖S x − y‖` is exactly the quotient norm `‖[S x]‖_{Y/V}`, and the
outer `sup_{‖x‖ ≤ 1}` is then the operator norm of the composition.

This formulation immediately collapses the two ε-arguments that appear
in a direct unfolding of the inf/sup definition:

* **(S3) ideal property.** Reduces to operator-norm submultiplicativity
  applied to the lifted quotient map `B̃ : Y/V →L[𝕜] Z/B(V)`. No
  `DenselyNormedField` rescaling needed.
* **(S5') strict normalisation.** Uses Riesz's lemma once together with
  `le_opNorm` — no second density-rescaling pass.

## Names

Primed throughout (`deviationFromSubspace'`, `kolmogorovNumber'`) so
this file coexists with `SNumbers.Kolmogorov` (which exports the
unprimed names via the Pietsch route).

## File-local helpers

The continuous-linear-map wrappers `Submodule.mkQL` (quotient projection)
and `Submodule.liftQL` (universal lift) are introduced here as `private`
declarations because they are used **only in this file**. If the rest of
the project ever needs a `ContinuousLinearMap` form of `mkQ` / `liftQ`,
these definitions should move into a shared helpers file (or be
upstreamed to mathlib).
-/

universe u

open scoped Cardinal
open ContinuousLinearMap

/-! ## Continuous-linear-map versions of the quotient API (file-local)

Mathlib ships `Submodule.mkQ` (a `LinearMap`) and `Submodule.liftQ` (also a
`LinearMap`); the normed-quotient API in `Mathlib.Analysis.Normed.Group.Quotient`
provides the corresponding `NormedAddGroupHom`s but no `ContinuousLinearMap`
wrappers. The two definitions below — `Submodule.mkQL` and `Submodule.liftQL` —
package the quotient projection and the universal lift as `ContinuousLinearMap`s
with the operator-norm bounds we need: `‖V.mkQL‖ ≤ 1` and `‖V.liftQL f h‖ ≤ ‖f‖`.

They are marked `private` because they are only used **in this file**. If
they prove useful elsewhere, lift them out into a shared helpers file. -/

namespace Submodule

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {Y Z : Type*}
variable [SeminormedAddCommGroup Y] [NormedSpace 𝕜 Y]
variable [SeminormedAddCommGroup Z] [NormedSpace 𝕜 Z]

/-- The quotient map `Y →L[𝕜] (Y ⧸ V)` as a continuous linear map. -/
private noncomputable def mkQL (V : Submodule 𝕜 Y) : Y →L[𝕜] (Y ⧸ V) :=
  V.mkQ.mkContinuous 1 fun x => by
    rw [one_mul, mkQ_apply]
    exact _root_.Submodule.Quotient.norm_mk_le (S := V) x

@[simp] private lemma mkQL_apply (V : Submodule 𝕜 Y) (x : Y) :
    V.mkQL x = V.mkQ x := rfl

@[simp] private lemma mkQL_toLinearMap (V : Submodule 𝕜 Y) :
    (V.mkQL : Y →ₗ[𝕜] Y ⧸ V) = V.mkQ := rfl

private lemma norm_mkQL_le (V : Submodule 𝕜 Y) : ‖V.mkQL‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

/-- Lift a continuous linear map `f : Y →L[𝕜] Z` whose kernel contains `V`
to a continuous linear map `(Y ⧸ V) →L[𝕜] Z`. The norm bound
`‖V.liftQL f h‖ ≤ ‖f‖` is `Submodule.norm_liftQL_le`. -/
private noncomputable def liftQL (V : Submodule 𝕜 Y) (f : Y →L[𝕜] Z)
    (h : V ≤ LinearMap.ker (f : Y →ₗ[𝕜] Z)) : (Y ⧸ V) →L[𝕜] Z :=
  (V.liftQ (f : Y →ₗ[𝕜] Z) h).mkContinuous ‖f‖ <| by
    -- For each `x : Y ⧸ V`, take a representative `y` with `‖y‖ ≤ ‖x‖ + ε`.
    -- Then `liftQ f h x = f y`, so `‖liftQ f h x‖ ≤ ‖f‖ * ‖y‖ ≤ ‖f‖ * (‖x‖ + ε)`,
    -- and ε → 0.
    intro x
    refine le_of_forall_pos_le_add fun ε hε => ?_
    have hf_pos : (0 : ℝ) < ‖f‖ + 1 := by positivity
    obtain ⟨y, hy_eq, hy_norm⟩ :=
      Submodule.Quotient.norm_mk_lt x (div_pos hε hf_pos)
    have h_eq : (V.liftQ (f : Y →ₗ[𝕜] Z) h) x = f y := by
      rw [← hy_eq]; exact V.liftQ_apply (f : Y →ₗ[𝕜] Z) y
    rw [h_eq]
    calc ‖f y‖
        ≤ ‖f‖ * ‖y‖ := f.le_opNorm y
      _ ≤ ‖f‖ * (‖x‖ + ε / (‖f‖ + 1)) :=
          mul_le_mul_of_nonneg_left hy_norm.le (norm_nonneg _)
      _ = ‖f‖ * ‖x‖ + ‖f‖ / (‖f‖ + 1) * ε := by ring
      _ ≤ ‖f‖ * ‖x‖ + 1 * ε := by
          gcongr
          rw [div_le_one hf_pos]; linarith [norm_nonneg f]
      _ = ‖f‖ * ‖x‖ + ε := by ring

@[simp] private lemma liftQL_mkQL (V : Submodule 𝕜 Y) (f : Y →L[𝕜] Z)
    (h : V ≤ LinearMap.ker (f : Y →ₗ[𝕜] Z)) (y : Y) :
    V.liftQL f h (V.mkQL y) = f y :=
  V.liftQ_apply (f : Y →ₗ[𝕜] Z) y

private lemma norm_liftQL_le (V : Submodule 𝕜 Y) (f : Y →L[𝕜] Z)
    (h : V ≤ LinearMap.ker (f : Y →ₗ[𝕜] Z)) :
    ‖V.liftQL f h‖ ≤ ‖f‖ :=
  LinearMap.mkContinuous_norm_le _ (norm_nonneg _) _

end Submodule

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
noncomputable def deviationFromSubspace' (S : X →L[𝕜] Y) (V : Submodule 𝕜 Y) : ℝ :=
  ‖V.mkQL.comp S‖

/-- Quotient form of the `n`-th Kolmogorov number. -/
noncomputable def kolmogorovNumber' (S : X →L[𝕜] Y) (n : ℕ) : ℝ :=
  sInf {r | ∃ V : Submodule 𝕜 Y,
      Module.rank 𝕜 V ≤ (n : Cardinal) ∧ r = deviationFromSubspace' S V}

/-! ### Basic facts about `deviationFromSubspace'` -/

lemma deviationFromSubspace'_nonneg (S : X →L[𝕜] Y) (V : Submodule 𝕜 Y) :
    0 ≤ deviationFromSubspace' S V :=
  norm_nonneg (V.mkQL.comp S)

lemma deviationFromSubspace'_le_norm (S : X →L[𝕜] Y) (V : Submodule 𝕜 Y) :
    deviationFromSubspace' S V ≤ ‖S‖ := by
  unfold deviationFromSubspace'
  calc ‖V.mkQL.comp S‖
      ≤ ‖V.mkQL‖ * ‖S‖ := opNorm_comp_le _ _
    _ ≤ 1 * ‖S‖ := mul_le_mul_of_nonneg_right V.norm_mkQL_le (norm_nonneg _)
    _ = ‖S‖ := one_mul _

/-! ### Helpers for the infimum set defining `kolmogorovNumber'` -/

private lemma kSet_nonempty (S : X →L[𝕜] Y) (n : ℕ) :
    {r : ℝ | ∃ V : Submodule 𝕜 Y,
        Module.rank 𝕜 V ≤ (n : Cardinal) ∧ r = deviationFromSubspace' S V}.Nonempty :=
  ⟨_, ⊥, by rw [rank_bot]; exact bot_le, rfl⟩

private lemma kSet_bddBelow (S : X →L[𝕜] Y) (n : ℕ) :
    BddBelow {r : ℝ | ∃ V : Submodule 𝕜 Y,
        Module.rank 𝕜 V ≤ (n : Cardinal) ∧ r = deviationFromSubspace' S V} :=
  ⟨0, by rintro _ ⟨V, _, rfl⟩; exact deviationFromSubspace'_nonneg S V⟩

lemma kolmogorovNumber'_le_deviation {S : X →L[𝕜] Y} {n : ℕ} {V : Submodule 𝕜 Y}
    (hV : Module.rank 𝕜 V ≤ (n : Cardinal)) :
    kolmogorovNumber' S n ≤ deviationFromSubspace' S V :=
  csInf_le (kSet_bddBelow S n) ⟨V, hV, rfl⟩

/-! ### (S1c) Non-negativity -/

lemma kolmogorovNumber'_nonneg (S : X →L[𝕜] Y) (n : ℕ) :
    0 ≤ kolmogorovNumber' S n :=
  Real.sInf_nonneg <| by
    rintro _ ⟨V, _, rfl⟩; exact deviationFromSubspace'_nonneg S V

/-! ### (S1b) Antitone in `n` -/

lemma kolmogorovNumber'_antitone (S : X →L[𝕜] Y) (n : ℕ) :
    kolmogorovNumber' S (n + 1) ≤ kolmogorovNumber' S n := by
  refine csInf_le_csInf (kSet_bddBelow S (n + 1)) (kSet_nonempty S n) ?_
  rintro _ ⟨V, hV, rfl⟩
  exact ⟨V, hV.trans (by exact_mod_cast Nat.le_succ n), rfl⟩

/-! ### (S4) Vanishing on operators of rank at most `n` -/

lemma kolmogorovNumber'_eq_zero_of_rank_le {S : X →L[𝕜] Y} {n : ℕ}
    (hS : S.rank ≤ (n : Cardinal)) :
    kolmogorovNumber' S n = 0 := by
  refine le_antisymm ?_ (kolmogorovNumber'_nonneg S n)
  -- Take `V = range S`. Then `V.mkQL ∘ S = 0`, so `deviation = 0`.
  set V : Submodule 𝕜 Y := LinearMap.range (S : X →ₗ[𝕜] Y) with hV_def
  have hV_rank : Module.rank 𝕜 V ≤ (n : Cardinal) := hS
  refine (kolmogorovNumber'_le_deviation hV_rank).trans ?_
  -- `V.mkQL.comp S = 0` because every `S x ∈ V`, so `[S x] = 0` in `Y/V`.
  have h_comp_zero : V.mkQL.comp S = 0 := by
    ext x
    simp only [coe_comp', Function.comp_apply, ContinuousLinearMap.zero_apply,
      Submodule.mkQL_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact LinearMap.mem_range_self (S : X →ₗ[𝕜] Y) x
  show ‖V.mkQL.comp S‖ ≤ 0
  rw [h_comp_zero]; exact le_of_eq (ContinuousLinearMap.opNorm_zero)

/-! ### (S2) Subadditivity -/

lemma kolmogorovNumber'_add_le (S T : X →L[𝕜] Y) (n : ℕ) :
    kolmogorovNumber' (S + T) n ≤ kolmogorovNumber' S n + ‖T‖ := by
  rw [← sub_le_iff_le_add]
  refine le_csInf (kSet_nonempty S n) ?_
  rintro _ ⟨V, hV, rfl⟩
  -- `V.mkQL.comp (S+T) = V.mkQL.comp S + V.mkQL.comp T`. Triangle:
  -- `‖V.mkQL.comp (S+T)‖ ≤ ‖V.mkQL.comp S‖ + ‖V.mkQL.comp T‖ ≤ deviation S V + ‖T‖`.
  have h_dist : kolmogorovNumber' (S + T) n
      ≤ deviationFromSubspace' S V + deviationFromSubspace' T V := by
    refine (kolmogorovNumber'_le_deviation hV).trans ?_
    unfold deviationFromSubspace'
    have h_eq : V.mkQL.comp (S + T) = V.mkQL.comp S + V.mkQL.comp T :=
      ContinuousLinearMap.comp_add _ _ _
    rw [h_eq]
    exact norm_add_le (V.mkQL.comp S) (V.mkQL.comp T)
  have h_T : deviationFromSubspace' T V ≤ ‖T‖ := deviationFromSubspace'_le_norm T V
  linarith

/-! ### (S3) Ideal property — the main payoff

The quotient formulation lets us factor

  `(B(V)).mkQL ∘ B = B̃ ∘ V.mkQL`

where `B̃ = V.liftQL ((B(V)).mkQL.comp B) _` is the descended map
`Y/V →L[𝕜] Z/B(V)`. Since `‖B̃‖ ≤ ‖(B(V)).mkQL.comp B‖ ≤ ‖B‖`, plain
operator-norm submultiplicativity finishes the job. No density of `‖𝕜‖`,
no ε. -/

/-- The natural lift of `B : Y →L[𝕜] Z` to a map between quotients. -/
private noncomputable def descend (B : Y →L[𝕜] Z) (V : Submodule 𝕜 Y) :
    (Y ⧸ V) →L[𝕜] (Z ⧸ V.map (B : Y →ₗ[𝕜] Z)) :=
  V.liftQL ((V.map (B : Y →ₗ[𝕜] Z)).mkQL.comp B) <| by
    intro y hy
    show ((V.map (B : Y →ₗ[𝕜] Z)).mkQL.comp B) y = 0
    show (V.map (B : Y →ₗ[𝕜] Z)).mkQL (B y) = 0
    rw [Submodule.mkQL_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact ⟨y, hy, rfl⟩

private lemma descend_apply (B : Y →L[𝕜] Z) (V : Submodule 𝕜 Y) (y : Y) :
    descend B V (V.mkQL y) = (V.map (B : Y →ₗ[𝕜] Z)).mkQL (B y) := by
  show V.liftQL ((V.map (B : Y →ₗ[𝕜] Z)).mkQL.comp B) _ (V.mkQL y) = _
  rw [V.liftQL_mkQL]
  rfl

private lemma descend_factor (B : Y →L[𝕜] Z) (V : Submodule 𝕜 Y) :
    (V.map (B : Y →ₗ[𝕜] Z)).mkQL.comp B = (descend B V).comp V.mkQL := by
  ext y
  show (V.map (B : Y →ₗ[𝕜] Z)).mkQL (B y) = descend B V (V.mkQL y)
  rw [descend_apply]

private lemma norm_descend_le (B : Y →L[𝕜] Z) (V : Submodule 𝕜 Y) :
    ‖descend B V‖ ≤ ‖B‖ := by
  refine (V.norm_liftQL_le _ _).trans ?_
  calc ‖(V.map (B : Y →ₗ[𝕜] Z)).mkQL.comp B‖
      ≤ ‖(V.map (B : Y →ₗ[𝕜] Z)).mkQL‖ * ‖B‖ := opNorm_comp_le _ _
    _ ≤ 1 * ‖B‖ :=
        mul_le_mul_of_nonneg_right (V.map (B : Y →ₗ[𝕜] Z)).norm_mkQL_le (norm_nonneg _)
    _ = ‖B‖ := one_mul _

/-- Per-subspace (S3) bound:
`deviation(B ∘ S ∘ A, B(V)) ≤ ‖B‖ * ‖A‖ * deviation(S, V)`.

Pure operator-norm submultiplicativity — no `DenselyNormedField` needed. -/
lemma deviationFromSubspace'_comp_comp_map_le
    (A : W →L[𝕜] X) (S : X →L[𝕜] Y) (B : Y →L[𝕜] Z) (V : Submodule 𝕜 Y) :
    deviationFromSubspace' (B.comp (S.comp A)) (V.map (B : Y →ₗ[𝕜] Z))
      ≤ ‖B‖ * ‖A‖ * deviationFromSubspace' S V := by
  unfold deviationFromSubspace'
  -- Factor: `(B(V)).mkQL ∘ B ∘ S ∘ A = (descend B V) ∘ V.mkQL ∘ S ∘ A`.
  have h_factor : (V.map (B : Y →ₗ[𝕜] Z)).mkQL.comp (B.comp (S.comp A))
      = (descend B V).comp ((V.mkQL.comp S).comp A) := by
    have : (V.map (B : Y →ₗ[𝕜] Z)).mkQL.comp (B.comp (S.comp A))
         = ((V.map (B : Y →ₗ[𝕜] Z)).mkQL.comp B).comp (S.comp A) := by
      ext; simp [coe_comp', Function.comp_apply]
    rw [this, descend_factor]
    ext; simp [coe_comp', Function.comp_apply]
  rw [h_factor]
  -- Submultiplicativity twice.
  calc ‖(descend B V).comp ((V.mkQL.comp S).comp A)‖
      ≤ ‖descend B V‖ * ‖(V.mkQL.comp S).comp A‖ := opNorm_comp_le _ _
    _ ≤ ‖B‖ * ‖(V.mkQL.comp S).comp A‖ :=
        mul_le_mul_of_nonneg_right (norm_descend_le B V)
          (norm_nonneg ((V.mkQL.comp S).comp A))
    _ ≤ ‖B‖ * (‖V.mkQL.comp S‖ * ‖A‖) :=
        mul_le_mul_of_nonneg_left (opNorm_comp_le _ _) (norm_nonneg _)
    _ = ‖B‖ * ‖A‖ * ‖V.mkQL.comp S‖ := by ring

lemma kolmogorovNumber'_comp_comp_le
    (A : W →L[𝕜] X) (S : X →L[𝕜] Y) (B : Y →L[𝕜] Z) (n : ℕ) :
    kolmogorovNumber' (B.comp (S.comp A)) n ≤
      ‖B‖ * kolmogorovNumber' S n * ‖A‖ := by
  -- Same scalar-pull-out trick as for the approximation numbers, but the
  -- per-subspace bound is now a one-line consequence of operator-norm
  -- submultiplicativity.
  have hkey : ∀ V : Submodule 𝕜 Y, Module.rank 𝕜 V ≤ (n : Cardinal) →
      kolmogorovNumber' (B.comp (S.comp A)) n ≤ ‖B‖ * ‖A‖ * deviationFromSubspace' S V :=
    fun V hV =>
      (kolmogorovNumber'_le_deviation ((rank_map_le _ _).trans hV)).trans
        (deviationFromSubspace'_comp_comp_map_le A S B V)
  have h_inf : kolmogorovNumber' (B.comp (S.comp A)) n
                ≤ ‖B‖ * ‖A‖ * kolmogorovNumber' S n := by
    show _ ≤ (‖B‖ * ‖A‖) • sInf
      {r | ∃ V : Submodule 𝕜 Y,
            Module.rank 𝕜 V ≤ (n : Cardinal) ∧ r = deviationFromSubspace' S V}
    rw [← Real.sInf_smul_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))]
    refine le_csInf ((kSet_nonempty S n).image _) ?_
    rintro _ ⟨_, ⟨V, hV, rfl⟩, rfl⟩
    exact hkey V hV
  exact h_inf.trans_eq (by ring)

/-! ### (S1a) Value at `n = 0`: `kolmogorovNumber' S 0 = ‖S‖`

The bound `‖V.mkQL ∘ S‖ ≤ ‖S‖` holds in general (since `‖V.mkQL‖ ≤ 1`), but
the matching lower bound `‖S‖ ≤ ‖(⊥).mkQL ∘ S‖` requires that `Y ⧸ ⊥` is
isometric to `Y` — i.e. `‖[y]‖ = ‖y‖` for the trivial subspace. We get this
from `Submodule.Quotient.norm_mk_lt`: a representative `y'` of `[y]` with
`‖y'‖ < ‖[y]‖ + ε` must satisfy `y' - y ∈ ⊥`, i.e. `y' = y`. -/

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

private lemma deviationFromSubspace'_bot (S : X →L[𝕜] Y) :
    deviationFromSubspace' S (⊥ : Submodule 𝕜 Y) = ‖S‖ := by
  unfold deviationFromSubspace'
  refine le_antisymm ?_ ?_
  · -- `‖(⊥).mkQL ∘ S‖ ≤ ‖S‖`: pointwise `‖[S x]‖ = ‖S x‖ ≤ ‖S‖ * ‖x‖`.
    refine opNorm_le_bound _ (norm_nonneg _) fun x => ?_
    rw [coe_comp', Function.comp_apply, Submodule.mkQL_apply, norm_mk_bot]
    exact S.le_opNorm x
  · -- `‖S‖ ≤ ‖(⊥).mkQL ∘ S‖`: pointwise `‖S x‖ = ‖[S x]‖ ≤ ‖(⊥).mkQL ∘ S‖ * ‖x‖`.
    refine opNorm_le_bound _
      (norm_nonneg ((⊥ : Submodule 𝕜 Y).mkQL.comp S)) fun x => ?_
    rw [← norm_mk_bot (𝕜 := 𝕜) (S x)]
    change ‖((⊥ : Submodule 𝕜 Y).mkQL.comp S) x‖ ≤ _
    exact ((⊥ : Submodule 𝕜 Y).mkQL.comp S).le_opNorm x

lemma kolmogorovNumber'_zero_eq_norm (S : X →L[𝕜] Y) :
    kolmogorovNumber' S 0 = ‖S‖ := by
  refine le_antisymm ?_ ?_
  · have h_rank : Module.rank 𝕜 (⊥ : Submodule 𝕜 Y) ≤ ((0 : ℕ) : Cardinal) := by
      rw [rank_bot]; exact_mod_cast Nat.zero_le 0
    exact (kolmogorovNumber'_le_deviation h_rank).trans_eq (deviationFromSubspace'_bot S)
  · refine le_csInf (kSet_nonempty S 0) ?_
    rintro _ ⟨V, hV, rfl⟩
    have hV_bot : V = ⊥ := by
      rw [← Submodule.rank_eq_zero]
      exact le_antisymm (by exact_mod_cast hV) (Cardinal.zero_le _)
    rw [hV_bot, deviationFromSubspace'_bot]

/-! ### (S5') Strict normalisation `kolmogorovNumber' (id_X) n = 1` whenever `dim X > n`

For any closed proper finite-dim `V ⊆ X`, Riesz's lemma gives
`x₀ ∉ V` with `(1 − ε) * ‖x₀‖ ≤ ‖x₀ − y‖` for every `y ∈ V`. The infimum
on the RHS is exactly `‖V.mkQL x₀‖`. Combining with `le_opNorm` and
cancelling `‖x₀‖ > 0` gives `(1 − ε) ≤ ‖V.mkQL‖`. Letting ε → 0 finishes
the lower bound. The upper bound `‖V.mkQL.comp id‖ = ‖V.mkQL‖ ≤ 1` is
already in `Submodule.norm_mkQL_le`.

No second density-rescaling step. -/

variable [CompleteSpace 𝕜]

private lemma one_le_norm_mkQL_of_proper {X : Type u} [NormedAddCommGroup X]
    [NormedSpace 𝕜 X] {V : Submodule 𝕜 X} [FiniteDimensional 𝕜 V] (hV_ne_top : V ≠ ⊤) :
    (1 : ℝ) ≤ ‖V.mkQL‖ := by
  have hV_closed : IsClosed (V : Set X) := V.closed_of_finiteDimensional
  have hV_exists : ∃ x : X, x ∉ V := SetLike.exists_not_mem_of_ne_top V hV_ne_top
  refine le_of_mul_one_sub_le_of_nonneg (by norm_num : (0 : ℝ) ≤ 1) ?_
  intro ε _ hε1
  rw [one_mul]
  have h_aux : (1 - ε : ℝ) < 1 := by linarith
  obtain ⟨x₀, hx₀_ne, hx₀_dist⟩ := riesz_lemma hV_closed hV_exists h_aux
  have hx₀_ne_zero : x₀ ≠ 0 := fun h0 => hx₀_ne (h0 ▸ V.zero_mem)
  have hx₀_norm_pos : 0 < ‖x₀‖ := norm_pos_iff.mpr hx₀_ne_zero
  -- `‖V.mkQL x₀‖ = ‖[x₀]‖ ≥ (1 - ε) * ‖x₀‖`.
  have h_quot_ge : (1 - ε) * ‖x₀‖ ≤ ‖V.mkQL x₀‖ := by
    -- `‖V.mkQL x₀‖ = ‖((x₀ : X) : X ⧸ V.toAddSubgroup)‖ = infDist x₀ V` via `norm_mk`.
    have h_norm_eq : ‖V.mkQL x₀‖ = Metric.infDist x₀ V :=
      QuotientAddGroup.norm_mk (S := V.toAddSubgroup) x₀
    rw [h_norm_eq, Metric.le_infDist ⟨0, V.zero_mem⟩]
    intro y hy
    rw [dist_eq_norm]
    exact hx₀_dist y hy
  -- `‖V.mkQL‖ * ‖x₀‖ ≥ ‖V.mkQL x₀‖ ≥ (1 - ε) * ‖x₀‖`, then cancel `‖x₀‖`.
  have h_op : ‖V.mkQL x₀‖ ≤ ‖V.mkQL‖ * ‖x₀‖ := V.mkQL.le_opNorm x₀
  have h_chain : (1 - ε) * ‖x₀‖ ≤ ‖V.mkQL‖ * ‖x₀‖ := h_quot_ge.trans h_op
  exact le_of_mul_le_mul_right h_chain hx₀_norm_pos

/-- (S5') Strict normalisation: `kolmogorovNumber' (id_X) n = 1` whenever
`n < Module.finrank 𝕜 X`. -/
lemma kolmogorovNumber'_strict {X : Type u} [NormedAddCommGroup X]
    [NormedSpace 𝕜 X] (n : ℕ) (h : n < Module.finrank 𝕜 X) :
    kolmogorovNumber' (ContinuousLinearMap.id 𝕜 X) n = 1 := by
  have h_finrank_pos : 0 < Module.finrank 𝕜 X :=
    Nat.lt_of_le_of_lt (Nat.zero_le _) h
  haveI : FiniteDimensional 𝕜 X := .of_finrank_pos h_finrank_pos
  haveI : Nontrivial X := Module.nontrivial_of_finrank_pos h_finrank_pos
  set I := ContinuousLinearMap.id 𝕜 X with hI_def
  refine le_antisymm ?_ ?_
  · -- `≤ 1`: take `V = ⊥`. `deviation(I, ⊥) = ‖I‖ = 1`.
    have h_rank_bot : Module.rank 𝕜 (⊥ : Submodule 𝕜 X) ≤ (n : Cardinal) := by
      rw [rank_bot]; exact Cardinal.zero_le _
    calc kolmogorovNumber' I n
        ≤ deviationFromSubspace' I ⊥ := kolmogorovNumber'_le_deviation h_rank_bot
      _ = ‖I‖ := deviationFromSubspace'_bot _
      _ = 1 := norm_id
  · -- `≥ 1`: every admissible `V` is proper, so `‖V.mkQL‖ ≥ 1`, and
    -- `deviation(I, V) = ‖V.mkQL.comp I‖ = ‖V.mkQL‖`.
    refine le_csInf (kSet_nonempty I n) ?_
    rintro _ ⟨V, hV, rfl⟩
    have hV_finrank_le : Module.finrank 𝕜 V ≤ n := Module.finrank_le_of_rank_le hV
    have hV_finrank_lt : Module.finrank 𝕜 V < Module.finrank 𝕜 X :=
      lt_of_le_of_lt hV_finrank_le h
    have hV_ne_top : V ≠ ⊤ := by
      intro h_top
      rw [h_top, finrank_top] at hV_finrank_lt
      exact lt_irrefl _ hV_finrank_lt
    haveI : FiniteDimensional 𝕜 V := FiniteDimensional.finiteDimensional_submodule V
    have h_dev_eq : deviationFromSubspace' I V = ‖V.mkQL‖ := by
      show ‖V.mkQL.comp I‖ = ‖V.mkQL‖
      rw [hI_def, ContinuousLinearMap.comp_id]
    rw [h_dev_eq]
    exact one_le_norm_mkQL_of_proper hV_ne_top

/-- (S5) Normalisation on `id_{ℓ₂^{n+1}}`: a special case of (S5'). -/
lemma kolmogorovNumber'_id_euclidean (n : ℕ) :
    kolmogorovNumber'
      (ContinuousLinearMap.id 𝕜 (EuclideanSpace 𝕜 (Fin (n + 1)))) n = 1 := by
  have h_finrank : Module.finrank 𝕜 (EuclideanSpace 𝕜 (Fin (n + 1))) = n + 1 := by
    rw [(WithLp.linearEquiv 2 𝕜 (Fin (n + 1) → 𝕜)).finrank_eq, Module.finrank_pi 𝕜]
    exact Fintype.card_fin _
  have h : n < Module.finrank 𝕜 (EuclideanSpace 𝕜 (Fin (n + 1))) := by
    rw [h_finrank]; exact Nat.lt_succ_self n
  exact kolmogorovNumber'_strict n h

/-! ### Summary: Kolmogorov numbers (quotient form) form a strict s-number sequence -/

theorem isSNumberSequence_kolmogorovNumber' :
    IsSNumberSequence (𝕜 := 𝕜)
        (fun {_X _Y} _ _ _ _ S n => kolmogorovNumber' S n) where
  nonneg := fun S n => kolmogorovNumber'_nonneg S n
  norm_at_zero := fun S => kolmogorovNumber'_zero_eq_norm S
  antitone := fun S n => kolmogorovNumber'_antitone S n
  subadditive := fun S T n => kolmogorovNumber'_add_le S T n
  ideal := fun A S B n => kolmogorovNumber'_comp_comp_le A S B n
  vanishes_on_low_rank := fun _ _ h => kolmogorovNumber'_eq_zero_of_rank_le h
  normalised_at_id := fun n => kolmogorovNumber'_id_euclidean n

theorem isStrictSNumberSequence_kolmogorovNumber' :
    IsStrictSNumberSequence (𝕜 := 𝕜)
        (fun {_X _Y} _ _ _ _ S n => kolmogorovNumber' S n) where
  toIsSNumberSequence := isSNumberSequence_kolmogorovNumber'
  strictly_normalised_at_id := fun n h => kolmogorovNumber'_strict n h

end SNumbers
