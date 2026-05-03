/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
import SNumbers.Helpers
import Mathlib.LinearAlgebra.Dimension.RankNullity

/-!
# Bernstein numbers `b_n`

The Bernstein numbers `b_n S` of a continuous linear map `S : X →L[𝕜] Y`
between normed `𝕜`-vector spaces measure the *largest* possible
"smallest gain" of `S` on an `(n+1)`-dimensional subspace of the domain:

  `b_n S = sup_{M ⊆ X, dim M = n+1} inf_{x ∈ M, x ≠ 0} ‖S x‖ / ‖x‖`,

i.e. the largest constant `c ≥ 0` with the property that there exists an
`(n+1)`-dimensional subspace `M ⊆ X` on which `S` is bounded below by
`c · ‖·‖`.

## Structure

The Bernstein numbers are the *smallest* of the canonical s-numbers (and
are sandwiched between the Hilbert and approximation numbers via
Pietsch's sandwich theorem). They form a strict s-number sequence:
(S1)–(S5)+(S5'). The proofs follow Pietsch and use a single nontrivial
case split — for (S3), we split on whether the outer map `A : W →L[𝕜] X`
is injective on the chosen `(n+1)`-dim subspace `M ⊆ W`. In the
non-injective case the gain on `M` is forced to `0`; in the injective
case `A.M` is itself an `(n+1)`-dim subspace of `X` and the per-vector
inequality `‖B(S(A x))‖ / ‖x‖ ≤ ‖B‖ · ‖A‖ · ‖S(A x)‖ / ‖A x‖` does
the rest.

The development requires only `[NontriviallyNormedField 𝕜]` — no Riesz,
no `[CompleteSpace 𝕜]`, no `[CompleteSpace X]`.
-/

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

/-- The smallest gain `inf_{x ∈ M, x ≠ 0} ‖S x‖ / ‖x‖` of an operator `S` on
a subspace `M`. By the conventional `sInf ∅ = 0` for `ℝ`, this is `0`
when `M = ⊥`. -/
noncomputable def gainOnSubspace (S : X →L[𝕜] Y) (M : Submodule 𝕜 X) : ℝ :=
  sInf {r | ∃ x : X, x ∈ M ∧ x ≠ 0 ∧ r = ‖S x‖ / ‖x‖}

/-- The `n`-th **Bernstein number** of a continuous linear map.

`b_n S = sup_{M ⊆ X, dim M = n + 1} gainOnSubspace S M`. -/
noncomputable def bernsteinNumber (S : X →L[𝕜] Y) (n : ℕ) : ℝ :=
  sSup {r | ∃ M : Submodule 𝕜 X,
      Module.rank 𝕜 M = (n + 1 : ℕ) ∧ r = gainOnSubspace S M}

/-! ### Basic facts about `gainOnSubspace` -/

private lemma gainSet_bddBelow (S : X →L[𝕜] Y) (M : Submodule 𝕜 X) :
    BddBelow {r : ℝ | ∃ x : X, x ∈ M ∧ x ≠ 0 ∧ r = ‖S x‖ / ‖x‖} :=
  ⟨0, by rintro _ ⟨_, _, _, rfl⟩; exact div_nonneg (norm_nonneg _) (norm_nonneg _)⟩

private lemma gainSet_nonempty_of_ne_bot (S : X →L[𝕜] Y) {M : Submodule 𝕜 X}
    (hM : M ≠ ⊥) :
    {r : ℝ | ∃ x : X, x ∈ M ∧ x ≠ 0 ∧ r = ‖S x‖ / ‖x‖}.Nonempty := by
  obtain ⟨x, hx_mem, hx_ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hM
  exact ⟨_, x, hx_mem, hx_ne, rfl⟩

lemma gainOnSubspace_nonneg (S : X →L[𝕜] Y) (M : Submodule 𝕜 X) :
    0 ≤ gainOnSubspace S M :=
  Real.sInf_nonneg fun _ ⟨_, _, _, hr⟩ =>
    hr.symm ▸ div_nonneg (norm_nonneg _) (norm_nonneg _)

/-- Pointwise upper bound: every nonzero `x ∈ M` upper-bounds the gain. -/
lemma gainOnSubspace_le_div {S : X →L[𝕜] Y} {M : Submodule 𝕜 X} {x : X}
    (hx_mem : x ∈ M) (hx_ne : x ≠ 0) :
    gainOnSubspace S M ≤ ‖S x‖ / ‖x‖ :=
  csInf_le (gainSet_bddBelow S M) ⟨x, hx_mem, hx_ne, rfl⟩

/-- Lower bound on the gain: if every nonzero `x ∈ M` satisfies
`c ≤ ‖S x‖/‖x‖`, then `c ≤ gainOnSubspace S M`. -/
lemma le_gainOnSubspace {S : X →L[𝕜] Y} {M : Submodule 𝕜 X} (hM : M ≠ ⊥)
    {c : ℝ} (h : ∀ x ∈ M, x ≠ 0 → c ≤ ‖S x‖ / ‖x‖) :
    c ≤ gainOnSubspace S M := by
  refine le_csInf (gainSet_nonempty_of_ne_bot S hM) ?_
  rintro _ ⟨x, hx_mem, hx_ne, rfl⟩
  exact h x hx_mem hx_ne

lemma gainOnSubspace_le_norm (S : X →L[𝕜] Y) (M : Submodule 𝕜 X) :
    gainOnSubspace S M ≤ ‖S‖ := by
  by_cases hM : M = ⊥
  · -- gainSet is empty when `M = ⊥`, so `sInf = 0 ≤ ‖S‖`.
    have h_empty : {r : ℝ | ∃ x : X, x ∈ M ∧ x ≠ 0 ∧ r = ‖S x‖ / ‖x‖} = ∅ := by
      ext r
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_exists]
      rintro x ⟨hx_mem, hx_ne, _⟩
      exact hx_ne (by rwa [hM, Submodule.mem_bot] at hx_mem)
    show sInf _ ≤ ‖S‖
    rw [h_empty, Real.sInf_empty]; exact norm_nonneg _
  · obtain ⟨x, hx_mem, hx_ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hM
    exact (gainOnSubspace_le_div hx_mem hx_ne).trans (S.ratio_le_opNorm x)

/-! ### Helpers for the supremum set defining `bernsteinNumber` -/

private lemma bSet_bddAbove (S : X →L[𝕜] Y) (n : ℕ) :
    BddAbove {r : ℝ | ∃ M : Submodule 𝕜 X,
        Module.rank 𝕜 M = (n + 1 : ℕ) ∧ r = gainOnSubspace S M} :=
  ⟨‖S‖, by rintro _ ⟨M, _, rfl⟩; exact gainOnSubspace_le_norm S M⟩

/-- The `(n+1)`-rank constraint forces `M ≠ ⊥`. -/
private lemma rank_eq_succ_implies_ne_bot {M : Submodule 𝕜 X} {n : ℕ}
    (hM_rank : Module.rank 𝕜 M = ((n + 1 : ℕ) : Cardinal)) :
    M ≠ ⊥ := fun hM_bot => by
  rw [hM_bot, rank_bot] at hM_rank
  exact Nat.succ_ne_zero n (by exact_mod_cast hM_rank.symm)

/-- Rank of the span of an `n`-element linearly independent family. -/
private lemma rank_span_range_fin {V : Type u} [AddCommGroup V] [Module 𝕜 V]
    {n : ℕ} {g : Fin n → V} (hg : LinearIndependent 𝕜 g) :
    Module.rank 𝕜 (Submodule.span 𝕜 (Set.range g)) = (n : Cardinal) := by
  classical
  haveI : Fintype (Set.range g) := Set.fintypeRange g
  rw [rank_span hg, Cardinal.mk_fintype, Set.card_range_of_injective hg.injective,
      Fintype.card_fin]

lemma bernsteinNumber_le_norm (S : X →L[𝕜] Y) (n : ℕ) :
    bernsteinNumber S n ≤ ‖S‖ :=
  Real.sSup_le (fun _ ⟨M, _, hr⟩ => hr.symm ▸ gainOnSubspace_le_norm S M)
    (norm_nonneg _)

/-! ## (S1c) Non-negativity -/

lemma bernsteinNumber_nonneg (S : X →L[𝕜] Y) (n : ℕ) :
    0 ≤ bernsteinNumber S n :=
  Real.sSup_nonneg <| by rintro _ ⟨M, _, rfl⟩; exact gainOnSubspace_nonneg S M

/-! ## (S1a) Value at `n = 0`: `bernsteinNumber S 0 = ‖S‖`

For `n = 0`, `dim M = 1`, so `M = span {v}` for some `v ≠ 0`. Then every
`x ∈ M, x ≠ 0` is `x = c · v` for some scalar `c ≠ 0`, and
`‖S x‖/‖x‖ = ‖S v‖/‖v‖`. Hence `gainOnSubspace S M = ‖S v‖/‖v‖`, and
the supremum over 1-dim subspaces equals `sup_v ‖S v‖/‖v‖ = ‖S‖`. -/

/-- For a one-dimensional subspace `M = span {v}` with `v ≠ 0`,
`gainOnSubspace S M = ‖S v‖ / ‖v‖`. -/
private lemma gainOnSubspace_span_singleton {S : X →L[𝕜] Y} {v : X} (hv_ne : v ≠ 0) :
    gainOnSubspace S (Submodule.span 𝕜 {v}) = ‖S v‖ / ‖v‖ := by
  set M : Submodule 𝕜 X := Submodule.span 𝕜 {v}
  have hv_mem : v ∈ M := Submodule.subset_span (Set.mem_singleton _)
  have hM_ne_bot : M ≠ ⊥ := fun hM_bot =>
    hv_ne (by rwa [hM_bot, Submodule.mem_bot] at hv_mem)
  refine le_antisymm (gainOnSubspace_le_div hv_mem hv_ne) ?_
  refine le_gainOnSubspace hM_ne_bot ?_
  rintro _ hx_mem hx_ne
  rw [Submodule.mem_span_singleton] at hx_mem
  obtain ⟨c, rfl⟩ := hx_mem
  have hc_ne : c ≠ 0 := fun hc => hx_ne (by rw [hc, zero_smul])
  rw [map_smul, norm_smul, norm_smul,
      mul_div_mul_left _ _ (norm_ne_zero_iff.mpr hc_ne)]

@[simp] lemma bernsteinNumber_zero_eq_norm (S : X →L[𝕜] Y) :
    bernsteinNumber S 0 = ‖S‖ := by
  refine le_antisymm (bernsteinNumber_le_norm S 0) ?_
  -- For each `v` with `‖v‖ ≠ 0`, the 1-dim subspace `span {v}` realises
  -- the gain `‖S v‖/‖v‖`, which is therefore `≤ b_0 S`.
  refine opNorm_le_bound' _ (bernsteinNumber_nonneg S 0) fun v hv_norm => ?_
  have hv_ne : v ≠ 0 := norm_ne_zero_iff.mp hv_norm
  have hv_pos : 0 < ‖v‖ := norm_pos_iff.mpr hv_ne
  have hM_rank : Module.rank 𝕜 (Submodule.span 𝕜 ({v} : Set X)) = ((0 + 1 : ℕ) : Cardinal) := by
    rw [rank_span_set (LinearIndepOn.singleton hv_ne), Cardinal.mk_singleton]; norm_cast
  have h_le : gainOnSubspace S (Submodule.span 𝕜 ({v} : Set X)) ≤ bernsteinNumber S 0 :=
    le_csSup (bSet_bddAbove S 0) ⟨_, hM_rank, rfl⟩
  rw [gainOnSubspace_span_singleton hv_ne, div_le_iff₀ hv_pos] at h_le
  linarith

/-! ## (S1b) Antitone in `n` -/

/-- Restricting the gain to a subspace `M' ⊆ M` only increases it (smaller
inf-domain). -/
lemma gainOnSubspace_anti {S : X →L[𝕜] Y} {M M' : Submodule 𝕜 X}
    (h_le : M' ≤ M) (hM' : M' ≠ ⊥) :
    gainOnSubspace S M ≤ gainOnSubspace S M' := by
  refine csInf_le_csInf (gainSet_bddBelow S M)
    (gainSet_nonempty_of_ne_bot S hM') ?_
  rintro _ ⟨x, hx_mem', hx_ne, rfl⟩
  exact ⟨x, h_le hx_mem', hx_ne, rfl⟩

lemma bernsteinNumber_antitone (S : X →L[𝕜] Y) (n : ℕ) :
    bernsteinNumber S (n + 1) ≤ bernsteinNumber S n := by
  refine Real.sSup_le ?_ (bernsteinNumber_nonneg S n)
  rintro _ ⟨M, hM_rank, rfl⟩
  -- `M` has rank `n + 2`. Pick an `(n+1)`-dim subspace `M' ⊆ M`.
  have hM_rank' : ((n + 1 : ℕ) : Cardinal) ≤ Module.rank 𝕜 M := by
    rw [hM_rank]; exact_mod_cast Nat.le_succ _
  obtain ⟨f, hf_li⟩ := exists_linearIndependent_of_le_rank hM_rank'
  set g : Fin (n + 1) → X := fun i => (f i : X) with hg_def
  have hg_li : LinearIndependent 𝕜 g :=
    (M.subtype.linearIndependent_iff (Submodule.ker_subtype M)).mpr hf_li
  set M' : Submodule 𝕜 X := Submodule.span 𝕜 (Set.range g) with hM'_def
  have hM'_rank : Module.rank 𝕜 M' = ((n + 1 : ℕ) : Cardinal) :=
    rank_span_range_fin hg_li
  have hM'_le : M' ≤ M := by
    rw [hM'_def]
    exact Submodule.span_le.mpr <| by rintro _ ⟨i, rfl⟩; exact (f i).2
  calc gainOnSubspace S M
      ≤ gainOnSubspace S M' :=
        gainOnSubspace_anti hM'_le (rank_eq_succ_implies_ne_bot hM'_rank)
    _ ≤ bernsteinNumber S n := le_csSup (bSet_bddAbove S n) ⟨M', hM'_rank, rfl⟩

/-! ## (S2) Subadditivity -/

private lemma gainOnSubspace_add_le (S T : X →L[𝕜] Y) {M : Submodule 𝕜 X}
    (hM : M ≠ ⊥) :
    gainOnSubspace (S + T) M ≤ gainOnSubspace S M + ‖T‖ := by
  rw [← sub_le_iff_le_add]
  refine le_gainOnSubspace hM ?_
  intro x hx_mem hx_ne
  have hx_pos : 0 < ‖x‖ := norm_pos_iff.mpr hx_ne
  -- `‖(S+T) x‖ / ‖x‖ ≤ ‖S x‖/‖x‖ + ‖T‖`, then chain through `gain (S+T) M`.
  have h_div : ‖(S + T) x‖ / ‖x‖ ≤ ‖S x‖ / ‖x‖ + ‖T‖ := by
    rw [show ‖S x‖ / ‖x‖ + ‖T‖ = (‖S x‖ + ‖T‖ * ‖x‖) / ‖x‖ from by
          rw [add_div, mul_div_cancel_right₀ _ hx_pos.ne'],
        div_le_div_iff_of_pos_right hx_pos]
    calc ‖(S + T) x‖
        = ‖S x + T x‖ := by rw [ContinuousLinearMap.add_apply]
      _ ≤ ‖S x‖ + ‖T x‖ := norm_add_le _ _
      _ ≤ ‖S x‖ + ‖T‖ * ‖x‖ := by linarith [T.le_opNorm x]
  linarith [gainOnSubspace_le_div (S := S + T) hx_mem hx_ne]

lemma bernsteinNumber_add_le (S T : X →L[𝕜] Y) (n : ℕ) :
    bernsteinNumber (S + T) n ≤ bernsteinNumber S n + ‖T‖ := by
  refine Real.sSup_le ?_
    (add_nonneg (bernsteinNumber_nonneg S n) (norm_nonneg _))
  rintro _ ⟨M, hM_rank, rfl⟩
  have h1 : gainOnSubspace (S + T) M ≤ gainOnSubspace S M + ‖T‖ :=
    gainOnSubspace_add_le S T (rank_eq_succ_implies_ne_bot hM_rank)
  have h2 : gainOnSubspace S M ≤ bernsteinNumber S n :=
    le_csSup (bSet_bddAbove S n) ⟨M, hM_rank, rfl⟩
  linarith

/-! ## (S4) Vanishing on operators of rank at most `n`

If `rank S ≤ n`, then for every `M ⊆ X` with `dim M = n + 1`, the
restriction `S|_M` has rank `≤ rank S ≤ n < n + 1 = dim M`, so by
rank-nullity `S` has a nontrivial kernel inside `M`. Picking
`x ∈ M ∩ ker S` with `x ≠ 0` gives `‖S x‖/‖x‖ = 0` in the gain set,
hence `gainOnSubspace S M = 0`. The supremum over `M` is then `0`. -/

lemma bernsteinNumber_eq_zero_of_rank_le {S : X →L[𝕜] Y} {n : ℕ}
    (hS : S.rank ≤ (n : Cardinal)) :
    bernsteinNumber S n = 0 := by
  refine le_antisymm ?_ (bernsteinNumber_nonneg S n)
  refine Real.sSup_le ?_ le_rfl
  rintro _ ⟨M, hM_rank, rfl⟩
  -- We claim `gainOnSubspace S M ≤ 0`. Find `x ∈ M ∩ ker S` with `x ≠ 0`
  -- via rank-nullity on `f := S.domRestrict M : M →ₗ Y`.
  set f : M →ₗ[𝕜] Y := (S : X →ₗ[𝕜] Y).domRestrict M
  have h_rank_f_le : Module.rank 𝕜 (LinearMap.range f) ≤ (n : Cardinal) :=
    (Submodule.rank_mono <| by rintro _ ⟨x, rfl⟩; exact ⟨x, rfl⟩).trans hS
  have h_split :
      Module.rank 𝕜 (LinearMap.range f) + Module.rank 𝕜 (LinearMap.ker f)
        = Module.rank 𝕜 M := LinearMap.rank_range_add_rank_ker f
  -- `dim ker f ≥ 1` from the rank decomposition.
  have h_ker_pos : 0 < Module.rank 𝕜 (LinearMap.ker f) := by
    rw [hM_rank] at h_split
    by_contra h_le
    have h_zero : Module.rank 𝕜 (LinearMap.ker f) = 0 :=
      le_antisymm (not_lt.mp h_le) bot_le
    rw [h_zero, add_zero] at h_split
    have : (n + 1 : ℕ) ≤ (n : ℕ) := by
      exact_mod_cast h_split.symm.trans_le h_rank_f_le
    omega
  have h_ker_ne_bot : LinearMap.ker f ≠ ⊥ := fun h => by
    rw [h, rank_bot] at h_ker_pos; exact lt_irrefl _ h_ker_pos
  obtain ⟨⟨x, hx_mem⟩, hx_ker, hx_ne⟩ :=
    Submodule.exists_mem_ne_zero_of_ne_bot h_ker_ne_bot
  have hx_ne_zero : x ≠ 0 := fun h => hx_ne (by ext; exact h)
  have hSx : S x = 0 := hx_ker
  have h_zero_in :
      (0 : ℝ) ∈ {r : ℝ | ∃ y, y ∈ M ∧ y ≠ 0 ∧ r = ‖S y‖ / ‖y‖} :=
    ⟨x, hx_mem, hx_ne_zero, by rw [hSx, norm_zero, zero_div]⟩
  exact csInf_le (gainSet_bddBelow S M) h_zero_in

/-! ## (S5') Strict normalisation `b_n (id_X) = 1` whenever `dim X > n`

For `id_X`, every nonzero `x` satisfies `‖x‖ / ‖x‖ = 1`. Hence
`gainOnSubspace id_X M = 1` for every `M ≠ ⊥`. The supremum over
`(n+1)`-dim subspaces is then `1`, provided at least one such subspace
exists (which holds iff `dim X > n`). -/

private lemma gainOnSubspace_id_eq_one {M : Submodule 𝕜 X} (hM : M ≠ ⊥) :
    gainOnSubspace (ContinuousLinearMap.id 𝕜 X) M = 1 := by
  refine le_antisymm ?_ ?_
  · obtain ⟨x, hx_mem, hx_ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hM
    have hx_pos : 0 < ‖x‖ := norm_pos_iff.mpr hx_ne
    refine (gainOnSubspace_le_div (S := ContinuousLinearMap.id 𝕜 X)
      hx_mem hx_ne).trans_eq ?_
    rw [ContinuousLinearMap.id_apply, div_self hx_pos.ne']
  · refine le_gainOnSubspace hM ?_
    intro x _ hx_ne
    rw [ContinuousLinearMap.id_apply, div_self (norm_pos_iff.mpr hx_ne).ne']

/-- (S5') Strict normalisation: `bernsteinNumber (id_X) n = 1` whenever
`n < Module.finrank 𝕜 X`. -/
lemma bernsteinNumber_strict {X : Type u} [NormedAddCommGroup X]
    [NormedSpace 𝕜 X] (n : ℕ) (h : n < Module.finrank 𝕜 X) :
    bernsteinNumber (ContinuousLinearMap.id 𝕜 X) n = 1 := by
  haveI : FiniteDimensional 𝕜 X :=
    .of_finrank_pos (Nat.lt_of_le_of_lt (Nat.zero_le _) h)
  -- Construct an `(n+1)`-dim subspace `M ⊆ X`.
  obtain ⟨g, hg_li⟩ := exists_linearIndependent_of_le_finrank (h : n + 1 ≤ _)
  set M : Submodule 𝕜 X := Submodule.span 𝕜 (Set.range g)
  have hM_rank : Module.rank 𝕜 M = ((n + 1 : ℕ) : Cardinal) :=
    rank_span_range_fin hg_li
  refine le_antisymm ?_ ?_
  · -- `≤ 1`: every gain in `bSet` is `1`.
    refine Real.sSup_le ?_ zero_le_one
    rintro _ ⟨M', hM'_rank, rfl⟩
    rw [gainOnSubspace_id_eq_one (rank_eq_succ_implies_ne_bot hM'_rank)]
  · -- `≥ 1`: `M` is a witness with gain `= 1`.
    refine (le_of_eq (gainOnSubspace_id_eq_one
      (rank_eq_succ_implies_ne_bot hM_rank)).symm).trans ?_
    exact le_csSup (bSet_bddAbove _ n) ⟨M, hM_rank, rfl⟩

/-- (S5) Normalisation on `id_{ℓ₂^{n+1}}`: a special case of (S5'). -/
lemma bernsteinNumber_id_euclidean (n : ℕ) :
    bernsteinNumber
      (ContinuousLinearMap.id 𝕜 (EuclideanSpace 𝕜 (Fin (n + 1)))) n = 1 := by
  have h_finrank : Module.finrank 𝕜 (EuclideanSpace 𝕜 (Fin (n + 1))) = n + 1 := by
    rw [(WithLp.linearEquiv 2 𝕜 (Fin (n + 1) → 𝕜)).finrank_eq, Module.finrank_pi 𝕜]
    exact Fintype.card_fin _
  have h : n < Module.finrank 𝕜 (EuclideanSpace 𝕜 (Fin (n + 1))) := by
    rw [h_finrank]; exact Nat.lt_succ_self n
  exact bernsteinNumber_strict n h

/-! ## (S3) Ideal property

For `M ⊆ W` with `dim M = n+1`, split on whether `A : W →L X` is
injective on `M`:

* If not, some nonzero `x ∈ M` has `A x = 0`, hence `(BSA) x = 0`, so
  `gainOnSubspace (BSA) M = 0` and the bound is trivial.
* If yes, `M' := A.M ⊆ X` has `dim M' = n+1`, and the per-vector
  inequality
    `‖B(S(A x))‖ / ‖x‖ ≤ ‖B‖ · ‖A‖ · ‖S(A x)‖ / ‖A x‖`
  taken against the bijection `M ≃ M'` gives
  `gainOnSubspace (BSA) M ≤ ‖B‖ · ‖A‖ · gainOnSubspace S M'`. -/

/-- Per-subspace bound in the injective case. -/
private lemma gainOnSubspace_comp_comp_le_of_injective
    (A : W →L[𝕜] X) (S : X →L[𝕜] Y) (B : Y →L[𝕜] Z) {M : Submodule 𝕜 W}
    (hM : M ≠ ⊥) (h_inj : ∀ x ∈ M, x ≠ 0 → A x ≠ 0) :
    gainOnSubspace (B.comp (S.comp A)) M ≤
      ‖B‖ * ‖A‖ * gainOnSubspace S (M.map (A : W →ₗ[𝕜] X)) := by
  by_cases hBA : ‖B‖ * ‖A‖ = 0
  · -- `‖B‖ * ‖A‖ = 0`. Either `‖B‖ = 0` (so `B = 0` and `BSA = 0`), or
    -- `‖A‖ = 0` (which is incompatible with `M ≠ ⊥` and `h_inj`).
    rw [hBA, zero_mul]
    obtain ⟨x, hx_mem, hx_ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hM
    rcases mul_eq_zero.mp hBA with hB | hA
    · have hB_zero : B = 0 := norm_eq_zero.mp hB
      have h_zero : B.comp (S.comp A) = 0 := by rw [hB_zero, zero_comp]
      rw [h_zero]
      refine (gainOnSubspace_le_div (S := (0 : W →L[𝕜] Z)) hx_mem hx_ne).trans ?_
      rw [ContinuousLinearMap.zero_apply, norm_zero, zero_div]
    · exfalso
      apply h_inj x hx_mem hx_ne
      rw [norm_eq_zero.mp hA, ContinuousLinearMap.zero_apply]
  · -- `‖B‖ * ‖A‖ > 0`. The main case.
    have hBA_pos : 0 < ‖B‖ * ‖A‖ :=
      lt_of_le_of_ne (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (Ne.symm hBA)
    set M' : Submodule 𝕜 X := M.map (A : W →ₗ[𝕜] X)
    have hM'_ne_bot : M' ≠ ⊥ := by
      obtain ⟨x, hx_mem, hx_ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hM
      intro hM'_bot
      have : A x ∈ M' := ⟨x, hx_mem, rfl⟩
      rw [hM'_bot, Submodule.mem_bot] at this
      exact h_inj x hx_mem hx_ne this
    -- Show `gain (BSA) M / (‖B‖‖A‖) ≤ gain S M'`.
    suffices h_div :
        gainOnSubspace (B.comp (S.comp A)) M / (‖B‖ * ‖A‖) ≤
          gainOnSubspace S M' by
      rw [div_le_iff₀ hBA_pos] at h_div
      linarith [mul_comm (‖B‖ * ‖A‖) (gainOnSubspace S M')]
    refine le_gainOnSubspace hM'_ne_bot ?_
    rintro _ ⟨x, hx_mem, rfl⟩ hAx_ne
    -- `A x ≠ 0` ⇒ `x ≠ 0` (since `A 0 = 0`).
    have hx_ne : x ≠ 0 := fun h => hAx_ne (by rw [h, map_zero])
    have hAx_pos : 0 < ‖A x‖ := norm_pos_iff.mpr hAx_ne
    have hx_pos : 0 < ‖x‖ := norm_pos_iff.mpr hx_ne
    -- `‖(BSA) x‖/‖x‖ ≤ ‖B‖‖A‖ * ‖S(A x)‖/‖A x‖`.
    have h_per_vec :
        ‖(B.comp (S.comp A)) x‖ / ‖x‖ ≤
          ‖B‖ * ‖A‖ * (‖S (A x)‖ / ‖A x‖) := by
      rw [div_le_iff₀ hx_pos]
      calc ‖(B.comp (S.comp A)) x‖
          = ‖B (S (A x))‖ := rfl
        _ ≤ ‖B‖ * ‖S (A x)‖ := B.le_opNorm _
        _ = ‖B‖ * (‖S (A x)‖ / ‖A x‖) * ‖A x‖ := by
            rw [mul_assoc, div_mul_cancel₀ _ hAx_pos.ne']
        _ ≤ ‖B‖ * (‖S (A x)‖ / ‖A x‖) * (‖A‖ * ‖x‖) := by
            gcongr; exact A.le_opNorm x
        _ = ‖B‖ * ‖A‖ * (‖S (A x)‖ / ‖A x‖) * ‖x‖ := by ring
    rw [div_le_iff₀ hBA_pos]
    calc gainOnSubspace (B.comp (S.comp A)) M
        ≤ ‖(B.comp (S.comp A)) x‖ / ‖x‖ := gainOnSubspace_le_div hx_mem hx_ne
      _ ≤ ‖B‖ * ‖A‖ * (‖S (A x)‖ / ‖A x‖) := h_per_vec
      _ = ‖S (A x)‖ / ‖A x‖ * (‖B‖ * ‖A‖) := by ring

/-- Rank of `M.map A` equals rank of `M` when `A` is injective on `M`. -/
private lemma rank_map_of_injective_on
    (A : W →L[𝕜] X) {M : Submodule 𝕜 W}
    (h_inj : ∀ x ∈ M, x ≠ 0 → A x ≠ 0) :
    Module.rank 𝕜 (M.map (A : W →ₗ[𝕜] X)) = Module.rank 𝕜 M := by
  -- `f := A.domRestrict M : M →ₗ X` has range `M.map A` and trivial kernel.
  set f : M →ₗ[𝕜] X := (A : W →ₗ[𝕜] X).domRestrict M with hf_def
  have h_inj_f : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    rintro ⟨x, hx_mem⟩ hx_ker
    by_contra hx_ne_zero
    exact h_inj x hx_mem (fun h => hx_ne_zero (by ext; exact h)) hx_ker
  rw [← LinearMap.range_domRestrict M (A : W →ₗ[𝕜] X)]
  exact (LinearEquiv.ofInjective f h_inj_f).rank_eq.symm

lemma bernsteinNumber_comp_comp_le
    (A : W →L[𝕜] X) (S : X →L[𝕜] Y) (B : Y →L[𝕜] Z) (n : ℕ) :
    bernsteinNumber (B.comp (S.comp A)) n ≤
      ‖B‖ * bernsteinNumber S n * ‖A‖ := by
  refine Real.sSup_le ?_
    (mul_nonneg (mul_nonneg (norm_nonneg _) (bernsteinNumber_nonneg _ _))
      (norm_nonneg _))
  rintro _ ⟨M, hM_rank, rfl⟩
  have hM_ne_bot : M ≠ ⊥ := rank_eq_succ_implies_ne_bot hM_rank
  by_cases h_inj : ∀ x ∈ M, x ≠ 0 → A x ≠ 0
  · -- Injective case.
    set M' : Submodule 𝕜 X := M.map (A : W →ₗ[𝕜] X)
    have hM'_rank : Module.rank 𝕜 M' = ((n + 1 : ℕ) : Cardinal) := by
      rw [rank_map_of_injective_on A h_inj, hM_rank]
    calc gainOnSubspace (B.comp (S.comp A)) M
        ≤ ‖B‖ * ‖A‖ * gainOnSubspace S M' :=
          gainOnSubspace_comp_comp_le_of_injective A S B hM_ne_bot h_inj
      _ ≤ ‖B‖ * ‖A‖ * bernsteinNumber S n :=
          mul_le_mul_of_nonneg_left
            (le_csSup (bSet_bddAbove S n) ⟨M', hM'_rank, rfl⟩)
            (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      _ = ‖B‖ * bernsteinNumber S n * ‖A‖ := by ring
  · -- Non-injective case: some nonzero `x ∈ M` has `A x = 0`, so `(BSA) x = 0`.
    simp only [not_forall, Classical.not_not, ne_eq] at h_inj
    obtain ⟨x, hx_mem, hx_ne, hAx_zero⟩ := h_inj
    have h_zero : ‖B.comp (S.comp A) x‖ / ‖x‖ = 0 := by
      show ‖B (S (A x))‖ / ‖x‖ = 0
      rw [hAx_zero, map_zero, map_zero, norm_zero, zero_div]
    linarith [(gainOnSubspace_le_div hx_mem hx_ne).trans (le_of_eq h_zero),
      mul_nonneg (mul_nonneg (norm_nonneg B) (bernsteinNumber_nonneg S n))
        (norm_nonneg A)]

/-! ## Summary: Bernstein numbers form a strict s-number sequence -/

theorem isSNumberSequence_bernsteinNumber :
    IsSNumberSequence (𝕜 := 𝕜)
        (fun {_X _Y} _ _ _ _ S n => bernsteinNumber S n) where
  nonneg := fun S n => bernsteinNumber_nonneg S n
  norm_at_zero := fun S => bernsteinNumber_zero_eq_norm S
  antitone := fun S n => bernsteinNumber_antitone S n
  subadditive := fun S T n => bernsteinNumber_add_le S T n
  ideal := fun A S B n => bernsteinNumber_comp_comp_le A S B n
  vanishes_on_low_rank := fun _ _ h => bernsteinNumber_eq_zero_of_rank_le h
  normalised_at_id := fun n => bernsteinNumber_id_euclidean n

theorem isStrictSNumberSequence_bernsteinNumber :
    IsStrictSNumberSequence (𝕜 := 𝕜)
        (fun {_X _Y} _ _ _ _ S n => bernsteinNumber S n) where
  toIsSNumberSequence := isSNumberSequence_bernsteinNumber
  strictly_normalised_at_id := fun n h => bernsteinNumber_strict n h

end SNumbers
