/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import SNumbers.ContinuousLinearMapRank
public import Mathlib.Analysis.Normed.Module.RieszLemma
public import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Approximation numbers

The approximation numbers are the *largest* example of an s-number sequence.
They are defined as

`a_n S = inf { ‖S - L‖ : L : X →L[𝕜] Y, rank L ≤ n }`.

In this file we prove that the approximation numbers satisfy all five
Pietsch axioms (S1)–(S5). In fact we prove the stronger normalisation
(S5'), `a_n (id_X) = 1` for every Banach space `X` with `dim X > n`,
via Riesz's lemma; (S5) on `ℓ₂^{n+1}` is the corresponding specialisation.
The argument requires `[CompleteSpace 𝕜]` (so that finite-dimensional
subspaces are closed) but is otherwise elementary.

We also prove here that the approximation numbers are the **largest**
s-number sequence (`sn_le_approximationNumber` : `sₙ(S) ≤ aₙ(S)` for every
s-number sequence `s`).

## Main definitions

* `SNumbers.approximationNumber S n`: the `n`-th approximation number of `S`.

## Main results

* `SNumbers.approximationNumber_zero_eq_norm` : `a_0 S = ‖S‖`              (S1a)
* `SNumbers.approximationNumber_antitone` : `a_{n+1} S ≤ a_n S`            (S1b)
* `SNumbers.approximationNumber_nonneg` : `0 ≤ a_n S`                      (S1c)
* `SNumbers.approximationNumber_additive` :
    `a_{n+m} (S + T) ≤ a_n S + a_m T`                                       (additivity)
* `SNumbers.approximationNumber_multiplicative` :
    `a_{n+m} (S ∘ T) ≤ a_n S * a_m T`                                       (multiplicativity)
* `SNumbers.approximationNumber_add_le` : `a_n (S + T) ≤ a_n S + ‖T‖`      (S2)
* `SNumbers.approximationNumber_comp_comp_le` :
    `a_n (B ∘ S ∘ A) ≤ ‖B‖ * a_n S * ‖A‖`                                   (S3)
* `SNumbers.approximationNumber_eq_zero_of_rank_le` :
    `rank S ≤ n ⇒ a_n S = 0`                                                (S4)
* `SNumbers.approximationNumber_strict` :
    `dim X > n ⇒ a_n (id_X) = 1`                                            (S5')
* `SNumbers.approximationNumber_id_euclidean` :
    `a_n (id_{ℓ₂^{n+1}}) = 1`                                               (S5)
* `SNumbers.isStrictSNumberSequence_approximationNumber` :
    the approximation numbers form a *strict* s-number sequence.
* `SNumbers.sn_le_approximationNumber` : `s_n S ≤ a_n S` for every s-number
    sequence `s`: the approximation numbers are the largest.
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

/-- The set of approximation residuals `‖S - L‖` over operators `L` of rank
at most `n`. -/
def approximationSet (S : X →L[𝕜] Y) (n : ℕ) : Set ℝ :=
  {r | ∃ L : X →L[𝕜] Y, L.rank ≤ (n : Cardinal) ∧ r = ‖S - L‖}

/-- The `n`-th **approximation number** of a continuous linear map: the
infimum of `‖S - L‖` over operators `L` of rank at most `n`. -/
noncomputable def approximationNumber (S : X →L[𝕜] Y) (n : ℕ) : ℝ :=
  sInf (approximationSet S n)

/-! ### Basic properties of `approximationSet` -/

/-- The approximation set is non-empty: take `L = 0`, which has rank `0`. -/
lemma approximationSet_nonempty (S : X →L[𝕜] Y) (n : ℕ) :
    (approximationSet S n).Nonempty :=
  ⟨‖S‖, 0, by simp, by simp⟩

/-- The approximation set is bounded below by `0`. -/
lemma bddBelow_approximationSet (S : X →L[𝕜] Y) (n : ℕ) :
    BddBelow (approximationSet S n) :=
  ⟨0, by rintro r ⟨L, _, rfl⟩; exact norm_nonneg _⟩

/-- Convenience: every operator `L` of rank ≤ n provides an upper bound for
the approximation number. -/
lemma approximationNumber_le_norm_sub {S : X →L[𝕜] Y} {n : ℕ}
    {L : X →L[𝕜] Y} (hL : L.rank ≤ (n : Cardinal)) :
    approximationNumber S n ≤ ‖S - L‖ :=
  csInf_le (bddBelow_approximationSet S n) ⟨L, hL, rfl⟩

/-! ### (S1c) Non-negativity -/

lemma approximationNumber_nonneg (S : X →L[𝕜] Y) (n : ℕ) :
    0 ≤ approximationNumber S n :=
  le_csInf (approximationSet_nonempty S n) <| by
    rintro r ⟨L, _, rfl⟩; exact norm_nonneg _

/-! ### (S1b) Monotonicity in `n` -/

/-- If `n ≤ m`, then `a_m S ≤ a_n S`. -/
lemma approximationNumber_antitone' {S : X →L[𝕜] Y} {n m : ℕ} (h : n ≤ m) :
    approximationNumber S m ≤ approximationNumber S n := by
  refine csInf_le_csInf (bddBelow_approximationSet S m) (approximationSet_nonempty S n) ?_
  rintro r ⟨L, hL, rfl⟩
  exact ⟨L, hL.trans (by exact_mod_cast h), rfl⟩

lemma approximationNumber_antitone (S : X →L[𝕜] Y) (n : ℕ) :
    approximationNumber S (n + 1) ≤ approximationNumber S n :=
  approximationNumber_antitone' (Nat.le_succ n)

/-! ### (S1a) Value at `n = 0` -/

/-- The approximation set at `n = 0` is the singleton `{‖S‖}`. -/
lemma approximationSet_zero (S : X →L[𝕜] Y) :
    approximationSet S 0 = {‖S‖} := by
  ext r; constructor
  · rintro ⟨L, hL, rfl⟩
    have : L = 0 := ContinuousLinearMap.eq_zero_of_rank_le_zero (by exact_mod_cast hL)
    simp [this]
  · rintro rfl
    exact ⟨0, by simp, by simp⟩

/-- (S1a) `a_0 S = ‖S‖`. -/
@[simp] lemma approximationNumber_zero_eq_norm (S : X →L[𝕜] Y) :
    approximationNumber S 0 = ‖S‖ := by
  simp [approximationNumber, approximationSet_zero]

/-- Upper bound by the operator norm: `a_n S ≤ ‖S‖`. -/
lemma approximationNumber_le_norm (S : X →L[𝕜] Y) (n : ℕ) :
    approximationNumber S n ≤ ‖S‖ :=
  (antitone_nat_of_succ_le (approximationNumber_antitone S) (Nat.zero_le n)).trans_eq
    (approximationNumber_zero_eq_norm S)

/-! ### (S4) Vanishing on operators of rank at most `n` -/

/-- (S4) If `rank S ≤ n`, then `a_n S = 0`. -/
lemma approximationNumber_eq_zero_of_rank_le {S : X →L[𝕜] Y} {n : ℕ}
    (hS : S.rank ≤ (n : Cardinal)) :
    approximationNumber S n = 0 := by
  refine le_antisymm ?_ (approximationNumber_nonneg S n)
  -- `0 = ‖S - S‖ ∈ approximationSet S n`, hence the infimum is `≤ 0`.
  have h0 : (0 : ℝ) ∈ approximationSet S n := ⟨S, hS, by simp⟩
  exact csInf_le (bddBelow_approximationSet S n) h0

/-! ### Additivity and multiplicativity

The strong forms of (S2) and (S3), in which both operators are approximated
(cf. Pietsch, *Eigenvalues and s-numbers*, Section 2.3):

* if `L` approximates `S` with rank `≤ n` and `K` approximates `T` with rank `≤ m`,
  then `L + K` approximates `S + T` with rank `≤ n + m`;
* for composition, `R := L ∘ T + (S - L) ∘ K` has rank `≤ n + m` and leaves the
  residual `S ∘ T - R = (S - L) ∘ (T - K)`.

Taking the infimum over `L` and `K` gives `a_{n+m}(S + T) ≤ aₙ(S) + a_m(T)` and
`a_{n+m}(S ∘ T) ≤ aₙ(S) · a_m(T)`. -/

/-- One pair of approximants for additivity: if `rank L ≤ n` and `rank K ≤ m`, then
`a_{n+m}(S + T) ≤ ‖S - L‖ + ‖T - K‖`, witnessed by the approximant `L + K`. -/
lemma approximationNumber_add_le_norm_sub_add {S T L K : X →L[𝕜] Y} {n m : ℕ}
    (hL : L.rank ≤ (n : Cardinal)) (hK : K.rank ≤ (m : Cardinal)) :
    approximationNumber (S + T) (n + m) ≤ ‖S - L‖ + ‖T - K‖ := by
  -- `rank (L + K) ≤ rank L + rank K ≤ n + m`
  have h_rank : (L + K).rank ≤ ((n + m : ℕ) : Cardinal) := by
    rw [Nat.cast_add]
    exact (LinearMap.rank_add_le (L : X →ₗ[𝕜] Y) (K : X →ₗ[𝕜] Y)).trans (add_le_add hL hK)
  calc approximationNumber (S + T) (n + m)
      ≤ ‖(S + T) - (L + K)‖ := approximationNumber_le_norm_sub h_rank
    _ = ‖(S - L) + (T - K)‖ := by congr 1; abel
    _ ≤ ‖S - L‖ + ‖T - K‖ := norm_add_le _ _

/-- **Additivity of the approximation numbers**:
`a_{n+m}(S + T) ≤ aₙ(S) + a_m(T)`. -/
theorem approximationNumber_additive (S T : X →L[𝕜] Y) (n m : ℕ) :
    approximationNumber (S + T) (n + m) ≤
      approximationNumber S n + approximationNumber T m := by
  -- infimum over the approximants `L` of `S`
  rw [← sub_le_iff_le_add]
  refine le_csInf (approximationSet_nonempty S n) ?_
  rintro _ ⟨L, hL, rfl⟩
  -- infimum over the approximants `K` of `T`
  rw [sub_le_comm]
  refine le_csInf (approximationSet_nonempty T m) ?_
  rintro _ ⟨K, hK, rfl⟩
  linarith [approximationNumber_add_le_norm_sub_add (S := S) (T := T) hL hK]

/-- One pair of approximants for multiplicativity: if `rank L ≤ n` and `rank K ≤ m`, then
`a_{n+m}(S ∘ T) ≤ ‖S - L‖ · ‖T - K‖`, witnessed by the approximant
`L ∘ T + (S - L) ∘ K`, whose residual is `(S - L) ∘ (T - K)`. -/
lemma approximationNumber_comp_le_norm_sub_mul {S L : Y →L[𝕜] Z} {T K : X →L[𝕜] Y}
    {n m : ℕ} (hL : L.rank ≤ (n : Cardinal)) (hK : K.rank ≤ (m : Cardinal)) :
    approximationNumber (S.comp T) (n + m) ≤ ‖S - L‖ * ‖T - K‖ := by
  set R : X →L[𝕜] Z := L.comp T + (S - L).comp K with hR
  -- `rank R ≤ rank (L ∘ T) + rank ((S - L) ∘ K) ≤ rank L + rank K ≤ n + m`
  have h_rank : R.rank ≤ ((n + m : ℕ) : Cardinal) := by
    rw [Nat.cast_add]
    calc R.rank
        ≤ (L.comp T).rank + ((S - L).comp K).rank :=
          LinearMap.rank_add_le ((L.comp T : X →L[𝕜] Z) : X →ₗ[𝕜] Z)
            ((S - L).comp K : X →ₗ[𝕜] Z)
      _ ≤ L.rank + K.rank :=
          add_le_add (LinearMap.rank_comp_le_left (T : X →ₗ[𝕜] Y) (L : Y →ₗ[𝕜] Z))
            (LinearMap.rank_comp_le_right (K : X →ₗ[𝕜] Y) ((S - L : Y →L[𝕜] Z) : Y →ₗ[𝕜] Z))
      _ ≤ n + m := add_le_add hL hK
  -- the residual factors
  have h_eq : S.comp T - R = (S - L).comp (T - K) := by
    rw [hR]
    simp only [ContinuousLinearMap.comp_sub, ContinuousLinearMap.sub_comp]
    abel
  calc approximationNumber (S.comp T) (n + m)
      ≤ ‖S.comp T - R‖ := approximationNumber_le_norm_sub h_rank
    _ = ‖(S - L).comp (T - K)‖ := by rw [h_eq]
    _ ≤ ‖S - L‖ * ‖T - K‖ := opNorm_comp_le _ _

/-- **Multiplicativity of the approximation numbers**: for `T : X → Y` and `S : Y → Z`,
`a_{n+m}(S ∘ T) ≤ aₙ(S) · a_m(T)`. -/
theorem approximationNumber_multiplicative (S : Y →L[𝕜] Z) (T : X →L[𝕜] Y) (n m : ℕ) :
    approximationNumber (S.comp T) (n + m) ≤
      approximationNumber S n * approximationNumber T m := by
  -- For a fixed approximant `L` of `S`, take the infimum over the approximants `K` of `T`,
  -- pulling the non-negative factor `‖S - L‖` inside it.
  have h1 : ∀ L : Y →L[𝕜] Z, L.rank ≤ (n : Cardinal) →
      approximationNumber (S.comp T) (n + m) ≤ ‖S - L‖ * approximationNumber T m := by
    intro L hL
    show _ ≤ ‖S - L‖ • sInf (approximationSet T m)
    rw [← Real.sInf_smul_of_nonneg (norm_nonneg _)]
    refine le_csInf ((approximationSet_nonempty T m).image _) ?_
    rintro _ ⟨_, ⟨K, hK, rfl⟩, rfl⟩
    exact approximationNumber_comp_le_norm_sub_mul hL hK
  -- Then take the infimum over `L`, pulling the factor `a_m(T) ≥ 0` inside it.
  rw [mul_comm]
  show _ ≤ approximationNumber T m • sInf (approximationSet S n)
  rw [← Real.sInf_smul_of_nonneg (approximationNumber_nonneg T m)]
  refine le_csInf ((approximationSet_nonempty S n).image _) ?_
  rintro _ ⟨_, ⟨L, hL, rfl⟩, rfl⟩
  show _ ≤ approximationNumber T m * ‖S - L‖
  rw [mul_comm]
  exact h1 L hL

/-! ### (S2) Subadditivity -/

/-- (S2) `a_n (S + T) ≤ a_n S + ‖T‖`: additivity with `m = 0`, since `a_0 T = ‖T‖`. -/
lemma approximationNumber_add_le (S T : X →L[𝕜] Y) (n : ℕ) :
    approximationNumber (S + T) n ≤ approximationNumber S n + ‖T‖ := by
  have h := approximationNumber_additive S T n 0
  rwa [Nat.add_zero, approximationNumber_zero_eq_norm] at h

/-! ### (S3) Ideal property -/

/-- **(S3) Ideal property.** `a_n (B ∘ S ∘ A) ≤ ‖B‖ * a_n S * ‖A‖`: multiplicativity
applied twice with one index `0`, since `a_0 = ‖·‖`. -/
lemma approximationNumber_comp_comp_le
    (A : W →L[𝕜] X) (S : X →L[𝕜] Y) (B : Y →L[𝕜] Z) (n : ℕ) :
    approximationNumber (B.comp (S.comp A)) n ≤
      ‖B‖ * approximationNumber S n * ‖A‖ := by
  have hSA : approximationNumber (S.comp A) n ≤ approximationNumber S n * ‖A‖ := by
    have h := approximationNumber_multiplicative S A n 0
    rwa [Nat.add_zero, approximationNumber_zero_eq_norm] at h
  have hB : approximationNumber (B.comp (S.comp A)) n ≤
      ‖B‖ * approximationNumber (S.comp A) n := by
    have h := approximationNumber_multiplicative B (S.comp A) 0 n
    rwa [Nat.zero_add, approximationNumber_zero_eq_norm] at h
  calc approximationNumber (B.comp (S.comp A)) n
      ≤ ‖B‖ * approximationNumber (S.comp A) n := hB
    _ ≤ ‖B‖ * (approximationNumber S n * ‖A‖) :=
        mul_le_mul_of_nonneg_left hSA (norm_nonneg B)
    _ = ‖B‖ * approximationNumber S n * ‖A‖ := (mul_assoc _ _ _).symm


/-! ### The approximation numbers are the largest s-number sequence -/

/-- For every `s`-number sequence and every operator `S : X → Y`,
`sₙ(S) ≤ aₙ(S)`: the approximation numbers are the largest `s`-numbers.
This is the easy half of Pietsch's sandwich theorem; it uses only axioms
(S2) and (S4) of `IsSNumberSequence`. -/
theorem sn_le_approximationNumber
    {s : Family 𝕜} (hs : IsSNumberSequence s) (S : X →L[𝕜] Y) (n : ℕ) :
    s S n ≤ approximationNumber S n := by
  refine le_csInf (approximationSet_nonempty S n) ?_
  rintro r ⟨A, hA, rfl⟩
  have hS_eq : S = A + (S - A) := by abel
  have h_low : s A n = 0 := hs.vanishes_on_low_rank A n hA
  calc s S n
      = s (A + (S - A)) n := by rw [← hS_eq]
    _ ≤ s A n + ‖S - A‖ := hs.subadditive A (S - A) n
    _ = ‖S - A‖ := by rw [h_low, zero_add]



/-! ### (S5') Strict normalisation `a_n (id_X) = 1` whenever `dim X > n`

We prove the stronger form (S5') directly via Riesz's lemma, avoiding both
SVD and Auerbach. The classical (S5) on `EuclideanSpace 𝕜 (Fin (n + 1))`
follows as a one-line specialisation.

Key idea:
* `≤ 1`: take `L = 0`. Then `‖id - 0‖ = ‖id‖ = 1` (since `dim X > 0`).
* `≥ 1`: for any `L` with `rank L ≤ n`, the range of `L` is a proper
  finite-dimensional, hence closed, subspace of `X`. Riesz's lemma gives,
  for any `r < 1`, an `x₀ ∉ range L` with `r * ‖x₀‖ ≤ ‖x₀ - L x₀‖`. The
  operator-norm sup characterisation then gives
  `‖id − L‖ ≥ ‖(id − L) x₀‖ / ‖x₀‖ ≥ r`. Letting `r → 1` yields `‖id − L‖ ≥ 1`,
  hence `a_n(id) ≥ 1`.-/
variable [CompleteSpace 𝕜]

/-- (S5') Strict normalisation: `approximationNumber (id_X) n = 1` whenever
`n < Module.finrank 𝕜 X`. -/
lemma approximationNumber_strict {X : Type u} [NormedAddCommGroup X]
    [NormedSpace 𝕜 X] (n : ℕ) (h : n < Module.finrank 𝕜 X) :
    approximationNumber (ContinuousLinearMap.id 𝕜 X) n = 1 := by
  -- Set up: `X` is finite-dimensional and nontrivial.
  have h_finrank_pos : 0 < Module.finrank 𝕜 X :=
    Nat.lt_of_le_of_lt (Nat.zero_le _) h
  have : FiniteDimensional 𝕜 X := .of_finrank_pos h_finrank_pos
  have : Nontrivial X := Module.nontrivial_of_finrank_pos h_finrank_pos
  have h_id_norm : ‖ContinuousLinearMap.id 𝕜 X‖ = 1 := norm_id
  set I := ContinuousLinearMap.id 𝕜 X with hI_def
  refine le_antisymm ?_ ?_
  · -- Upper bound: `a_n I ≤ ‖I − 0‖ = ‖I‖ = 1`.
    have h_zero_rank : (0 : X →L[𝕜] X).rank ≤ (n : Cardinal) := by simp
    calc approximationNumber I n
        ≤ ‖I - 0‖ := approximationNumber_le_norm_sub h_zero_rank
      _ = ‖I‖ := by rw [sub_zero]
      _ = 1 := h_id_norm
  · -- Lower bound: every `L` with `rank L ≤ n` satisfies `‖I − L‖ ≥ 1`.
    refine le_csInf (approximationSet_nonempty I n) ?_
    rintro _ ⟨L, hL, rfl⟩
    -- ===== Step A: `range L` is a closed proper subspace of `X`. =====
    set V : Submodule 𝕜 X := LinearMap.range (L : X →ₗ[𝕜] X) with hV_def
    -- `dim V ≤ rank L ≤ n < dim X`, so `V` cannot be all of `X`.
    have hV_finrank_le : Module.finrank 𝕜 V ≤ n := Module.finrank_le_of_rank_le hL
    have hV_finrank_lt : Module.finrank 𝕜 V < Module.finrank 𝕜 X :=
      lt_of_le_of_lt hV_finrank_le h
    have hV_ne_top : V ≠ ⊤ := by
      intro h_top
      rw [h_top, finrank_top] at hV_finrank_lt
      exact lt_irrefl _ hV_finrank_lt
    -- Finite-dimensional subspaces are closed (uses `[CompleteSpace 𝕜]`).
    have hV_closed : IsClosed (V : Set X) := V.closed_of_finiteDimensional
    -- Properness gives some point outside `V`.
    have hV_exists : ∃ x : X, x ∉ V := SetLike.exists_notMem_of_ne_top V hV_ne_top
    -- ===== Steps B–D: for every `r ∈ (0, 1)`, show `r ≤ ‖I − L‖`. =====
    have h_aux : ∀ r : ℝ, 0 < r → r < 1 → r ≤ ‖I - L‖ := by
      intro r _ hr1
      -- ----- Step B: Riesz's lemma at level `r < 1` produces `x₀`. -----
      obtain ⟨x₀, hx₀_ne, hx₀_dist⟩ := riesz_lemma hV_closed hV_exists hr1
      -- `x₀ ∉ V`, in particular `x₀ ≠ 0`, so `‖x₀‖ > 0`.
      have hx₀_ne_zero : x₀ ≠ 0 := fun h0 => hx₀_ne (h0 ▸ V.zero_mem)
      have hx₀_norm_pos : 0 < ‖x₀‖ := norm_pos_iff.mpr hx₀_ne_zero
      -- ----- Step C: `r * ‖x₀‖ ≤ ‖(I − L) x₀‖`. -----
      -- Specialise the Riesz distance bound to `y = L x₀ ∈ range L`.
      have h_apply : (I - L) x₀ = x₀ - L x₀ := by
        simp [hI_def, sub_apply, ContinuousLinearMap.id_apply]
      have h_riesz : r * ‖x₀‖ ≤ ‖x₀ - L x₀‖ :=
        hx₀_dist (L x₀) (LinearMap.mem_range_self _ _)
      have h_witness : r * ‖x₀‖ ≤ ‖(I - L) x₀‖ := by
        rw [h_apply]; exact h_riesz
      -- ----- Step D: divide by `‖x₀‖` after the operator-norm bound. -----
      -- `‖(I − L) x₀‖ ≤ ‖I − L‖ * ‖x₀‖` is the operator-norm inequality.
      have h_op : ‖(I - L) x₀‖ ≤ ‖I - L‖ * ‖x₀‖ := (I - L).le_opNorm x₀
      have h_chain : r * ‖x₀‖ ≤ ‖I - L‖ * ‖x₀‖ := h_witness.trans h_op
      -- Cancel the positive factor `‖x₀‖`.
      exact le_of_mul_le_mul_right h_chain hx₀_norm_pos
    -- ===== Step E: ε → 1 via `le_of_forall_pos_le_add`. =====
    -- We have `(1 - ε) ≤ ‖I − L‖` for every small `ε > 0`. Rephrase as
    -- `1 ≤ ‖I − L‖ + ε`; the `ε ≥ 1` case is trivial (RHS ≥ 0 + 1).
    refine le_of_forall_pos_le_add fun ε hε => ?_
    by_cases hε1 : 1 ≤ ε
    · linarith [norm_nonneg (I - L)]
    have hε1' : ε < 1 := lt_of_not_ge hε1
    linarith [h_aux (1 - ε) (by linarith) (by linarith)]

/-- (S5) Normalisation on `id_{ℓ₂^{n+1}}`: a special case of (S5'). -/
lemma approximationNumber_id_euclidean (n : ℕ) :
    approximationNumber
      (ContinuousLinearMap.id 𝕜 (EuclideanSpace 𝕜 (Fin (n + 1)))) n = 1 := by
  have h : n < Module.finrank 𝕜 (EuclideanSpace 𝕜 (Fin (n + 1))) := by
    rw [finrank_euclideanSpace_fin' (n + 1)]; exact Nat.lt_succ_self n
  exact approximationNumber_strict n h

/-! ### Summary: approximation numbers form a strict s-number sequence -/

/-- The approximation numbers as a `Family`, the form in which the axioms of an s-number
sequence take their argument. It is public because the two theorems below name it in their
statements. -/
noncomputable def approxFamily : Family 𝕜 :=
  fun {_X _Y} _ _ _ _ S n => approximationNumber S n

/-- The approximation numbers form an s-number sequence in the sense of Pietsch. -/
theorem isSNumberSequence_approximationNumber :
    IsSNumberSequence (𝕜 := 𝕜) approxFamily where
  norm_at_zero := fun S => approximationNumber_zero_eq_norm S
  antitone := fun S n => approximationNumber_antitone S n
  nonneg := fun S n => approximationNumber_nonneg S n
  subadditive := fun S T n => approximationNumber_add_le S T n
  ideal := fun A S B n => approximationNumber_comp_comp_le A S B n
  vanishes_on_low_rank := fun _ _ h => approximationNumber_eq_zero_of_rank_le h
  normalised_at_id := fun n => approximationNumber_id_euclidean n

/-- Approximation numbers form a *strict* s-number sequence: in addition to
(S1)–(S5) they satisfy (S5'), the strong normalisation `a_n (id_X) = 1` for
every Banach space `X` with `dim X > n`. -/
theorem isStrictSNumberSequence_approximationNumber :
    IsStrictSNumberSequence (𝕜 := 𝕜) approxFamily where
  toIsSNumberSequence := isSNumberSequence_approximationNumber
  strictly_normalised_at_id := fun n h => approximationNumber_strict n h

omit [CompleteSpace 𝕜] in
/-- The approximation numbers are additive: `a_{n+m}(S + T) ≤ aₙ(S) + a_m(T)`. -/
theorem additive_approxFamily : Additive (𝕜 := 𝕜) approxFamily :=
  fun S T n m => approximationNumber_additive S T n m

omit [CompleteSpace 𝕜] in
/-- The approximation numbers are multiplicative: `a_{n+m}(S ∘ T) ≤ aₙ(S) · a_m(T)`. -/
theorem multiplicative_approxFamily : Multiplicative (𝕜 := 𝕜) approxFamily :=
  fun S T n m => approximationNumber_multiplicative S T n m

end SNumbers
