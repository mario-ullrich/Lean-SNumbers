/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import SNumbers.Bernstein
public import SNumbers.PiLpCoordinates
public import SNumbers.Examples.Identity
public import Mathlib.Analysis.Normed.Operator.Prod

/-!
# The identities between `ℓ₂ᴺ` and `ℓ∞ᴺ`, and two bad properties of the Bernstein numbers

The approximation, Gelfand and Kolmogorov numbers are additive and multiplicative
(`approximationNumber_additive`, `gelfandNumber_multiplicative`, …). The Bernstein numbers
are neither, as Pietsch showed (*Bad properties of the Bernstein numbers*, Studia Math. 184
(2008), Theorem 3). This file gives two explicit finite-dimensional counterexamples. They
rest on two bounds for the identity maps between `ℓ₂ᴺ` and `ℓ∞ᴺ`:

* `bernsteinNumber_idEmbed_two_infty_le`: `bₙ(id : ℓ₂ᴺ → ℓ∞ᴺ) ≤ 1/√(n+1)`. Every
  `(n+1)`-dimensional subspace contains a vector whose coordinates all have modulus `≤ 1`
  and at least `n + 1` of which have modulus `1` (the flatness lemma `exists_flat_vector`).
  Its `ℓ∞`-norm is at most `1` and its `ℓ₂`-norm at least `√(n+1)`.
* `bernsteinNumber_idEmbed_infty_two_le`: `bₙ(id : ℓ∞ᴺ → ℓ₂ᴺ) ≤ √(N/(n+1))`. Let
  `v₁, …, v_{n+1}` be an orthonormal basis, for the `ℓ₂` inner product, of an
  `(n+1)`-dimensional subspace `M`. For a coordinate `k`, the vector
  `x = ∑ᵢ conj(vᵢ(k)) vᵢ ∈ M` satisfies `x(k) = ‖x‖₂² = sₖ := ∑ᵢ |vᵢ(k)|²`, so the gain `c`
  of the identity on `M` satisfies `c² sₖ ≤ 1`. Summing over `k` and using
  `∑ₖ sₖ = ∑ᵢ ‖vᵢ‖₂² = n + 1` gives `c² (n + 1) ≤ N`.

**Multiplicativity fails** (`not_multiplicative_bernsteinNumber`): for `T = id : ℓ₂³ → ℓ∞³`
and `S = id : ℓ∞³ → ℓ₂³`, the composition `S ∘ T` is the identity of `ℓ₂³`, so
`b₂(S ∘ T) = 1`, while `b₁(S) · b₁(T) ≤ √(3/2) · (1/√2) = √3/2 < 1`.

**Additivity fails** (`not_additive_bernsteinNumber`): on `ℓ₂⁷¹ × ℓ∞⁷¹` with the maximum of
the two norms, let `S (x, y) = (0, x)` and `T (x, y) = (y/9, 0)`. Then `S + T` maps `(x, 3x)`
to `(x/3, x) = (1/3) · (x, 3x)`, so `b₇₀(S + T) ≥ 1/3`, while `b₃₅(S) ≤ 1/6` and
`b₃₅(T) ≤ √71/54 < 1/6`.

Pietsch's proof uses the same two identities, together with the `2`-summing norm; the
arguments here are elementary.
-/

@[expose] public section

universe u

open scoped ENNReal ComplexConjugate
open ContinuousLinearMap

namespace SNumbers.L2Linf

variable {𝕜 : Type u} [RCLike 𝕜]

/-! ## The identity `ℓ₂ᴺ → ℓ∞ᴺ` -/

/-- A vector with at least `k` coordinates of modulus `1` has `ℓ₂`-norm at least `√k`. -/
lemma sqrt_le_norm_toLp_two {N k : ℕ} (w : Fin N → 𝕜)
    (hk : k ≤ (Finset.univ.filter fun i => ‖w i‖ = 1).card) :
    Real.sqrt k ≤ ‖(WithLp.toLp 2 w : PiLp 2 (fun _ : Fin N => 𝕜))‖ := by
  rw [PiLp.norm_eq_of_L2]
  refine Real.sqrt_le_sqrt ?_
  calc (k : ℝ)
      ≤ (Finset.univ.filter fun i => ‖w i‖ = 1).card := by exact_mod_cast hk
    _ = ∑ i ∈ Finset.univ.filter (fun i => ‖w i‖ = 1), ‖w i‖ ^ 2 := by
        rw [Finset.card_eq_sum_ones, Nat.cast_sum]
        refine Finset.sum_congr rfl fun i hi => ?_
        rw [(Finset.mem_filter.mp hi).2, one_pow, Nat.cast_one]
    _ ≤ ∑ i, ‖w i‖ ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          fun i _ _ => sq_nonneg _

/-- **Bernstein numbers of `ℓ₂ᴺ → ℓ∞ᴺ`**: `bₙ(id : ℓ₂ᴺ → ℓ∞ᴺ) ≤ 1/√(n+1)`. Every
`(n+1)`-dimensional subspace contains a flat vector `x` (`exists_flat_vector`), with
`‖x‖_∞ ≤ 1` and `‖x‖₂ ≥ √(n+1)`. -/
theorem bernsteinNumber_idEmbed_two_infty_le (N n : ℕ) :
    bernsteinNumber (idEmbed (𝕜 := 𝕜) (m := N) ∞ 2) n ≤ 1 / Real.sqrt (n + 1) := by
  refine Real.sSup_le ?_ (by positivity)
  rintro _ ⟨M, hM_rank, rfl⟩
  -- transport `M` to `Fin N → 𝕜` and pick a flat vector there
  set e : PiLp 2 (fun _ : Fin N => 𝕜) ≃ₗ[𝕜] (Fin N → 𝕜) :=
    WithLp.linearEquiv 2 𝕜 (Fin N → 𝕜) with he
  have hkV : n + 1 ≤ Module.finrank 𝕜
      (M.map (e : PiLp 2 (fun _ : Fin N => 𝕜) →ₗ[𝕜] (Fin N → 𝕜))) := by
    rw [LinearEquiv.finrank_map_eq, Module.finrank_eq_of_rank_eq hM_rank]
  obtain ⟨w, hwV, hw0, hwle, hwcard⟩ := exists_flat_vector (k := n + 1) (by omega) hkV
  obtain ⟨v, hvM, hev⟩ := Submodule.mem_map.mp hwV
  have hxM : (WithLp.toLp 2 w : PiLp 2 (fun _ : Fin N => 𝕜)) ∈ M := by
    rw [← hev]; simpa [he] using hvM
  have hx0 : (WithLp.toLp 2 w : PiLp 2 (fun _ : Fin N => 𝕜)) ≠ 0 := fun h =>
    hw0 (by simpa using congrArg WithLp.ofLp h)
  -- `‖x‖_∞ ≤ 1` and `‖x‖₂ ≥ √(n+1)`
  have hnum : ‖idEmbed (𝕜 := 𝕜) (m := N) ∞ 2 (WithLp.toLp 2 w)‖ ≤ 1 := by
    rw [← PiLp.norm_ofLp]
    exact (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun i => hwle i
  have hden : Real.sqrt (n + 1) ≤ ‖(WithLp.toLp 2 w : PiLp 2 (fun _ : Fin N => 𝕜))‖ := by
    have h := sqrt_le_norm_toLp_two w hwcard
    push_cast at h
    exact h
  have hsqrt : 0 < Real.sqrt ((n : ℝ) + 1) := Real.sqrt_pos.mpr (by positivity)
  calc gainOnSubspace (idEmbed (𝕜 := 𝕜) (m := N) ∞ 2) M
      ≤ ‖idEmbed (𝕜 := 𝕜) (m := N) ∞ 2 (WithLp.toLp 2 w)‖ /
          ‖(WithLp.toLp 2 w : PiLp 2 (fun _ : Fin N => 𝕜))‖ := gainOnSubspace_le_div hxM hx0
    _ ≤ 1 / ‖(WithLp.toLp 2 w : PiLp 2 (fun _ : Fin N => 𝕜))‖ := by gcongr
    _ ≤ 1 / Real.sqrt (n + 1) := one_div_le_one_div_of_le hsqrt hden

/-! ## The identity `ℓ∞ᴺ → ℓ₂ᴺ` -/

section OrthonormalBasis

variable {N : ℕ} {ι : Type*} [Fintype ι] {M : Submodule 𝕜 (PiLp 2 (fun _ : Fin N => 𝕜))}

/-- For an orthonormal basis `(vᵢ)` of a subspace `M ⊆ ℓ₂ᴺ` and a coordinate `k`, the
vector `x = ∑ᵢ conj(vᵢ(k)) vᵢ ∈ M` satisfies `x(k) = ‖x‖₂² = ∑ᵢ |vᵢ(k)|²`. -/
lemma exists_mem_apply_eq_norm_sq (b : OrthonormalBasis ι 𝕜 M) (k : Fin N) :
    ∃ x ∈ M, x k = ((∑ i, ‖(b i : PiLp 2 (fun _ : Fin N => 𝕜)) k‖ ^ 2 : ℝ) : 𝕜) ∧
      ‖x‖ ^ 2 = ∑ i, ‖(b i : PiLp 2 (fun _ : Fin N => 𝕜)) k‖ ^ 2 := by
  set a : EuclideanSpace 𝕜 ι :=
    WithLp.toLp 2 (fun i => conj ((b i : PiLp 2 (fun _ : Fin N => 𝕜)) k)) with ha
  refine ⟨(b.repr.symm a : PiLp 2 (fun _ : Fin N => 𝕜)), (b.repr.symm a).2, ?_, ?_⟩
  · rw [← b.sum_repr_symm a, Submodule.coe_sum]
    simp [ha, RCLike.conj_mul]
  · rw [Submodule.norm_coe, LinearIsometryEquiv.norm_map, PiLp.norm_sq_eq_of_L2]
    simp [ha]

/-- The coordinates of an orthonormal basis of `M ⊆ ℓ₂ᴺ` carry total mass `dim M`:
`∑ₖ ∑ᵢ |vᵢ(k)|² = ∑ᵢ ‖vᵢ‖₂² = |ι|`. -/
lemma sum_sum_norm_sq_apply (b : OrthonormalBasis ι 𝕜 M) :
    ∑ k, ∑ i, ‖(b i : PiLp 2 (fun _ : Fin N => 𝕜)) k‖ ^ 2 = Fintype.card ι := by
  rw [Finset.sum_comm]
  have h : ∀ i, ∑ k, ‖(b i : PiLp 2 (fun _ : Fin N => 𝕜)) k‖ ^ 2 = 1 := fun i => by
    rw [← PiLp.norm_sq_eq_of_L2 (fun _ : Fin N => 𝕜) (b i : PiLp 2 (fun _ : Fin N => 𝕜)),
      Submodule.norm_coe, b.orthonormal.1 i, one_pow]
  simp only [h, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]

end OrthonormalBasis

/-- **Bernstein numbers of `ℓ∞ᴺ → ℓ₂ᴺ`**: `bₙ(id : ℓ∞ᴺ → ℓ₂ᴺ) ≤ √(N/(n+1))`. On an
`(n+1)`-dimensional subspace with gain `c`, every coordinate `k` gives `c² sₖ ≤ 1`, where
`sₖ = ∑ᵢ |vᵢ(k)|²` for an orthonormal basis `(vᵢ)` (`exists_mem_apply_eq_norm_sq`), and
`∑ₖ sₖ = n + 1` (`sum_sum_norm_sq_apply`). -/
theorem bernsteinNumber_idEmbed_infty_two_le (N n : ℕ) :
    bernsteinNumber (idEmbed (𝕜 := 𝕜) (m := N) 2 ∞) n ≤ Real.sqrt (N / (n + 1)) := by
  refine Real.sSup_le ?_ (Real.sqrt_nonneg _)
  rintro _ ⟨M, hM_rank, rfl⟩
  set c := gainOnSubspace (idEmbed (𝕜 := 𝕜) (m := N) 2 ∞) M with hc_def
  have hc0 : 0 ≤ c := gainOnSubspace_nonneg _ _
  -- the same subspace, inside `ℓ₂ᴺ`
  set E : PiLp ∞ (fun _ : Fin N => 𝕜) ≃ₗ[𝕜] PiLp 2 (fun _ : Fin N => 𝕜) :=
    (WithLp.linearEquiv ∞ 𝕜 (Fin N → 𝕜)).trans (WithLp.linearEquiv 2 𝕜 (Fin N → 𝕜)).symm
    with hE
  set M₂ : Submodule 𝕜 (PiLp 2 (fun _ : Fin N => 𝕜)) :=
    M.map (E : PiLp ∞ (fun _ : Fin N => 𝕜) →ₗ[𝕜] PiLp 2 (fun _ : Fin N => 𝕜)) with hM₂
  have hd : Module.finrank 𝕜 M₂ = n + 1 := by
    rw [hM₂, LinearEquiv.finrank_map_eq, Module.finrank_eq_of_rank_eq hM_rank]
  set b := stdOrthonormalBasis 𝕜 M₂ with hb
  obtain ⟨s, hs⟩ : ∃ s : Fin N → ℝ,
      s = fun k => ∑ i, ‖(b i : PiLp 2 (fun _ : Fin N => 𝕜)) k‖ ^ 2 := ⟨_, rfl⟩
  have hs_apply : ∀ k, s k = ∑ i, ‖(b i : PiLp 2 (fun _ : Fin N => 𝕜)) k‖ ^ 2 := by
    intro k; rw [hs]
  -- each coordinate: `c² · s k ≤ 1`
  have hkey : ∀ k, c ^ 2 * s k ≤ 1 := by
    intro k
    have hs0 : 0 ≤ s k := by rw [hs_apply]; exact Finset.sum_nonneg fun i _ => sq_nonneg _
    rcases hs0.eq_or_lt with hsk | hsk
    · rw [← hsk, mul_zero]; exact zero_le_one
    obtain ⟨x, hxM₂, hxk, hxnorm⟩ := exists_mem_apply_eq_norm_sq b k
    rw [← hs_apply] at hxk hxnorm
    obtain ⟨y, hyM, hyx⟩ := Submodule.mem_map.mp hxM₂
    -- `y ∈ M` and `x ∈ M₂` have the same coordinates
    have hcoord : ∀ i, y i = x i := fun i => by rw [← hyx]; rfl
    have hid : idEmbed (𝕜 := 𝕜) (m := N) 2 ∞ y = x := by rw [← hyx]; rfl
    have hy0 : y ≠ 0 := by
      intro h
      have hx0 : x k = 0 := by rw [← hcoord k, h, PiLp.zero_apply]
      rw [hxk, RCLike.ofReal_eq_zero] at hx0
      exact hsk.ne' hx0
    have hypos : 0 < ‖y‖ := norm_pos_iff.mpr hy0
    -- `s k = |x k| = |y k| ≤ ‖y‖_∞`
    have hyk : s k ≤ ‖y‖ := by
      calc s k = ‖x k‖ := by rw [hxk, RCLike.norm_ofReal, abs_of_nonneg hs0]
        _ = ‖y k‖ := by rw [hcoord]
        _ ≤ ‖y‖ := PiLp.norm_apply_le y k
    -- the gain on `M` is at most `‖x‖₂ / ‖y‖_∞`
    have hgain : c * ‖y‖ ≤ ‖x‖ := by
      have h := gainOnSubspace_le_div (S := idEmbed (𝕜 := 𝕜) (m := N) 2 ∞) hyM hy0
      rw [hid, le_div_iff₀ hypos] at h
      exact h
    have h1 : c * s k ≤ ‖x‖ :=
      (mul_le_mul_of_nonneg_left hyk hc0).trans hgain
    have h2 : (c * s k) ^ 2 ≤ s k := by
      calc (c * s k) ^ 2 ≤ ‖x‖ ^ 2 := pow_le_pow_left₀ (by positivity) h1 2
        _ = s k := hxnorm
    have h3 : c ^ 2 * s k * s k ≤ 1 * s k := by nlinarith [h2]
    exact le_of_mul_le_mul_right h3 hsk
  -- sum over the coordinates
  have hsum : ∑ k, s k = n + 1 := by
    simp only [hs_apply]
    rw [sum_sum_norm_sq_apply b, Fintype.card_fin, hd, Nat.cast_add, Nat.cast_one]
  have hmain : c ^ 2 * (n + 1) ≤ N := by
    calc c ^ 2 * (n + 1) = ∑ k, c ^ 2 * s k := by rw [← Finset.mul_sum, hsum]
      _ ≤ ∑ _k : Fin N, (1 : ℝ) := Finset.sum_le_sum fun k _ => hkey k
      _ = N := by simp
  rw [Real.le_sqrt hc0 (by positivity), le_div_iff₀ (by positivity)]
  exact hmain

/-! ## Multiplicativity fails -/

/-- `ℓ₂ᴺ → ℓ∞ᴺ → ℓ₂ᴺ` is the identity of `ℓ₂ᴺ`. -/
lemma idEmbed_two_infty_comp_idEmbed_infty_two (N : ℕ) :
    (idEmbed (𝕜 := 𝕜) (m := N) 2 ∞).comp (idEmbed ∞ 2) =
      ContinuousLinearMap.id 𝕜 (PiLp 2 (fun _ : Fin N => 𝕜)) := by
  refine ContinuousLinearMap.ext fun x => ?_
  rfl

/-- **The counterexample to multiplicativity.** For `T = id : ℓ₂³ → ℓ∞³` and
`S = id : ℓ∞³ → ℓ₂³`, `b₁(S) · b₁(T) < b₂(S ∘ T) = 1`. -/
theorem bernsteinNumber_mul_lt_comp :
    bernsteinNumber (idEmbed (𝕜 := 𝕜) (m := 3) 2 ∞) 1 *
        bernsteinNumber (idEmbed (𝕜 := 𝕜) (m := 3) ∞ 2) 1 <
      bernsteinNumber ((idEmbed (𝕜 := 𝕜) (m := 3) 2 ∞).comp (idEmbed ∞ 2)) (1 + 1) := by
  rw [idEmbed_two_infty_comp_idEmbed_infty_two,
    bernsteinNumber_strict _ (Module.lt_rank_of_lt_finrank (by rw [finrank_piLp]; norm_num))]
  have hS : bernsteinNumber (idEmbed (𝕜 := 𝕜) (m := 3) 2 ∞) 1 ≤ Real.sqrt (3 / 2) := by
    convert bernsteinNumber_idEmbed_infty_two_le (𝕜 := 𝕜) 3 1 using 2; norm_num
  have hT : bernsteinNumber (idEmbed (𝕜 := 𝕜) (m := 3) ∞ 2) 1 ≤ 1 / Real.sqrt 2 := by
    convert bernsteinNumber_idEmbed_two_infty_le (𝕜 := 𝕜) 3 1 using 3; norm_num
  -- `√(3/2) · (1/√2) < 1`, since `3/2 < 2`
  have hlt : Real.sqrt (3 / 2) * (1 / Real.sqrt 2) < 1 := by
    rw [mul_one_div, div_lt_one (Real.sqrt_pos.mpr (by norm_num))]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  calc bernsteinNumber (idEmbed (𝕜 := 𝕜) (m := 3) 2 ∞) 1 *
        bernsteinNumber (idEmbed (𝕜 := 𝕜) (m := 3) ∞ 2) 1
      ≤ Real.sqrt (3 / 2) * (1 / Real.sqrt 2) :=
        mul_le_mul hS hT (bernsteinNumber_nonneg _ _) (Real.sqrt_nonneg _)
    _ < 1 := hlt

/-- **The Bernstein numbers are not multiplicative.** -/
theorem _root_.SNumbers.not_multiplicative_bernsteinNumber :
    ¬ Multiplicative (𝕜 := 𝕜) (fun {_X _Y} _ _ _ _ S n => bernsteinNumber S n) := fun h =>
  lt_irrefl _ (bernsteinNumber_mul_lt_comp.trans_le
    (h (idEmbed (𝕜 := 𝕜) (m := 3) 2 ∞) (idEmbed ∞ 2) 1 1))

/-! ## Additivity fails -/

/-- The space `ℓ₂⁷¹ × ℓ∞⁷¹`, normed by the maximum of the two norms. -/
abbrev L2LinfProd (𝕜 : Type u) [RCLike 𝕜] : Type u :=
  PiLp 2 (fun _ : Fin 71 => 𝕜) × PiLp ∞ (fun _ : Fin 71 => 𝕜)

/-- The operator `S (x, y) = (0, x)` on `ℓ₂⁷¹ × ℓ∞⁷¹`. -/
noncomputable def crossS : L2LinfProd 𝕜 →L[𝕜] L2LinfProd 𝕜 :=
  (inr 𝕜 _ _).comp ((idEmbed (𝕜 := 𝕜) (m := 71) ∞ 2).comp (fst 𝕜 _ _))

/-- The operator `T (x, y) = (y/9, 0)` on `ℓ₂⁷¹ × ℓ∞⁷¹`. -/
noncomputable def crossT : L2LinfProd 𝕜 →L[𝕜] L2LinfProd 𝕜 :=
  (inl 𝕜 _ _).comp ((idEmbed (𝕜 := 𝕜) (m := 71) 2 ∞).comp ((9 : 𝕜)⁻¹ • snd 𝕜 _ _))

/-- The graph map `x ↦ (x, 3x)` from `ℓ₂⁷¹` into `ℓ₂⁷¹ × ℓ∞⁷¹`. -/
noncomputable def graphThree : PiLp 2 (fun _ : Fin 71 => 𝕜) →L[𝕜] L2LinfProd 𝕜 :=
  (ContinuousLinearMap.id 𝕜 _).prod ((3 : 𝕜) • idEmbed (𝕜 := 𝕜) (m := 71) ∞ 2)

/-- On the graph of `x ↦ 3x`, the operator `S + T` is multiplication by `1/3`:
`(S + T)(x, 3x) = (x/3, x)`. -/
lemma crossS_add_crossT_graphThree (x : PiLp 2 (fun _ : Fin 71 => 𝕜)) :
    (crossS + crossT : L2LinfProd 𝕜 →L[𝕜] L2LinfProd 𝕜) (graphThree x) =
      (3 : 𝕜)⁻¹ • graphThree x := by
  refine Prod.ext ?_ ?_
  · ext i
    simp [crossS, crossT, graphThree]
    ring
  · ext i
    simp [crossS, crossT, graphThree]

/-- `b₇₀(S + T) ≥ 1/3`: the gain of `S + T` on the `71`-dimensional graph of `x ↦ 3x` is
exactly `1/3`. -/
lemma inv_three_le_bernsteinNumber_crossS_add_crossT :
    (3 : ℝ)⁻¹ ≤ bernsteinNumber (crossS (𝕜 := 𝕜) + crossT) (35 + 35) := by
  set E : Submodule 𝕜 (L2LinfProd 𝕜) :=
    LinearMap.range (graphThree (𝕜 := 𝕜) : PiLp 2 (fun _ : Fin 71 => 𝕜) →ₗ[𝕜] L2LinfProd 𝕜)
    with hE
  have hinj : Function.Injective
      (graphThree (𝕜 := 𝕜) : PiLp 2 (fun _ : Fin 71 => 𝕜) →ₗ[𝕜] L2LinfProd 𝕜) :=
    fun x y h => congrArg Prod.fst h
  have hE_rank : Module.rank 𝕜 E = ((35 + 35 + 1 : ℕ) : Cardinal) := by
    rw [hE, rank_range_of_injective _ hinj, ← Module.finrank_eq_rank, finrank_piLp]
  have hE_ne : E ≠ ⊥ := fun h => by
    rw [h, rank_bot] at hE_rank
    exact Nat.succ_ne_zero (35 + 35) (by exact_mod_cast hE_rank.symm)
  refine le_trans ?_ (le_csSup (bddAbove_bernsteinSet _ _) ⟨E, hE_rank, rfl⟩)
  refine le_gainOnSubspace hE_ne fun z hz hz0 => ?_
  obtain ⟨x, rfl⟩ := LinearMap.mem_range.mp hz
  simp only [ContinuousLinearMap.coe_coe] at hz0 ⊢
  rw [crossS_add_crossT_graphThree, norm_smul, mul_div_assoc,
    div_self (norm_ne_zero_iff.mpr hz0), mul_one, norm_inv, RCLike.norm_ofNat]

/-- `b₃₅(S) ≤ 1/6`, from `b₃₅(id : ℓ₂⁷¹ → ℓ∞⁷¹) ≤ 1/√36`. -/
lemma bernsteinNumber_crossS_le : bernsteinNumber (crossS (𝕜 := 𝕜)) 35 ≤ 1 / 6 := by
  have h : bernsteinNumber (crossS (𝕜 := 𝕜)) 35 ≤
      ‖inr 𝕜 (PiLp 2 (fun _ : Fin 71 => 𝕜)) (PiLp ∞ (fun _ : Fin 71 => 𝕜))‖ *
        bernsteinNumber (idEmbed (𝕜 := 𝕜) (m := 71) ∞ 2) 35 *
        ‖fst 𝕜 (PiLp 2 (fun _ : Fin 71 => 𝕜)) (PiLp ∞ (fun _ : Fin 71 => 𝕜))‖ :=
    bernsteinNumber_comp_comp_le _ _ _ 35
  have hB : bernsteinNumber (idEmbed (𝕜 := 𝕜) (m := 71) ∞ 2) 35 ≤ 1 / 6 := by
    have h6 : Real.sqrt (((35 : ℕ) : ℝ) + 1) = 6 := by
      rw [show ((35 : ℕ) : ℝ) + 1 = 6 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    have := bernsteinNumber_idEmbed_two_infty_le (𝕜 := 𝕜) 71 35
    rwa [h6] at this
  calc bernsteinNumber (crossS (𝕜 := 𝕜)) 35
      ≤ ‖inr 𝕜 (PiLp 2 (fun _ : Fin 71 => 𝕜)) (PiLp ∞ (fun _ : Fin 71 => 𝕜))‖ *
          bernsteinNumber (idEmbed (𝕜 := 𝕜) (m := 71) ∞ 2) 35 *
          ‖fst 𝕜 (PiLp 2 (fun _ : Fin 71 => 𝕜)) (PiLp ∞ (fun _ : Fin 71 => 𝕜))‖ := h
    _ ≤ 1 * (1 / 6) * 1 :=
        mul_le_mul (mul_le_mul (norm_inr_le_one 𝕜 _ _) hB (bernsteinNumber_nonneg _ _) zero_le_one)
          (ContinuousLinearMap.norm_fst_le 𝕜 _ _) (norm_nonneg _) (by norm_num)
    _ = 1 / 6 := by norm_num

/-- `b₃₅(T) ≤ √(71/36)/9`, from `b₃₅(id : ℓ∞⁷¹ → ℓ₂⁷¹) ≤ √(71/36)`. -/
lemma bernsteinNumber_crossT_le :
    bernsteinNumber (crossT (𝕜 := 𝕜)) 35 ≤ Real.sqrt (71 / 36) / 9 := by
  have h : bernsteinNumber (crossT (𝕜 := 𝕜)) 35 ≤
      ‖inl 𝕜 (PiLp 2 (fun _ : Fin 71 => 𝕜)) (PiLp ∞ (fun _ : Fin 71 => 𝕜))‖ *
        bernsteinNumber (idEmbed (𝕜 := 𝕜) (m := 71) 2 ∞) 35 *
        ‖(9 : 𝕜)⁻¹ • snd 𝕜 (PiLp 2 (fun _ : Fin 71 => 𝕜)) (PiLp ∞ (fun _ : Fin 71 => 𝕜))‖ :=
    bernsteinNumber_comp_comp_le _ _ _ 35
  have hB : bernsteinNumber (idEmbed (𝕜 := 𝕜) (m := 71) 2 ∞) 35 ≤ Real.sqrt (71 / 36) := by
    convert bernsteinNumber_idEmbed_infty_two_le (𝕜 := 𝕜) 71 35 using 2; norm_num
  have hsnd : ‖(9 : 𝕜)⁻¹ •
      snd 𝕜 (PiLp 2 (fun _ : Fin 71 => 𝕜)) (PiLp ∞ (fun _ : Fin 71 => 𝕜))‖ ≤ 9⁻¹ := by
    calc _ ≤ ‖(9 : 𝕜)⁻¹‖ *
          ‖snd 𝕜 (PiLp 2 (fun _ : Fin 71 => 𝕜)) (PiLp ∞ (fun _ : Fin 71 => 𝕜))‖ :=
          norm_smul_le _ _
      _ ≤ 9⁻¹ * 1 := by
          rw [norm_inv, RCLike.norm_ofNat]
          exact mul_le_mul_of_nonneg_left (ContinuousLinearMap.norm_snd_le 𝕜 _ _) (by norm_num)
      _ = 9⁻¹ := mul_one _
  calc bernsteinNumber (crossT (𝕜 := 𝕜)) 35
      ≤ ‖inl 𝕜 (PiLp 2 (fun _ : Fin 71 => 𝕜)) (PiLp ∞ (fun _ : Fin 71 => 𝕜))‖ *
          bernsteinNumber (idEmbed (𝕜 := 𝕜) (m := 71) 2 ∞) 35 *
          ‖(9 : 𝕜)⁻¹ • snd 𝕜 (PiLp 2 (fun _ : Fin 71 => 𝕜)) (PiLp ∞ (fun _ : Fin 71 => 𝕜))‖ :=
        h
    _ ≤ 1 * Real.sqrt (71 / 36) * 9⁻¹ :=
        mul_le_mul (mul_le_mul (norm_inl_le_one 𝕜 _ _) hB (bernsteinNumber_nonneg _ _) zero_le_one)
          hsnd (norm_nonneg _) (by positivity)
    _ = Real.sqrt (71 / 36) / 9 := by ring

/-- **The counterexample to additivity.** On `ℓ₂⁷¹ × ℓ∞⁷¹`, with `S (x, y) = (0, x)` and
`T (x, y) = (y/9, 0)`, `b₃₅(S) + b₃₅(T) < b₇₀(S + T)`. -/
theorem bernsteinNumber_add_lt :
    bernsteinNumber (crossS (𝕜 := 𝕜)) 35 + bernsteinNumber (crossT (𝕜 := 𝕜)) 35 <
      bernsteinNumber (crossS (𝕜 := 𝕜) + crossT) (35 + 35) := by
  have hS := bernsteinNumber_crossS_le (𝕜 := 𝕜)
  have hT := bernsteinNumber_crossT_le (𝕜 := 𝕜)
  have h := inv_three_le_bernsteinNumber_crossS_add_crossT (𝕜 := 𝕜)
  -- `√(71/36) < 3/2`, since `71/36 < 81/36`
  have hsqrt : Real.sqrt (71 / 36) < 3 / 2 := (Real.sqrt_lt' (by norm_num)).mpr (by norm_num)
  linarith

/-- **The Bernstein numbers are not additive.** -/
theorem _root_.SNumbers.not_additive_bernsteinNumber :
    ¬ Additive (𝕜 := 𝕜) (fun {_X _Y} _ _ _ _ S n => bernsteinNumber S n) := fun h =>
  lt_irrefl _ (bernsteinNumber_add_lt.trans_le (h (crossS (𝕜 := 𝕜)) crossT 35 35))

end SNumbers.L2Linf
