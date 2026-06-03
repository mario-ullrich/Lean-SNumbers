/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.Normed.Operator.Compact.Basic
import SNumbers.Approximation

/-!
# Singular value decomposition of a Hilbert-space operator

A non-negative real `σ` is a *singular value* of `S : H₁ →L[𝕜] H₂` if
there is a *singular vector pair* `(u, v)`: unit vectors `u ∈ H₁`,
`v ∈ H₂` with `S u = σ • v` and `S* v = σ • u`.

This file develops the SVD of a compact operator via the **singular-value
iteration** (peeling off the top singular pair given by
`norm_isSingularValue`), and the **scalar factorisation** for general
operators that the `s`-numbers uniqueness theorem consumes.

## Main results

* `SVD.IsCompactOperator.norm_isSingularValue` (Pietsch §2.11.7) — every
  compact operator attains its operator norm as a singular value
  (**proved**).
* `SVD.IsCompactOperator.SVD` (Pietsch §2.11.8) — the singular value
  decomposition / Schmidt representation `S x = Σ aₖ ⟨uₖ,x⟩ vₖ`. Needs the
  *infinite* iteration plus the convergence facts `σₖ → 0`, `HasSum`.
* `SVD.IsCompactOperator.truncation_residual_eq_approxNumber` — Eckart–Young
  `‖S - Sₙ‖ = aₙ(S)`, identifying singular values with approximation
  numbers.
* `SVD.IsCompactOperator.diagonalFactorisation` — the factorisation
  `B ∘ S ∘ A = diag(a₀, …, aₙ)` through `ℓ₂ⁿ⁺¹`. Needs only the **top
  `n+1` singular pairs** — a *finite* truncation, a sibling of `SVD`, and
  (pinning the exact `aₖ`) requires `S` compact.
* `SVD.exists_scalar_factorisation` — `B ∘ S ∘ A = c • id` for `c < aₙ(S)`,
  for an **arbitrary bounded** `S`. This is the single SVD input consumed
  by `SNumbers.Uniqueness`.

All four are currently stated with `sorry`; `norm_isSingularValue` — the
analytic heart — is proved.
-/

universe u

open Filter Topology

namespace SVD

variable {𝕜 : Type u} [RCLike 𝕜]
variable {H₁ H₂ : Type u}
variable [NormedAddCommGroup H₁] [InnerProductSpace 𝕜 H₁] [CompleteSpace H₁]
variable [NormedAddCommGroup H₂] [InnerProductSpace 𝕜 H₂] [CompleteSpace H₂]

/-- A non-negative real `σ` is a **singular value** of `S` if there exist
unit vectors `u ∈ H₁`, `v ∈ H₂` with `S u = σ • v` and `S* v = σ • u`. -/
def IsSingularValue (S : H₁ →L[𝕜] H₂) (σ : ℝ) : Prop :=
  ∃ u : H₁, ∃ v : H₂, ‖u‖ = 1 ∧ ‖v‖ = 1 ∧
    S u = (σ : 𝕜) • v ∧ S.adjoint v = (σ : 𝕜) • u

private lemma exists_unit (H : Type u) [NormedAddCommGroup H]
    [InnerProductSpace 𝕜 H] [Nontrivial H] : ∃ u : H, ‖u‖ = 1 :=
  let ⟨x, hx⟩ := exists_ne (0 : H)
  ⟨(‖x‖ : 𝕜)⁻¹ • x, by
    simp [norm_smul, inv_mul_cancel₀ (norm_pos_iff.mpr hx).ne']⟩

/-- **Pietsch §2.11.7.** Every compact operator between Hilbert spaces
attains its norm as a singular value: there exist unit vectors `u`, `v`
with `S u = ‖S‖ • v` and `S* v = ‖S‖ • u`.

Proof sketch: take a maximising sequence `xₙ` (unit, `‖S xₙ‖ → ‖S‖`),
extract a strongly convergent subsequence `S xₙₖ → y` by compactness,
let `v := ‖S‖⁻¹ • y` and `u' := S* v`. Cauchy–Schwarz on
`⟨u', xₙₖ⟩ = ⟨v, S xₙₖ⟩ → ‖S‖` shows `‖u'‖ = ‖S‖`; equality in C–S
forces `xₙₖ → ‖S‖⁻¹ • u' =: u`, so by continuity `S u = y = ‖S‖ • v`. -/
theorem IsCompactOperator.norm_isSingularValue
    [Nontrivial H₁] [Nontrivial H₂]
    {S : H₁ →L[𝕜] H₂} (hS : IsCompactOperator S) :
    IsSingularValue S ‖S‖ := by
  obtain ⟨u₀, hu₀⟩ := exists_unit (𝕜 := 𝕜) H₁
  obtain ⟨v₀, hv₀⟩ := exists_unit (𝕜 := 𝕜) H₂
  -- Trivial case: ‖S‖ = 0, so S = 0 and any unit pair works.
  by_cases hS0 : ‖S‖ = 0
  · have hSu : S u₀ = 0 := by
      have h := S.le_opNorm u₀; simp [hS0, hu₀] at h; exact h
    have hSv : S.adjoint v₀ = 0 := by
      have h := S.adjoint.le_opNorm v₀
      rw [LinearIsometryEquiv.norm_map ContinuousLinearMap.adjoint S] at h
      simp [hS0, hv₀] at h; exact h
    exact ⟨u₀, v₀, hu₀, hv₀, by simp [hSu, hS0], by simp [hSv, hS0]⟩
  -- Main case: ‖S‖ > 0.
  have hpos : 0 < ‖S‖ := (norm_nonneg _).lt_of_ne (Ne.symm hS0)
  have hKne : (‖S‖ : 𝕜) ≠ 0 := by exact_mod_cast hS0
  -- Step 1. Maximising sequence (xₙ) of unit vectors with ‖S xₙ‖ → ‖S‖.
  have hmax : ∀ n : ℕ, ∃ x : H₁, ‖x‖ = 1 ∧ ‖S‖ - 1 / ((n : ℝ) + 1) ≤ ‖S x‖ := fun n => by
    by_cases h : ‖S‖ ≤ 1 / ((n : ℝ) + 1)
    · exact ⟨u₀, hu₀, by linarith [norm_nonneg (S u₀)]⟩
    push Not at h
    have hε : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    obtain ⟨z, hz_lt, hz_app⟩ := S.exists_lt_apply_of_lt_opNorm
      (show ‖S‖ - 1 / ((n : ℝ) + 1) < ‖S‖ by linarith)
    have hSz_pos : 0 < ‖S z‖ := lt_of_le_of_lt (by linarith) hz_app
    have hz_pos : 0 < ‖z‖ := norm_pos_iff.mpr fun hz => by
      rw [hz, map_zero, norm_zero] at hSz_pos; exact lt_irrefl 0 hSz_pos
    refine ⟨(‖z‖ : 𝕜)⁻¹ • z, ?_, ?_⟩
    · simp [norm_smul, inv_mul_cancel₀ hz_pos.ne']
    rw [map_smul, norm_smul, norm_inv, RCLike.norm_ofReal, abs_of_pos hz_pos,
      show ‖z‖⁻¹ * ‖S z‖ = ‖S z‖ / ‖z‖ from by ring, le_div_iff₀ hz_pos]
    calc (‖S‖ - 1 / ((n : ℝ) + 1)) * ‖z‖
        ≤ (‖S‖ - 1 / ((n : ℝ) + 1)) * 1 := by
          apply mul_le_mul_of_nonneg_left hz_lt.le; linarith
      _ = ‖S‖ - 1 / ((n : ℝ) + 1) := mul_one _
      _ ≤ ‖S z‖ := hz_app.le
  choose x hxu hxb using hmax
  have hxle : ∀ n, ‖S (x n)‖ ≤ ‖S‖ := fun n => by
    have := S.le_opNorm (x n); simp [hxu n] at this; exact this
  have hxlim : Tendsto (fun n => ‖S (x n)‖) atTop (𝓝 ‖S‖) := by
    have h0 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have hlo : Tendsto (fun n : ℕ => ‖S‖ - 1 / ((n : ℝ) + 1)) atTop (𝓝 ‖S‖) := by
      simpa using tendsto_const_nhds.sub h0
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlo tendsto_const_nhds hxb hxle
  -- Step 2. Extract a subsequence with `S (x ∘ φ) → y`, `‖y‖ = ‖S‖`.
  obtain ⟨y, _, φ, hφ, hφl⟩ := (hS.isCompact_closure_image_closedBall (1 : ℝ)).tendsto_subseq
    fun n => subset_closure ⟨x n, by simp [hxu n], rfl⟩
  have hy : ‖y‖ = ‖S‖ := tendsto_nhds_unique
    ((continuous_norm.tendsto _).comp hφl) (hxlim.comp hφ.tendsto_atTop)
  -- Step 3. v := ‖S‖⁻¹ • y is a unit vector; u' := S* v has ‖u'‖ ≤ ‖S‖.
  set v : H₂ := (‖S‖ : 𝕜)⁻¹ • y with hvdef
  have hv1 : ‖v‖ = 1 := by
    simp [hvdef, norm_smul, norm_inv, hy, inv_mul_cancel₀ hpos.ne']
  set u' : H₁ := S.adjoint v with hu'def
  have hu'le : ‖u'‖ ≤ ‖S‖ := by
    calc ‖u'‖ ≤ ‖S.adjoint‖ * ‖v‖ := S.adjoint.le_opNorm v
      _ = ‖S‖ := by rw [LinearIsometryEquiv.norm_map, hv1, mul_one]
  -- ⟨u', xφₙ⟩ = ⟨v, S xφₙ⟩ → ⟨v, y⟩ = (‖S‖ : 𝕜).
  have hvy : (inner 𝕜 v y : 𝕜) = (‖S‖ : 𝕜) := by
    rw [hvdef, inner_smul_left, map_inv₀, RCLike.conj_ofReal,
      inner_self_eq_norm_sq_to_K (𝕜 := 𝕜) y, hy, sq, ← mul_assoc,
      inv_mul_cancel₀ hKne, one_mul]
  have hil : Tendsto (fun n => inner 𝕜 u' (x (φ n))) atTop (𝓝 (‖S‖ : 𝕜)) := by
    have h : Tendsto (fun n => inner 𝕜 v (S (x (φ n)))) atTop (𝓝 (‖S‖ : 𝕜)) := by
      rw [← hvy]; exact tendsto_const_nhds.inner hφl
    exact h.congr fun n => (S.adjoint_inner_left _ _).symm
  -- ‖u'‖ ≥ ‖S‖ via Cauchy–Schwarz on the limit.
  have hu'ge : ‖S‖ ≤ ‖u'‖ := by
    have hN : ‖(‖S‖ : 𝕜)‖ = ‖S‖ := by rw [RCLike.norm_ofReal, abs_of_pos hpos]
    have hlim := (continuous_norm.tendsto _).comp hil
    rw [hN] at hlim
    refine le_of_tendsto' hlim fun n => ?_
    have h : ‖inner 𝕜 u' (x (φ n))‖ ≤ ‖u'‖ * ‖x (φ n)‖ := norm_inner_le_norm _ _
    simp [hxu (φ n)] at h; exact h
  have hu'eq : ‖u'‖ = ‖S‖ := le_antisymm hu'le hu'ge
  -- Step 4. u := ‖S‖⁻¹ • u' is a unit vector; the C–S equality limit gives xφₙ → u.
  set u : H₁ := (‖S‖ : 𝕜)⁻¹ • u' with hudef
  have hu1 : ‖u‖ = 1 := by
    simp [hudef, norm_smul, norm_inv, hu'eq, inv_mul_cancel₀ hpos.ne']
  have hi1 : Tendsto (fun n => inner 𝕜 (x (φ n)) u) atTop (𝓝 (1 : 𝕜)) := by
    -- ⟨xφₙ, u'⟩ = star ⟨u', xφₙ⟩ → star (‖S‖ : 𝕜) = (‖S‖ : 𝕜).
    have hswap : Tendsto (fun n => inner 𝕜 (x (φ n)) u') atTop (𝓝 (‖S‖ : 𝕜)) := by
      have h := (continuous_star.tendsto _).comp hil
      rw [show star (‖S‖ : 𝕜) = (‖S‖ : 𝕜) from RCLike.conj_ofReal _] at h
      exact h.congr fun n => inner_conj_symm _ _
    -- ⟨xφₙ, u⟩ = ‖S‖⁻¹ * ⟨xφₙ, u'⟩ → ‖S‖⁻¹ * ‖S‖ = 1.
    have hmul : Tendsto (fun n => (‖S‖ : 𝕜)⁻¹ * inner 𝕜 (x (φ n)) u') atTop
        (𝓝 ((‖S‖ : 𝕜)⁻¹ * (‖S‖ : 𝕜))) := tendsto_const_nhds.mul hswap
    rw [inv_mul_cancel₀ hKne] at hmul
    exact hmul.congr fun n => by rw [hudef, inner_smul_right]
  have hxu_lim : Tendsto (fun n => x (φ n)) atTop (𝓝 u) := by
    -- ‖xφₙ - u‖² = 2 - 2 Re ⟨xφₙ, u⟩ → 0; hence ‖xφₙ - u‖ → 0.
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hre : Tendsto (fun n => RCLike.re (inner 𝕜 (x (φ n)) u)) atTop (𝓝 1) := by
      simpa [Function.comp_def] using (RCLike.continuous_re.tendsto _).comp hi1
    have hsq : Tendsto (fun n => ‖x (φ n) - u‖ ^ 2) atTop (𝓝 0) := by
      have hsub : Tendsto (fun n => (2 : ℝ) - 2 * RCLike.re (inner 𝕜 (x (φ n)) u)) atTop
          (𝓝 ((2 : ℝ) - 2 * 1)) := tendsto_const_nhds.sub (hre.const_mul 2)
      rw [show ((2 : ℝ) - 2 * 1 : ℝ) = 0 by ring] at hsub
      exact hsub.congr fun n => by
        rw [@norm_sub_sq 𝕜 _ _ _ _ _ _, hxu (φ n), hu1]; ring
    have hsqrt := (Real.continuous_sqrt.tendsto _).comp hsq
    rw [Real.sqrt_zero] at hsqrt
    exact hsqrt.congr fun n => Real.sqrt_sq (norm_nonneg _)
  -- Step 5. Continuity of S: `S u = lim S xφₙ = y = ‖S‖ • v`; `S* v = u' = ‖S‖ • u`.
  have h1 : Tendsto (fun n => S (x (φ n))) atTop (𝓝 (S u)) :=
    (S.continuous.tendsto _).comp hxu_lim
  have h2 : Tendsto (fun n => S (x (φ n))) atTop (𝓝 y) := hφl
  have hSu : S u = y := tendsto_nhds_unique h1 h2
  refine ⟨u, v, hu1, hv1, ?_, ?_⟩
  · rw [hSu, hvdef, smul_smul, mul_inv_cancel₀ hKne, one_smul]
  · rw [hudef, smul_smul, mul_inv_cancel₀ hKne, one_smul]

/-- **Singular value decomposition / Schmidt representation
(Pietsch §2.11.8).** Every compact operator between Hilbert spaces has a
Schmidt expansion

  `S x = Σ σₖ ⟨uₖ, x⟩ vₖ`,

with orthonormal sequences `(uₖ) ⊆ H₁`, `(vₖ) ⊆ H₂` and singular values
`σ₀ ≥ σ₁ ≥ ⋯ → 0`.

**Proof outline** (Pietsch 2.11.8, by iterating `norm_isSingularValue`):

1. *Iteration.* Set `S₀ := S`. Given `Sₙ` (compact), apply
   `IsCompactOperator.norm_isSingularValue` to obtain unit vectors
   `uₙ, vₙ` with `Sₙ uₙ = ‖Sₙ‖ • vₙ` and `Sₙ* vₙ = ‖Sₙ‖ • uₙ`. Set
   `σₙ := ‖Sₙ‖` and `Sₙ₊₁ := Sₙ - σₙ • rankOne 𝕜 vₙ uₙ`. The rank-one
   subtrahend is compact (its image is finite-dimensional), and
   `IsCompactOperator` is closed under subtraction
   (`IsCompactOperator.sub`), so the recursion stays inside the
   compact-operator class.

2. *Orthogonality.* By construction `Sₙ₊₁ uₙ = 0`, so by induction
   `Sₘ uₙ = 0` for all `m > n`. The variational characterisation of
   `uₘ` (the maximiser of `‖Sₘ x‖` on the unit sphere) then forces
   `uₘ ⊥ uₙ`: writing `uₘ = α uₙ + w` with `w ⊥ uₙ` and using
   `‖Sₘ uₘ‖² = ‖Sₘ w‖² ≤ ‖Sₘ‖² (1 - |α|²) = σₘ² (1 - |α|²)`
   together with `‖Sₘ uₘ‖ = σₘ` gives `α = 0` (assuming `σₘ > 0`).
   Symmetrically, `vₘ ⊥ vₙ` (using `Sₙ₊₁* vₙ = 0`).

3. *`σₙ → 0`.* Since `S uₙ = σₙ vₙ` (using `uₙ ⊥ uₘ` for `m < n`) and
   the `vₙ` are orthonormal, `‖S uₙ - S uₘ‖² = σₙ² + σₘ²`. If `σₙ`
   stayed `≥ ε > 0`, the bounded sequence `(uₙ)` would map under `S`
   to a sequence with no Cauchy subsequence, contradicting
   compactness of `S`.

4. *Convergence.* `‖S - Σₖ<n σₖ • rankOne 𝕜 vₖ uₖ‖ = ‖Sₙ‖ = σₙ → 0`,
   so the Schmidt partial sums converge to `S` in operator norm; the
   pointwise `HasSum` follows. -/
theorem IsCompactOperator.SVD
    [Nontrivial H₁] [Nontrivial H₂]
    {S : H₁ →L[𝕜] H₂} (hS : IsCompactOperator S) :
    ∃ (σ : ℕ → ℝ) (u : ℕ → H₁) (v : ℕ → H₂),
      Orthonormal 𝕜 u ∧ Orthonormal 𝕜 v ∧
      Tendsto σ atTop (𝓝 0) ∧
      ∀ x : H₁, HasSum (fun k => ((σ k : 𝕜) * inner 𝕜 (u k) x) • v k) (S x) := by
  sorry

/-! ### Eckart–Young: singular values are the approximation numbers

The truncation `Sₙ := Σ_{k < n} σₖ ⟨uₖ, ·⟩ vₖ` is the best rank-`n`
approximation, with residual `‖S - Sₙ‖ = σₙ`. Since the truncation has
rank `≤ n`, this is `≥ aₙ(S)`, and minimality gives equality: the `k`-th
singular value equals the `k`-th approximation number, `σₖ = aₖ(S)`. -/

/-- **Eckart–Young.** Some rank-`n` operator `L` attains the approximation
number: `‖S - L‖ = aₙ(S)` (the truncated SVD). In particular the infimum
defining `aₙ(S)` is attained on Hilbert spaces. -/
theorem IsCompactOperator.truncation_residual_eq_approxNumber
    {S : H₁ →L[𝕜] H₂} (hS : IsCompactOperator S) (n : ℕ) :
    ∃ L : H₁ →L[𝕜] H₂, L.rank ≤ (n : Cardinal) ∧
      ‖S - L‖ = SNumbers.approximationNumber S n := by
  sorry

/-! ### Diagonal factorisation through `ℓ₂ⁿ⁺¹`

`B ∘ S ∘ A = diag(a₀, …, aₙ)`, with `A : ℓ₂ⁿ⁺¹ → H₁` the isometric inclusion
`eₖ ↦ uₖ` and `B : H₂ → ℓ₂ⁿ⁺¹` the contraction `y ↦ Σ_{k ≤ n} ⟨vₖ, y⟩ eₖ`.

**This uses only the top `n+1` singular pairs** `(uₖ, vₖ, σₖ)_{k ≤ n}` — a
*finite* slice of the SVD obtained by `n+1` iterations of
`norm_isSingularValue`. It needs neither `σₖ → 0` nor the `HasSum`
convergence of the full `SVD`, so it is a **sibling** of `SVD`, not a
corollary. (Identifying `σₖ = aₖ` is Eckart–Young above.) -/

/-- **Diagonal factorisation through `ℓ₂ⁿ⁺¹`.** There is an isometric
inclusion `A : ℓ₂ⁿ⁺¹ →L[𝕜] H₁` with `‖A‖ ≤ 1` and a contraction
`B : H₂ →L[𝕜] ℓ₂ⁿ⁺¹` with `‖B‖ ≤ 1` such that on each basis vector,

```
(B ∘ S ∘ A)(eₖ) = aₖ(S) · eₖ,
```

i.e. `B ∘ S ∘ A = diag(a₀(S), …, aₙ(S))`. Built from the top `n+1` singular
pairs only. -/
theorem IsCompactOperator.diagonalFactorisation
    [Nontrivial H₁] [Nontrivial H₂]
    {S : H₁ →L[𝕜] H₂} (hS : IsCompactOperator S) (n : ℕ) :
    ∃ (A : EuclideanSpace 𝕜 (Fin (n + 1)) →L[𝕜] H₁)
      (B : H₂ →L[𝕜] EuclideanSpace 𝕜 (Fin (n + 1))),
      ‖A‖ ≤ 1 ∧ ‖B‖ ≤ 1 ∧
      ∀ k : Fin (n + 1),
        B (S (A (EuclideanSpace.single k (1 : 𝕜)))) =
          (SNumbers.approximationNumber S k : 𝕜) •
            EuclideanSpace.single k (1 : 𝕜) := by
  sorry

/-! ### Scalar factorisation (general operators)

Whereas `diagonalFactorisation` pins the *exact* values `aₖ` (so needs `S`
compact, see its note), the **scalar factorisation** asks only for
`B ∘ S ∘ A = c • id` with `c < aₙ(S)` strict. It therefore holds for an
**arbitrary** bounded `S`: for `c < aₙ(S)` there is an `(n+1)`-dimensional
subspace `M ⊆ H₁` on which `‖S x‖ ≥ c ‖x‖` (the variational characterisation
of `aₙ`, valid even when `aₙ(S)` is *not* attained — e.g. continuous
spectrum); take `A` to embed `ℓ₂ⁿ⁺¹` isometrically onto `M`, and `B` to be
`c` times a left inverse of the bounded-below `S|_M`.

This is the **single input** the uniqueness theorem for `s`-numbers
(`SNumbers.Uniqueness`) consumes: chaining (S3) over `B ∘ S ∘ A = c • id`
with the (S5) normalisation `sₙ(id) = 1` gives `c ≤ sₙ(S)` for every
`c < aₙ(S)`, hence `aₙ(S) ≤ sₙ(S)`. -/

/-- **Scalar factorisation.** For any bounded `S : H₁ →L[𝕜] H₂` between
Hilbert spaces and any real `c` with `0 ≤ c < aₙ(S)`, there are contractions
`A : ℓ₂ⁿ⁺¹ →L[𝕜] H₁`, `B : H₂ →L[𝕜] ℓ₂ⁿ⁺¹` with

```
B ∘ S ∘ A = c • id_{ℓ₂ⁿ⁺¹}.
```

**Status: `sorry`** — the one SVD blackbox the s-numbers development rests
on. (No compactness needed: the strict `c < aₙ(S)` only requires an
approximate `(n+1)`-dimensional lower bound, available for every bounded
operator.) -/
theorem exists_scalar_factorisation
    (S : H₁ →L[𝕜] H₂) (n : ℕ) {c : ℝ}
    (hc0 : 0 ≤ c) (hc : c < SNumbers.approximationNumber S n) :
    ∃ (A : EuclideanSpace 𝕜 (Fin (n + 1)) →L[𝕜] H₁)
      (B : H₂ →L[𝕜] EuclideanSpace 𝕜 (Fin (n + 1))),
      ‖A‖ ≤ 1 ∧ ‖B‖ ≤ 1 ∧
      B.comp (S.comp A) =
        (c : 𝕜) • ContinuousLinearMap.id 𝕜 (EuclideanSpace 𝕜 (Fin (n + 1))) := by
  sorry

end SVD
