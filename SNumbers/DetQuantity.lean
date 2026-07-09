/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
import SNumbers.Inequalities
import SNumbers.PiLpCoordinates

/-!
# The determinant quantities `Δₖ(S)`

For a bounded operator `S : X →L[𝕜] Y` between normed spaces over `𝕜 ∈ {ℝ, ℂ}`
and `k ∈ ℕ`, define

  `Δₖ(S) := sup { |det (B ∘ S ∘ A)| : A : ℓ₂ᵏ → X, B : Y → ℓ₂ᵏ, ‖A‖ ≤ 1, ‖B‖ ≤ 1 }`.

Here `B ∘ S ∘ A` is an endomorphism of the `k`-dimensional Hilbert space
`ℓ₂ᵏ = EuclideanSpace 𝕜 (Fin k)`, so its determinant is a scalar. For `k = 0`
the space is trivial and every determinant equals `1`, so `Δ₀(S) = 1`.

These quantities drive the proof of the bound
`max(cₙ(S), dₙ(S)) ≤ e·(n+1)·hₙ(S)` (see `SNumbers.GelfandKolmogorovVsHilbert`):
they are **closed under contractive compressions** (any contraction pair
composed with an admissible pair is again admissible) and they **do not decay
too fast** from `Δₖ` to `Δₖ₊₁` (the growth lemma, proved in the companion
file from the extension lemma below).

## Main definitions and results

* `SNumbers.detSet`, `SNumbers.detNumber` — the admissible set and `Δₖ(S)`.
* `SNumbers.detNumber_zero` — `Δ₀(S) = 1`.
* `SNumbers.norm_det_le_detNumber` — every admissible pair gives a lower
  bound for the supremum.
* `SNumbers.norm_det_le_pow_norm` — `|det T| ≤ ‖T‖ᵏ` for an endomorphism of
  `ℓ₂ᵏ` (via `∏ aᵢ(T) = |det T|`), whence `Δₖ(S) ≤ ‖S‖ᵏ < ∞`.
* `SNumbers.exists_det_extension` — the **extension lemma**: from an
  admissible pair `(A, B)` for `Δₖ`, a vector `u ∈ B_X`, a functional
  `ρ ∈ B_{Y'}`, and weights `λ² + μ² = 1`, build an admissible pair
  `(A', B')` for `Δₖ₊₁` with

    `|det (B'∘S∘A')| = λ^{2k} · μ² · |ρ(Su)| · |det (B∘S∘A)|`,

  provided the extended matrix is block-triangular: either `B(Su) = 0`
  (Gelfand case) or `ρ` kills the range of `S∘A` (Kolmogorov case).

## Mathematical remarks

The extension lemma is the paper's key computation: with
`A'(s ⊕ t) = λ·As + μ·t·u` and `B'y = (λ·By) ⊕ (μ·ρ(y))`, the matrix of
`B'∘S∘A'` in the standard basis is the old matrix scaled by `λ²`, bordered by
one row and one column of which (at least) one vanishes outside the corner
entry `μ²·ρ(Su)`; Laplace expansion along that line gives the determinant
identity. Contractivity of `A'` is the two-term Cauchy–Schwarz inequality
`λa + μb ≤ √(a² + b²)`, and of `B'` the identity
`‖B'y‖² = λ²‖By‖² + μ²|ρ(y)|²`.
-/

universe u

open ContinuousLinearMap

namespace SNumbers

variable {𝕜 : Type u} [RCLike 𝕜]
variable {X Y : Type u}
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]

/-! ### Definition -/

/-- The set of values `|det (B ∘ S ∘ A)|` over contraction pairs
`A : ℓ₂ᵏ → X`, `B : Y → ℓ₂ᵏ`; its supremum is `Δₖ(S)`. -/
def detSet (S : X →L[𝕜] Y) (k : ℕ) : Set ℝ :=
  {r | ∃ (A : EuclideanSpace 𝕜 (Fin k) →L[𝕜] X) (B : Y →L[𝕜] EuclideanSpace 𝕜 (Fin k)),
      ‖A‖ ≤ 1 ∧ ‖B‖ ≤ 1 ∧
      r = ‖LinearMap.det (B.comp (S.comp A) :
          EuclideanSpace 𝕜 (Fin k) →ₗ[𝕜] EuclideanSpace 𝕜 (Fin k))‖}

/-- The `k`-th **determinant quantity**
`Δₖ(S) = sup { |det (B∘S∘A)| : ‖A‖ ≤ 1, ‖B‖ ≤ 1 }` of a bounded operator.
For `k = 0` this equals `1` (`detNumber_zero`). -/
noncomputable def detNumber (S : X →L[𝕜] Y) (k : ℕ) : ℝ :=
  sSup (detSet S k)

/-! ### Elementary properties -/

/-- The admissible set is nonempty (take `A = 0`, `B = 0`). -/
lemma detSet_nonempty (S : X →L[𝕜] Y) (k : ℕ) : (detSet S k).Nonempty :=
  ⟨_, 0, 0, by simp, by simp, rfl⟩

omit [RCLike 𝕜] in
/-- The trivial space `ℓ₂⁰` has only one element. -/
private lemma subsingleton_euclidean_zero :
    Subsingleton (EuclideanSpace 𝕜 (Fin 0)) :=
  ⟨fun _ _ => PiLp.ext fun i => i.elim0⟩

/-- **`|det T| ≤ ‖T‖ᵏ`** for an endomorphism `T` of `ℓ₂ᵏ`. For `k ≥ 1` this is
the identity `∏ᵢ aᵢ(T) = |det T|` (`prod_approximationNumber_eq_norm_det`)
together with `aᵢ(T) ≤ ‖T‖`; for `k = 0` both sides are `1`. -/
lemma norm_det_le_pow_norm {k : ℕ}
    (T : EuclideanSpace 𝕜 (Fin k) →L[𝕜] EuclideanSpace 𝕜 (Fin k)) :
    ‖LinearMap.det (T : EuclideanSpace 𝕜 (Fin k) →ₗ[𝕜] EuclideanSpace 𝕜 (Fin k))‖
      ≤ ‖T‖ ^ k := by
  cases k with
  | zero =>
    haveI := subsingleton_euclidean_zero (𝕜 := 𝕜)
    rw [LinearMap.det_eq_one_of_subsingleton, norm_one, pow_zero]
  | succ m =>
    haveI : Nontrivial (EuclideanSpace 𝕜 (Fin (m + 1))) :=
      Module.nontrivial_of_finrank_pos (by rw [finrank_euclideanSpace_fin]; omega)
    have h := prod_approximationNumber_eq_norm_det T
    rw [finrank_euclideanSpace_fin] at h
    rw [← h]
    calc ∏ i ∈ Finset.range (m + 1), approximationNumber T i
        ≤ ∏ _i ∈ Finset.range (m + 1), ‖T‖ :=
          Finset.prod_le_prod (fun i _ => approximationNumber_nonneg T i)
            (fun i _ => approximationNumber_le_norm T i)
      _ = ‖T‖ ^ (m + 1) := by rw [Finset.prod_const, Finset.card_range]

/-- Each admissible value is at most `‖S‖ᵏ` (since `‖B∘S∘A‖ ≤ ‖S‖`). -/
private lemma detSet_le_pow_norm (S : X →L[𝕜] Y) (k : ℕ) :
    ∀ r ∈ detSet S k, r ≤ ‖S‖ ^ k := by
  rintro r ⟨A, B, hA, hB, rfl⟩
  refine (norm_det_le_pow_norm _).trans (pow_le_pow_left₀ (norm_nonneg _) ?_ k)
  calc ‖B.comp (S.comp A)‖
      ≤ ‖B‖ * ‖S‖ * ‖A‖ := norm_comp_comp_le A S B
    _ ≤ 1 * ‖S‖ * 1 := by gcongr
    _ = ‖S‖ := by ring

/-- The admissible set is bounded above by `‖S‖ᵏ`. -/
lemma detSet_bddAbove (S : X →L[𝕜] Y) (k : ℕ) : BddAbove (detSet S k) :=
  ⟨‖S‖ ^ k, detSet_le_pow_norm S k⟩

/-- Every admissible pair bounds `Δₖ(S)` from below. -/
lemma norm_det_le_detNumber (S : X →L[𝕜] Y) {k : ℕ}
    {A : EuclideanSpace 𝕜 (Fin k) →L[𝕜] X} {B : Y →L[𝕜] EuclideanSpace 𝕜 (Fin k)}
    (hA : ‖A‖ ≤ 1) (hB : ‖B‖ ≤ 1) :
    ‖LinearMap.det (B.comp (S.comp A) :
        EuclideanSpace 𝕜 (Fin k) →ₗ[𝕜] EuclideanSpace 𝕜 (Fin k))‖ ≤ detNumber S k :=
  le_csSup (detSet_bddAbove S k) ⟨A, B, hA, hB, rfl⟩

lemma detNumber_nonneg (S : X →L[𝕜] Y) (k : ℕ) : 0 ≤ detNumber S k :=
  Real.sSup_nonneg <| by rintro r ⟨A, B, _, _, rfl⟩; exact norm_nonneg _

/-- **`Δ₀(S) = 1`.** Every endomorphism of the trivial space `ℓ₂⁰` has
determinant `1`, so the admissible set is exactly `{1}`. -/
lemma detNumber_zero (S : X →L[𝕜] Y) : detNumber S 0 = 1 := by
  haveI := subsingleton_euclidean_zero (𝕜 := 𝕜)
  have hset : detSet S 0 = {(1 : ℝ)} := by
    ext r
    constructor
    · rintro ⟨A, B, _, _, rfl⟩
      rw [Set.mem_singleton_iff, LinearMap.det_eq_one_of_subsingleton, norm_one]
    · rintro hr
      rw [Set.mem_singleton_iff] at hr
      subst hr
      exact ⟨0, 0, by simp, by simp,
        by rw [LinearMap.det_eq_one_of_subsingleton, norm_one]⟩
  rw [detNumber, hset, csSup_singleton]

/-- `Δₖ(S) ≤ ‖S‖ᵏ`. -/
lemma detNumber_le_pow_norm (S : X →L[𝕜] Y) (k : ℕ) : detNumber S k ≤ ‖S‖ ^ k :=
  csSup_le (detSet_nonempty S k) (detSet_le_pow_norm S k)

/-! ### The extension lemma

Given an admissible pair `(A, B)` for `Δₖ`, a unit vector `u` and a unit
functional `ρ`, and weights `λ, μ ≥ 0` with `λ² + μ² = 1`, we extend to an
admissible pair `(A', B')` for `Δₖ₊₁`:

* `A' : ℓ₂ᵏ⁺¹ → X` acts as `λ·A` on the first `k` coordinates and sends the
  last basis vector to `μ·u`;
* `B' : Y → ℓ₂ᵏ⁺¹` is `λ·B` in the first `k` coordinates and `μ·ρ(y)` in the
  last.

If either `B(Su) = 0` (the extended matrix's last **column** vanishes above
the corner) or `ρ ∘ S ∘ A = 0` (its last **row** vanishes before the corner),
Laplace expansion along that line gives

  `|det(B'∘S∘A')| = λ^{2k} · μ² · |ρ(Su)| · |det(B∘S∘A)|`. -/

section Extension

variable {k : ℕ}

/-- Two-term Cauchy–Schwarz: for `λ² + μ² = 1` and `a, b ≥ 0`,
`λ·a + μ·b ≤ √(a² + b²)`. -/
private lemma lam_mul_add_mu_mul_le {lam mu a b c : ℝ}
    (hlam : 0 ≤ lam) (hmu : 0 ≤ mu) (hlm : lam ^ 2 + mu ^ 2 = 1)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hsq : a ^ 2 + b ^ 2 = c ^ 2) :
    lam * a + mu * b ≤ c := by
  have h1 : (lam * a + mu * b) ^ 2 ≤ c ^ 2 := by nlinarith [sq_nonneg (lam * b - mu * a)]
  have h2 : 0 ≤ lam * a + mu * b := by positivity
  calc lam * a + mu * b = Real.sqrt ((lam * a + mu * b) ^ 2) := (Real.sqrt_sq h2).symm
    _ ≤ Real.sqrt (c ^ 2) := Real.sqrt_le_sqrt h1
    _ = c := Real.sqrt_sq hc

/-- **Extension lemma.** From an admissible pair `(A, B)` for `Δₖ(S)`, a
vector `u ∈ B_X`, a functional `ρ ∈ B_{Y'}`, and weights `λ² + μ² = 1`,
build an admissible pair `(A', B')` for `Δₖ₊₁(S)` whose determinant picks up
exactly the factor `λ^{2k}·μ²·|ρ(Su)|`, provided the bordered matrix is
block-triangular: either `B(Su) = 0` or `ρ(S(A eⱼ)) = 0` for all `j`. -/
lemma exists_det_extension (S : X →L[𝕜] Y)
    {A : EuclideanSpace 𝕜 (Fin k) →L[𝕜] X} {B : Y →L[𝕜] EuclideanSpace 𝕜 (Fin k)}
    (hA : ‖A‖ ≤ 1) (hB : ‖B‖ ≤ 1)
    {u : X} (hu : ‖u‖ ≤ 1) {ρ : Y →L[𝕜] 𝕜} (hρ : ‖ρ‖ ≤ 1)
    {lam mu : ℝ} (hlam : 0 ≤ lam) (hmu : 0 ≤ mu) (hlm : lam ^ 2 + mu ^ 2 = 1)
    (htri : (∀ i, B (S u) i = 0) ∨
      (∀ j, ρ (S (A (EuclideanSpace.single j (1 : 𝕜)))) = 0)) :
    ∃ (A' : EuclideanSpace 𝕜 (Fin (k + 1)) →L[𝕜] X)
      (B' : Y →L[𝕜] EuclideanSpace 𝕜 (Fin (k + 1))),
      ‖A'‖ ≤ 1 ∧ ‖B'‖ ≤ 1 ∧
      ‖LinearMap.det (B'.comp (S.comp A') :
          EuclideanSpace 𝕜 (Fin (k + 1)) →ₗ[𝕜] EuclideanSpace 𝕜 (Fin (k + 1)))‖
        = lam ^ (2 * k) * mu ^ 2 * ‖ρ (S u)‖ *
          ‖LinearMap.det (B.comp (S.comp A) :
              EuclideanSpace 𝕜 (Fin k) →ₗ[𝕜] EuclideanSpace 𝕜 (Fin k))‖ := by
  classical
  have hle : k ≤ k + 1 := Nat.le_succ k
  -- The last standard basis vector of `ℓ₂ᵏ⁺¹`.
  set eL : EuclideanSpace 𝕜 (Fin (k + 1)) :=
    EuclideanSpace.single (Fin.last k) (1 : 𝕜) with heL
  -- The extended factors.
  set A' : EuclideanSpace 𝕜 (Fin (k + 1)) →L[𝕜] X :=
    (lam : 𝕜) • (A.comp (projFin (p := 2) hle)) +
      (mu : 𝕜) • ((innerSL 𝕜 eL).smulRight u) with hA'def
  set B' : Y →L[𝕜] EuclideanSpace 𝕜 (Fin (k + 1)) :=
    (lam : 𝕜) • ((padFin (p := 2)).comp B) + (mu : 𝕜) • (ρ.smulRight eL) with hB'def
  -- `castLE` along `k ≤ k+1` is `castSucc` (both only touch the value).
  have hcast : ∀ i : Fin k, Fin.castLE hle i = Fin.castSucc i := fun i => rfl
  -- Application formula for `A'`.
  have hA'app : ∀ w, A' w = (lam : 𝕜) • A (projFin (p := 2) hle w) +
      ((mu : 𝕜) * w (Fin.last k)) • u := by
    intro w
    rw [hA'def, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, heL,
      EuclideanSpace.inner_single_left, map_one, one_mul, smul_smul]
  -- Coordinate formulas for `B'`.
  have hB'cs : ∀ (y : Y) (i : Fin k),
      (B' y) (Fin.castSucc i) = (lam : 𝕜) * (B y) i := by
    intro y i
    rw [hB'def, ContinuousLinearMap.add_apply, PiLp.add_apply,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply,
      PiLp.smul_apply, PiLp.smul_apply, PiLp.smul_apply, ← hcast i, padFin_castLE, heL,
      PiLp.single_apply,
      if_neg ((Fin.castSucc_lt_last i).ne ∘ (hcast i ▸ ·)), smul_zero, smul_zero, add_zero,
      smul_eq_mul]
  have hB'last : ∀ y : Y, (B' y) (Fin.last k) = (mu : 𝕜) * ρ y := by
    intro y
    rw [hB'def, ContinuousLinearMap.add_apply, PiLp.add_apply,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply,
      PiLp.smul_apply, PiLp.smul_apply, PiLp.smul_apply, padFin_apply,
      dif_neg (by simp), smul_zero, zero_add, heL, PiLp.single_apply,
      if_pos rfl, smul_eq_mul, smul_eq_mul, mul_one]
  -- Values of `A'` on the standard basis.
  have hproj_single : ∀ j : Fin k,
      projFin (p := 2) hle (EuclideanSpace.single (Fin.castSucc j) (1 : 𝕜))
        = EuclideanSpace.single j (1 : 𝕜) := by
    intro j
    ext i
    rw [projFin_apply, PiLp.single_apply, PiLp.single_apply, hcast i]
    exact if_congr Fin.castSucc_inj.symm.symm rfl rfl
  have hproj_last :
      projFin (p := 2) hle (EuclideanSpace.single (Fin.last k) (1 : 𝕜)) = 0 := by
    ext i
    rw [projFin_apply, PiLp.single_apply, hcast i, PiLp.zero_apply,
      if_neg (Fin.castSucc_lt_last i).ne]
  have hA'cs : ∀ j : Fin k,
      A' (EuclideanSpace.single (Fin.castSucc j) (1 : 𝕜))
        = (lam : 𝕜) • A (EuclideanSpace.single j (1 : 𝕜)) := by
    intro j
    rw [hA'app, hproj_single j, PiLp.single_apply,
      if_neg (Fin.castSucc_lt_last j).ne', mul_zero, zero_smul, add_zero]
  have hA'last : A' (EuclideanSpace.single (Fin.last k) (1 : 𝕜)) = (mu : 𝕜) • u := by
    rw [hA'app, hproj_last, map_zero, smul_zero, zero_add,
      PiLp.single_apply, if_pos rfl, mul_one]
  -- Norms of coordinates split as `‖w‖² = ‖proj w‖² + ‖w last‖²`.
  have hsplit : ∀ w : EuclideanSpace 𝕜 (Fin (k + 1)),
      ‖projFin (p := 2) hle w‖ ^ 2 + ‖w (Fin.last k)‖ ^ 2 = ‖w‖ ^ 2 := by
    intro w
    have h1 : ‖w‖ ^ 2 = ∑ i : Fin (k + 1), ‖w i‖ ^ 2 := by
      rw [EuclideanSpace.norm_eq,
        Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
    have h2 : ‖projFin (p := 2) hle w‖ ^ 2 = ∑ i : Fin k, ‖w (Fin.castSucc i)‖ ^ 2 := by
      rw [EuclideanSpace.norm_eq,
        Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
      exact Finset.sum_congr rfl fun i _ => by rw [projFin_apply, hcast i]
    rw [h1, h2, Fin.sum_univ_castSucc]
  -- `A'` is a contraction.
  have hA'norm : ‖A'‖ ≤ 1 := by
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun w => ?_
    rw [one_mul, hA'app]
    have h1 : ‖(lam : 𝕜) • A (projFin (p := 2) hle w)‖
        ≤ lam * ‖projFin (p := 2) hle w‖ := by
      rw [norm_smul, RCLike.norm_ofReal, abs_of_nonneg hlam]
      have := (A.le_opNorm (projFin (p := 2) hle w)).trans
        (mul_le_of_le_one_left (norm_nonneg _) hA)
      exact mul_le_mul_of_nonneg_left this hlam
    have h2 : ‖((mu : 𝕜) * w (Fin.last k)) • u‖ ≤ mu * ‖w (Fin.last k)‖ := by
      rw [norm_smul, norm_mul, RCLike.norm_ofReal, abs_of_nonneg hmu, mul_assoc]
      exact mul_le_mul_of_nonneg_left
        (mul_le_of_le_one_right (norm_nonneg _) hu) hmu
    refine (norm_add_le _ _).trans ((add_le_add h1 h2).trans ?_)
    exact lam_mul_add_mu_mul_le hlam hmu hlm (norm_nonneg _) (norm_nonneg _)
      (norm_nonneg w) (hsplit w)
  -- `B'` is a contraction: `‖B'y‖² = λ²‖By‖² + μ²|ρy|² ≤ ‖y‖²`.
  have hB'norm : ‖B'‖ ≤ 1 := by
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun y => ?_
    rw [one_mul]
    have hsq : ‖B' y‖ ^ 2 = lam ^ 2 * ‖B y‖ ^ 2 + mu ^ 2 * ‖ρ y‖ ^ 2 := by
      have h1 : ‖B' y‖ ^ 2 = ∑ i : Fin (k + 1), ‖(B' y) i‖ ^ 2 := by
        rw [EuclideanSpace.norm_eq,
          Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
      have h2 : ‖B y‖ ^ 2 = ∑ i : Fin k, ‖(B y) i‖ ^ 2 := by
        rw [EuclideanSpace.norm_eq,
          Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
      rw [h1, Fin.sum_univ_castSucc, hB'last y]
      have h3 : ∀ i : Fin k, ‖(B' y) (Fin.castSucc i)‖ ^ 2 = lam ^ 2 * ‖(B y) i‖ ^ 2 := by
        intro i
        rw [hB'cs y i, norm_mul, RCLike.norm_ofReal, abs_of_nonneg hlam, mul_pow]
      rw [Finset.sum_congr rfl fun i _ => h3 i, ← Finset.mul_sum, ← h2, norm_mul,
        RCLike.norm_ofReal, abs_of_nonneg hmu, mul_pow]
    have hBy : ‖B y‖ ≤ ‖y‖ :=
      (B.le_opNorm y).trans (mul_le_of_le_one_left (norm_nonneg _) hB)
    have hρy : ‖ρ y‖ ≤ ‖y‖ :=
      (ρ.le_opNorm y).trans (mul_le_of_le_one_left (norm_nonneg _) hρ)
    have hsq2 : ‖B' y‖ ^ 2 ≤ ‖y‖ ^ 2 := by
      rw [hsq]
      have e1 : lam ^ 2 * ‖B y‖ ^ 2 ≤ lam ^ 2 * ‖y‖ ^ 2 := by
        have := mul_self_le_mul_self (norm_nonneg (B y)) hBy
        nlinarith [sq_nonneg lam]
      have e2 : mu ^ 2 * ‖ρ y‖ ^ 2 ≤ mu ^ 2 * ‖y‖ ^ 2 := by
        have := mul_self_le_mul_self (norm_nonneg (ρ y)) hρy
        nlinarith [sq_nonneg mu]
      nlinarith [e1, e2]
    calc ‖B' y‖ = Real.sqrt (‖B' y‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
      _ ≤ Real.sqrt (‖y‖ ^ 2) := Real.sqrt_le_sqrt hsq2
      _ = ‖y‖ := Real.sqrt_sq (norm_nonneg _)
  -- The matrices of the two compositions in the standard bases.
  set bk := EuclideanSpace.basisFun (Fin k) 𝕜 with hbk
  set bk1 := EuclideanSpace.basisFun (Fin (k + 1)) 𝕜 with hbk1
  set Nmat := LinearMap.toMatrix bk.toBasis bk.toBasis
    (B.comp (S.comp A) : EuclideanSpace 𝕜 (Fin k) →ₗ[𝕜] EuclideanSpace 𝕜 (Fin k))
    with hNmat
  set Mmat := LinearMap.toMatrix bk1.toBasis bk1.toBasis
    (B'.comp (S.comp A') :
      EuclideanSpace 𝕜 (Fin (k + 1)) →ₗ[𝕜] EuclideanSpace 𝕜 (Fin (k + 1)))
    with hMmat
  have hMapp : ∀ i j, Mmat i j
      = (B' (S (A' (EuclideanSpace.single j (1 : 𝕜))))) i := by
    intro i j
    rw [hMmat, LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,
      OrthonormalBasis.coe_toBasis, hbk1, EuclideanSpace.basisFun_repr,
      EuclideanSpace.basisFun_apply, ContinuousLinearMap.coe_coe,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]
  have hNapp : ∀ i j, Nmat i j
      = (B (S (A (EuclideanSpace.single j (1 : 𝕜))))) i := by
    intro i j
    rw [hNmat, LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,
      OrthonormalBasis.coe_toBasis, hbk, EuclideanSpace.basisFun_repr,
      EuclideanSpace.basisFun_apply, ContinuousLinearMap.coe_coe,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]
  -- The four kinds of entries of the bordered matrix.
  have hMcc : ∀ i j : Fin k, Mmat (Fin.castSucc i) (Fin.castSucc j)
      = (lam : 𝕜) ^ 2 * Nmat i j := by
    intro i j
    rw [hMapp, hA'cs j, map_smul, map_smul, PiLp.smul_apply, hB'cs, hNapp,
      smul_eq_mul]
    ring
  have hMlc : ∀ j : Fin k, Mmat (Fin.last k) (Fin.castSucc j)
      = (lam : 𝕜) * (mu : 𝕜) * ρ (S (A (EuclideanSpace.single j (1 : 𝕜)))) := by
    intro j
    rw [hMapp, hA'cs j, map_smul, map_smul, PiLp.smul_apply, hB'last, smul_eq_mul]
    ring
  have hMcl : ∀ i : Fin k, Mmat (Fin.castSucc i) (Fin.last k)
      = (lam : 𝕜) * (mu : 𝕜) * (B (S u)) i := by
    intro i
    rw [hMapp, hA'last, map_smul, map_smul, PiLp.smul_apply, hB'cs, smul_eq_mul]
    ring
  have hMll : Mmat (Fin.last k) (Fin.last k) = (mu : 𝕜) ^ 2 * ρ (S u) := by
    rw [hMapp, hA'last, map_smul, map_smul, PiLp.smul_apply, hB'last, smul_eq_mul]
    ring
  -- The minor at the corner is `λ²` times the old matrix.
  have hsub : Mmat.submatrix Fin.castSucc Fin.castSucc = ((lam : 𝕜) ^ 2) • Nmat := by
    ext i j
    rw [Matrix.submatrix_apply, hMcc i j, Matrix.smul_apply, smul_eq_mul]
  have hminor :
      (Mmat.submatrix (Fin.last k).succAbove (Fin.last k).succAbove).det
        = (lam : 𝕜) ^ (2 * k) * Nmat.det := by
    rw [Fin.succAbove_last, hsub, Matrix.det_smul, Fintype.card_fin, pow_mul]
  -- Laplace expansion along the last column (Gelfand case) or row (Kolmogorov).
  have hdetM : Mmat.det
      = (lam : 𝕜) ^ (2 * k) * (mu : 𝕜) ^ 2 * ρ (S u) * Nmat.det := by
    have hsign : ((-1 : 𝕜)) ^ ((Fin.last k : ℕ) + (Fin.last k : ℕ)) = 1 := by
      rw [Fin.val_last]
      exact Even.neg_one_pow ⟨k, rfl⟩
    rcases htri with hcol | hrow
    · -- Last column vanishes above the corner: expand along column `last`.
      rw [Matrix.det_succ_column Mmat (Fin.last k),
        Finset.sum_eq_single (Fin.last k)
          (fun i _ hi => by
            obtain ⟨i', rfl⟩ := Fin.eq_castSucc_of_ne_last hi
            rw [hMcl i', hcol i', mul_zero, mul_zero, zero_mul])
          (fun h => absurd (Finset.mem_univ _) h),
        hsign, hMll, hminor, one_mul]
      ring
    · -- Last row vanishes before the corner: expand along row `last`.
      rw [Matrix.det_succ_row Mmat (Fin.last k),
        Finset.sum_eq_single (Fin.last k)
          (fun j _ hj => by
            obtain ⟨j', rfl⟩ := Fin.eq_castSucc_of_ne_last hj
            rw [hMlc j', hrow j', mul_zero, mul_zero, zero_mul])
          (fun h => absurd (Finset.mem_univ _) h),
        hsign, hMll, hminor, one_mul]
      ring
  -- Assemble.
  refine ⟨A', B', hA'norm, hB'norm, ?_⟩
  rw [← LinearMap.det_toMatrix bk1.toBasis
      (B'.comp (S.comp A') :
        EuclideanSpace 𝕜 (Fin (k + 1)) →ₗ[𝕜] EuclideanSpace 𝕜 (Fin (k + 1))),
    ← LinearMap.det_toMatrix bk.toBasis
      (B.comp (S.comp A) : EuclideanSpace 𝕜 (Fin k) →ₗ[𝕜] EuclideanSpace 𝕜 (Fin k)),
    ← hMmat, ← hNmat, hdetM, norm_mul, norm_mul, norm_mul, norm_pow, norm_pow,
    RCLike.norm_ofReal, RCLike.norm_ofReal, abs_of_nonneg hlam, abs_of_nonneg hmu]

end Extension

end SNumbers
