/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
import SNumbers.MaxDifference

/-!
# A bound between all s-numbers: `aₙ ≤ e·(n+1)·hₙ`

For every bounded operator `S : X →L[𝕜] Y` between normed spaces over
`𝕜 ∈ {ℝ, ℂ}` and every `n`, the **approximation numbers** are bounded by the
**Hilbert numbers**:

  `aₙ(S) ≤ e·(n+1)·hₙ(S)`.

Since `aₙ` is the largest and `hₙ` the smallest s-number sequence, this bounds
*any* s-number sequence by *any* other, `sₙ(S) ≤ e·(n+1)·tₙ(S)`
(`sn_le_e_mul_tn`), and it proves the conjecture of Carl and Pietsch up to the
constant `e`. The factor `n+1` is optimal, e.g. for the identity
`ℓ₁ → ℓ∞`.

This strengthens `max (cₙ, dₙ) ≤ e·(n+1)·hₙ`
(`max_gelfandNumber_kolmogorovNumber_le_e_mul_hilbertNumber` in
`SNumbers.MaxDifference`), since `cₙ, dₙ ≤ aₙ`.

## The argument

Everything runs through the determinant quantities

  `Δₖ(S) = sup { |det (B ∘ S ∘ A)| : A : ℓ₂ᵏ → X, B : Y → ℓ₂ᵏ, ‖A‖ ≤ 1, ‖B‖ ≤ 1 }`

(`detNumber`, from `SNumbers.MaxDifference`), which are squeezed between the
two quantities of interest:

* **Upper bound** `Δₙ₊₁(S) ≤ hₙ(S)·Δₙ(S)`, already proved as
  `detNumber_succ_le_hilbertNumber_mul`;
* **Lower bound** `Δₙ₊₁(S) ≥ (nⁿ/(n+1)ⁿ⁺¹)·aₙ(S)·Δₙ(S)`, proved here as
  `approximationNumber_mul_detNumber_le_detNumber_succ`.

Dividing by `Δₙ(S) > 0` gives `aₙ(S) ≤ ((n+1)ⁿ⁺¹/nⁿ)·hₙ(S) ≤ e·(n+1)·hₙ(S)`.

The lower bound is the new ingredient. Given contractions `A : ℓ₂ⁿ → X` and
`B : Y → ℓ₂ⁿ` with `det (BSA) ≠ 0`, the operator

  `L := S∘A∘(B∘S∘A)⁻¹∘B∘S`

has rank at most `n`, so `‖S - L‖ ≥ aₙ(S)` by the very definition of the
approximation numbers. Bordering `(A, B)` by a vector `x ∈ B_X` and a
functional `b ∈ B_{Y'}`, weighted by `λ² + μ² = 1`,

  `A₀(ξ ⊕ τ) = λ·Aξ + μ·τ·x`,   `B₀ y = (λ·By) ⊕ (μ·b y)`,

produces an admissible pair for `Δₙ₊₁(S)` whose determinant is

  `det (B₀SA₀) = λ^{2n}·μ²·b((S - L)x)·det (BSA)`.                       (∗)

Choosing `x` and `b` so that `b((S - L)x)` almost equals `‖S - L‖ ≥ aₙ(S)`
(the operator norm characterisation plus Hahn–Banach) and optimising
`λ² = n/(n+1)`, `μ² = 1/(n+1)` yields the lower bound.

Identity (∗) is a *column operation*, not a Schur complement: writing
`ζ := (BSA)⁻¹B(Sx)`, the last column of the matrix of `B₀SA₀` equals
`μ/λ` times the combination of its first `n` columns with coefficients `ζ`,
*above the corner*. Subtracting that combination therefore leaves a matrix
whose last column is zero except at the corner, where it equals
`μ²·(b(Sx) - b(S(Aζ))) = μ²·b((S - L)x)`; Laplace expansion along that column
finishes. This is `det_eq_corner_mul_det_submatrix` below, a statement about
matrices that needs no invertibility hypothesis.

## Remaining work

The sharper bound `aₙ(S) ≤ √(e·(n+1))·hₙ(S)` valid when `X` or `Y` is a
Hilbert space is **not** formalised here.

## References

* M. Ullrich, *On bounds between all s-numbers and widths of convex sets*
  (preprint, 2026), Theorem 1 (general case).
-/

universe u

open ContinuousLinearMap
open scoped Pointwise

namespace SNumbers

variable {𝕜 : Type u} [RCLike 𝕜]
variable {X Y : Type u}
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]

/-! ### Elementary helpers

These four are copies of the corresponding private lemmas in
`SNumbers.MaxDifference`; they are repeated because `private` declarations are
not visible across files. -/

/-- `0 < nⁿ` in `ℝ` (with the convention `0⁰ = 1`). -/
private lemma pow_self_pos' (n : ℕ) : (0 : ℝ) < (n : ℝ) ^ n := by
  cases n with
  | zero => norm_num
  | succ m => exact pow_pos (by exact_mod_cast Nat.succ_pos m) _

/-- The per-step growth factor `kᵏ/(k+1)^{k+1}` is positive. -/
private lemma growth_ratio_pos' (k : ℕ) :
    (0 : ℝ) < (k : ℝ) ^ k / ((k : ℝ) + 1) ^ (k + 1) :=
  div_pos (pow_self_pos' k) (pow_pos (by positivity) _)

/-- Two-term Cauchy–Schwarz: for `λ² + μ² = 1` and `a, b ≥ 0`,
`λ·a + μ·b ≤ √(a² + b²)`. -/
private lemma lam_mul_add_mu_mul_le' {lam mu a b c : ℝ}
    (hlam : 0 ≤ lam) (hmu : 0 ≤ mu) (hlm : lam ^ 2 + mu ^ 2 = 1)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hsq : a ^ 2 + b ^ 2 = c ^ 2) :
    lam * a + mu * b ≤ c := by
  have h1 : (lam * a + mu * b) ^ 2 ≤ c ^ 2 := by nlinarith [sq_nonneg (lam * b - mu * a)]
  have h2 : 0 ≤ lam * a + mu * b := by positivity
  calc lam * a + mu * b = Real.sqrt ((lam * a + mu * b) ^ 2) := (Real.sqrt_sq h2).symm
    _ ≤ Real.sqrt (c ^ 2) := Real.sqrt_le_sqrt h1
    _ = c := Real.sqrt_sq hc

/-- `(n+1)^{n+1}/nⁿ = (n+1)·(1+1/n)ⁿ ≤ e·(n+1)`, from `1 + x ≤ eˣ` at
`x = 1/n` raised to the `n`-th power. -/
private lemma ratio_le_exp_mul' (n : ℕ) :
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
    rw [div_le_iff₀ (pow_self_pos' n)]
    calc ((n : ℝ) + 1) ^ (n + 1) = ((n : ℝ) + 1) ^ n * ((n : ℝ) + 1) := pow_succ _ _
      _ ≤ Real.exp 1 * (n : ℝ) ^ n * ((n : ℝ) + 1) :=
          mul_le_mul_of_nonneg_right h3 (by positivity)
      _ = Real.exp 1 * ((n : ℝ) + 1) * (n : ℝ) ^ n := by ring

/-! ### The bordered determinant identity

If the last column of a `(k+1)×(k+1)` matrix `M` is, *above the corner*, the
combination of the first `k` columns with coefficients `w`, then subtracting
that combination clears the column and Laplace expansion gives `det M` as the
resulting corner entry times the determinant of the top-left `k×k` block. -/

/-- **Bordered determinant.** Let `M` be a `(k+1)×(k+1)` matrix and `w` a
vector of `k` scalars such that the entries of the last column of `M` above the
corner are given by the combination of the first `k` columns with coefficients
`w`, i.e. `M i last = ∑ⱼ M i j · wⱼ` for `i < k`. Then

  `det M = (M last last - ∑ⱼ M last j · wⱼ) · det (M restricted to the first k
  rows and columns)`.

No invertibility of the top-left block is required; this is the elementary
column-operation form of the Schur determinant formula. -/
lemma det_eq_corner_mul_det_submatrix {k : ℕ}
    (M : Matrix (Fin (k + 1)) (Fin (k + 1)) 𝕜) (w : Fin k → 𝕜)
    (hw : ∀ i : Fin k, M i.castSucc (Fin.last k)
      = ∑ j, M i.castSucc j.castSucc * w j) :
    M.det = (M (Fin.last k) (Fin.last k) - ∑ j, M (Fin.last k) j.castSucc * w j)
      * (M.submatrix Fin.castSucc Fin.castSucc).det := by
  classical
  -- The coefficients of the column operation: keep the last column, subtract
  -- `wⱼ` times the `j`-th one.
  set c : Fin (k + 1) → 𝕜 := Fin.lastCases 1 (fun j => -w j) with hc
  have hclast : c (Fin.last k) = 1 := by rw [hc]; simp
  have hccast : ∀ j : Fin k, c j.castSucc = -w j := fun j => by rw [hc]; simp
  -- The column obtained from the operation.
  have hcol : ∀ r : Fin (k + 1), (∑ i, c i • M r i)
      = M r (Fin.last k) - ∑ j, M r j.castSucc * w j := by
    intro r
    rw [Fin.sum_univ_castSucc, hclast, one_smul]
    have hterm : ∀ j : Fin k,
        c j.castSucc • M r j.castSucc = -(M r j.castSucc * w j) := by
      intro j
      rw [hccast j, neg_smul, smul_eq_mul]
      ring
    rw [Finset.sum_congr rfl fun j _ => hterm j, Finset.sum_neg_distrib]
    ring
  -- The matrix after the column operation; its determinant is unchanged.
  set M' := M.updateCol (Fin.last k) (fun r => ∑ i, c i • M r i) with hM'
  have hMM' : M'.det = M.det := by
    rw [hM', Matrix.det_updateCol_sum, hclast, one_smul]
  have hlastcol : ∀ r, M' r (Fin.last k)
      = M r (Fin.last k) - ∑ j, M r j.castSucc * w j := fun r => by
    rw [hM', Matrix.updateCol_self, hcol r]
  -- The last column of `M'` vanishes above the corner.
  have hzero : ∀ i : Fin k, M' i.castSucc (Fin.last k) = 0 := fun i => by
    rw [hlastcol, hw i, sub_self]
  -- The top-left block is unchanged.
  have hsub : M'.submatrix Fin.castSucc Fin.castSucc
      = M.submatrix Fin.castSucc Fin.castSucc := by
    ext i j
    rw [Matrix.submatrix_apply, Matrix.submatrix_apply, hM',
      Matrix.updateCol_ne (Fin.castSucc_lt_last j).ne]
  -- Laplace expansion along the last column of `M'`.
  have hsign : ((-1 : 𝕜)) ^ ((Fin.last k : ℕ) + (Fin.last k : ℕ)) = 1 := by
    rw [Fin.val_last]
    exact Even.neg_one_pow ⟨k, rfl⟩
  rw [← hMM', Matrix.det_succ_column M' (Fin.last k),
    Finset.sum_eq_single (Fin.last k)
      (fun i _ hi => by
        obtain ⟨i', rfl⟩ := Fin.eq_castSucc_of_ne_last hi
        rw [hzero i', mul_zero, zero_mul])
      (fun h => absurd (Finset.mem_univ _) h),
    hsign, one_mul, Fin.succAbove_last, hsub, hlastcol]

/-! ### Basis expansions in `ℓ₂ᵏ`

Two routine consequences of linearity: an operator on `ℓ₂ᵏ` is determined by
its values on the standard basis, in the form needed to recognise a column of a
matrix as a combination of the others. -/

/-- Expanding `F z` over the standard basis of `ℓ₂ᵏ`. -/
private lemma clm_apply_eq_sum {k : ℕ} {Z : Type u} [NormedAddCommGroup Z]
    [NormedSpace 𝕜 Z] (F : EuclideanSpace 𝕜 (Fin k) →L[𝕜] Z)
    (z : EuclideanSpace 𝕜 (Fin k)) :
    F z = ∑ j, z j • F (EuclideanSpace.single j (1 : 𝕜)) := by
  classical
  have hz : ∑ j, z j • EuclideanSpace.single j (1 : 𝕜) = z := by
    simpa using (EuclideanSpace.basisFun (Fin k) 𝕜).sum_repr z
  calc F z = F (∑ j, z j • EuclideanSpace.single j (1 : 𝕜)) := by rw [hz]
    _ = ∑ j, z j • F (EuclideanSpace.single j (1 : 𝕜)) := by
        rw [map_sum]
        exact Finset.sum_congr rfl fun j _ => map_smul F _ _

/-- The `i`-th coordinate of `F z` expanded over the standard basis of `ℓ₂ᵏ`:
the matrix of `F` acts on the coordinates of `z`. -/
private lemma coord_apply_eq_sum {k m : ℕ}
    (F : EuclideanSpace 𝕜 (Fin k) →L[𝕜] EuclideanSpace 𝕜 (Fin m))
    (z : EuclideanSpace 𝕜 (Fin k)) (i : Fin m) :
    F z i = ∑ j, z j * (F (EuclideanSpace.single j (1 : 𝕜))) i := by
  have h := clm_apply_eq_sum ((innerSL 𝕜 (EuclideanSpace.single i (1 : 𝕜))).comp F) z
  simp only [ContinuousLinearMap.comp_apply, innerSL_apply_apply,
    EuclideanSpace.inner_single_left, map_one, one_mul, smul_eq_mul] at h
  exact h

/-! ### Rank of an operator factoring through `ℓ₂ᵏ` -/

/-- An operator that factors through the `k`-dimensional space `ℓ₂ᵏ` has rank
at most `k`. This is what makes the approximant `L = SA(BSA)⁻¹BS` below
admissible for `aₖ`. -/
lemma rank_comp_le_of_euclidean {k : ℕ} (F : EuclideanSpace 𝕜 (Fin k) →L[𝕜] Y)
    (G : X →L[𝕜] EuclideanSpace 𝕜 (Fin k)) :
    (F.comp G).rank ≤ (k : Cardinal) := by
  have hdom : Module.rank 𝕜 (EuclideanSpace 𝕜 (Fin k)) = (k : Cardinal) := by
    rw [← Module.finrank_eq_rank, finrank_euclideanSpace_fin]
  calc (F.comp G).rank
      ≤ F.rank := LinearMap.rank_comp_le_left _ _
    _ ≤ Module.rank 𝕜 (EuclideanSpace 𝕜 (Fin k)) := LinearMap.rank_le_domain _
    _ = (k : Cardinal) := hdom

/-! ### The bordered pair

An admissible pair `(A, B)` for `Δₖ` is enlarged to an admissible pair for
`Δₖ₊₁` using a vector `x ∈ B_X` and a functional `b ∈ B_{Y'}`, weighted so that
`λ² + μ² = 1`:

  `A₀(ξ ⊕ τ) = λ·Aξ + μ·τ·x`,   `B₀ y = (λ·By) ⊕ (μ·b y)`.

Contractivity of `A₀` is the two-term Cauchy–Schwarz inequality
`λa + μb ≤ √(a² + b²)`; contractivity of `B₀` is the identity
`‖B₀y‖² = λ²‖By‖² + μ²|b y|²`. -/

section Border

variable {k : ℕ}

/-- The bordered map `A₀(ξ ⊕ τ) = λ·Aξ + μ·τ·x` on `ℓ₂ᵏ⁺¹`, where `ξ` are the
first `k` coordinates and `τ` the last. -/
private noncomputable def borderDom (A : EuclideanSpace 𝕜 (Fin k) →L[𝕜] X) (x : X)
    (lam mu : ℝ) : EuclideanSpace 𝕜 (Fin (k + 1)) →L[𝕜] X :=
  (lam : 𝕜) • (A.comp (projFin (p := 2) (Nat.le_succ k))) +
    (mu : 𝕜) • ((innerSL 𝕜 (EuclideanSpace.single (Fin.last k) (1 : 𝕜))).smulRight x)

/-- The bordered map `B₀ y = (λ·By) ⊕ (μ·b y)` into `ℓ₂ᵏ⁺¹`. -/
private noncomputable def borderCod (B : Y →L[𝕜] EuclideanSpace 𝕜 (Fin k))
    (b : Y →L[𝕜] 𝕜) (lam mu : ℝ) : Y →L[𝕜] EuclideanSpace 𝕜 (Fin (k + 1)) :=
  (lam : 𝕜) • ((padFin (p := 2)).comp B) +
    (mu : 𝕜) • (b.smulRight (EuclideanSpace.single (Fin.last k) (1 : 𝕜)))

/-- `castLE` along `k ≤ k+1` is `castSucc` (both only touch the value). -/
private lemma castLE_succ_eq_castSucc (i : Fin k) :
    Fin.castLE (Nat.le_succ k) i = Fin.castSucc i := rfl

variable (A : EuclideanSpace 𝕜 (Fin k) →L[𝕜] X) (x : X)
  (B : Y →L[𝕜] EuclideanSpace 𝕜 (Fin k)) (b : Y →L[𝕜] 𝕜) (lam mu : ℝ)

private lemma borderDom_apply (v : EuclideanSpace 𝕜 (Fin (k + 1))) :
    borderDom A x lam mu v = (lam : 𝕜) • A (projFin (p := 2) (Nat.le_succ k) v) +
      ((mu : 𝕜) * v (Fin.last k)) • x := by
  rw [borderDom, add_apply, smul_apply, smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.smulRight_apply, innerSL_apply_apply,
    EuclideanSpace.inner_single_left, map_one, one_mul, smul_smul]

private lemma borderDom_single_castSucc (j : Fin k) :
    borderDom A x lam mu (EuclideanSpace.single (Fin.castSucc j) (1 : 𝕜))
      = (lam : 𝕜) • A (EuclideanSpace.single j (1 : 𝕜)) := by
  have hproj : projFin (p := 2) (Nat.le_succ k)
      (EuclideanSpace.single (Fin.castSucc j) (1 : 𝕜))
        = EuclideanSpace.single j (1 : 𝕜) := by
    ext i
    rw [projFin_apply, PiLp.single_apply, PiLp.single_apply, castLE_succ_eq_castSucc i]
    exact if_congr Fin.castSucc_inj.symm.symm rfl rfl
  rw [borderDom_apply, hproj, PiLp.single_apply,
    if_neg (Fin.castSucc_lt_last j).ne', mul_zero, zero_smul, add_zero]

private lemma borderDom_single_last :
    borderDom A x lam mu (EuclideanSpace.single (Fin.last k) (1 : 𝕜)) = (mu : 𝕜) • x := by
  have hproj : projFin (p := 2) (Nat.le_succ k)
      (EuclideanSpace.single (Fin.last k) (1 : 𝕜)) = 0 := by
    ext i
    rw [projFin_apply, PiLp.single_apply, castLE_succ_eq_castSucc i, PiLp.zero_apply,
      if_neg (Fin.castSucc_lt_last i).ne]
  rw [borderDom_apply, hproj, map_zero, smul_zero, zero_add, PiLp.single_apply,
    if_pos rfl, mul_one]

private lemma borderCod_castSucc (y : Y) (i : Fin k) :
    (borderCod B b lam mu y) (Fin.castSucc i) = (lam : 𝕜) * (B y) i := by
  rw [borderCod, add_apply, PiLp.add_apply, smul_apply, smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply,
    PiLp.smul_apply, PiLp.smul_apply, PiLp.smul_apply,
    ← castLE_succ_eq_castSucc i, padFin_castLE, PiLp.single_apply,
    if_neg ((Fin.castSucc_lt_last i).ne ∘ (castLE_succ_eq_castSucc i ▸ ·)),
    smul_zero, smul_zero, add_zero, smul_eq_mul]

private lemma borderCod_last (y : Y) :
    (borderCod B b lam mu y) (Fin.last k) = (mu : 𝕜) * b y := by
  rw [borderCod, add_apply, PiLp.add_apply, smul_apply, smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply,
    PiLp.smul_apply, PiLp.smul_apply, PiLp.smul_apply, padFin_apply,
    dif_neg (by simp), smul_zero, zero_add, PiLp.single_apply, if_pos rfl,
    smul_eq_mul, smul_eq_mul, mul_one]

/-- In `ℓ₂ᵏ⁺¹`, the squared norm splits as the squared norm of the first `k`
coordinates plus the squared modulus of the last one. -/
private lemma norm_sq_projFin_add_last (v : EuclideanSpace 𝕜 (Fin (k + 1))) :
    ‖projFin (p := 2) (Nat.le_succ k) v‖ ^ 2 + ‖v (Fin.last k)‖ ^ 2 = ‖v‖ ^ 2 := by
  have h1 : ‖v‖ ^ 2 = ∑ i : Fin (k + 1), ‖v i‖ ^ 2 := by
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
  have h2 : ‖projFin (p := 2) (Nat.le_succ k) v‖ ^ 2
      = ∑ i : Fin k, ‖v (Fin.castSucc i)‖ ^ 2 := by
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
    exact Finset.sum_congr rfl fun i _ => by
      rw [projFin_apply, castLE_succ_eq_castSucc i]
  rw [h1, h2, Fin.sum_univ_castSucc]

/-- The bordered domain map is a contraction. -/
private lemma norm_borderDom_le (hA : ‖A‖ ≤ 1) (hx : ‖x‖ ≤ 1)
    (hlam : 0 ≤ lam) (hmu : 0 ≤ mu) (hlm : lam ^ 2 + mu ^ 2 = 1) :
    ‖borderDom A x lam mu‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => ?_
  rw [one_mul, borderDom_apply]
  have h1 : ‖(lam : 𝕜) • A (projFin (p := 2) (Nat.le_succ k) v)‖
      ≤ lam * ‖projFin (p := 2) (Nat.le_succ k) v‖ := by
    rw [norm_smul, RCLike.norm_ofReal, abs_of_nonneg hlam]
    have := (A.le_opNorm (projFin (p := 2) (Nat.le_succ k) v)).trans
      (mul_le_of_le_one_left (norm_nonneg _) hA)
    exact mul_le_mul_of_nonneg_left this hlam
  have h2 : ‖((mu : 𝕜) * v (Fin.last k)) • x‖ ≤ mu * ‖v (Fin.last k)‖ := by
    rw [norm_smul, norm_mul, RCLike.norm_ofReal, abs_of_nonneg hmu, mul_assoc]
    exact mul_le_mul_of_nonneg_left (mul_le_of_le_one_right (norm_nonneg _) hx) hmu
  refine (norm_add_le _ _).trans ((add_le_add h1 h2).trans ?_)
  exact lam_mul_add_mu_mul_le' hlam hmu hlm (norm_nonneg _) (norm_nonneg _)
    (norm_nonneg v) (norm_sq_projFin_add_last v)

/-- The bordered codomain map is a contraction. -/
private lemma norm_borderCod_le (hB : ‖B‖ ≤ 1) (hb : ‖b‖ ≤ 1)
    (hlam : 0 ≤ lam) (hmu : 0 ≤ mu) (hlm : lam ^ 2 + mu ^ 2 = 1) :
    ‖borderCod B b lam mu‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun y => ?_
  rw [one_mul]
  have hsq : ‖borderCod B b lam mu y‖ ^ 2
      = lam ^ 2 * ‖B y‖ ^ 2 + mu ^ 2 * ‖b y‖ ^ 2 := by
    have h1 : ‖borderCod B b lam mu y‖ ^ 2
        = ∑ i : Fin (k + 1), ‖(borderCod B b lam mu y) i‖ ^ 2 := by
      rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
    have h2 : ‖B y‖ ^ 2 = ∑ i : Fin k, ‖(B y) i‖ ^ 2 := by
      rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
    rw [h1, Fin.sum_univ_castSucc, borderCod_last B b lam mu y]
    have h3 : ∀ i : Fin k, ‖(borderCod B b lam mu y) (Fin.castSucc i)‖ ^ 2
        = lam ^ 2 * ‖(B y) i‖ ^ 2 := by
      intro i
      rw [borderCod_castSucc B b lam mu y i, norm_mul, RCLike.norm_ofReal,
        abs_of_nonneg hlam, mul_pow]
    rw [Finset.sum_congr rfl fun i _ => h3 i, ← Finset.mul_sum, ← h2, norm_mul,
      RCLike.norm_ofReal, abs_of_nonneg hmu, mul_pow]
  have hBy : ‖B y‖ ≤ ‖y‖ :=
    (B.le_opNorm y).trans (mul_le_of_le_one_left (norm_nonneg _) hB)
  have hby : ‖b y‖ ≤ ‖y‖ :=
    (b.le_opNorm y).trans (mul_le_of_le_one_left (norm_nonneg _) hb)
  have hsq2 : ‖borderCod B b lam mu y‖ ^ 2 ≤ ‖y‖ ^ 2 := by
    rw [hsq]
    have e1 : lam ^ 2 * ‖B y‖ ^ 2 ≤ lam ^ 2 * ‖y‖ ^ 2 := by
      have := mul_self_le_mul_self (norm_nonneg (B y)) hBy
      nlinarith [sq_nonneg lam]
    have e2 : mu ^ 2 * ‖b y‖ ^ 2 ≤ mu ^ 2 * ‖y‖ ^ 2 := by
      have := mul_self_le_mul_self (norm_nonneg (b y)) hby
      nlinarith [sq_nonneg mu]
    nlinarith [e1, e2]
  calc ‖borderCod B b lam mu y‖ = Real.sqrt (‖borderCod B b lam mu y‖ ^ 2) :=
        (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt (‖y‖ ^ 2) := Real.sqrt_le_sqrt hsq2
    _ = ‖y‖ := Real.sqrt_sq (norm_nonneg _)

end Border

/-! ### The growth lemma

The determinant quantities cannot decay faster than the approximation numbers
allow. This is the new ingredient; the matching upper bound
`Δₙ₊₁ ≤ hₙ·Δₙ` is `detNumber_succ_le_hilbertNumber_mul`. -/

/-- **Growth lemma.** For every `S` and every `k`,

  `(kᵏ/(k+1)^{k+1}) · aₖ(S) · Δₖ(S) ≤ Δₖ₊₁(S)`.

Fix an admissible pair `(A, B)` for `Δₖ(S)` and put `T := B∘S∘A`. If
`det T = 0` there is nothing to prove. Otherwise `T` is invertible, so

  `L := S∘A∘T⁻¹∘B∘S`

factors through `ℓ₂ᵏ`, hence has rank at most `k`, hence `‖S - L‖ ≥ aₖ(S)`.
Pick `x ∈ B_X` with `‖(S - L)x‖` almost `‖S - L‖` and a norming functional
`b ∈ B_{Y'}`, and border the pair by them:

  `A₀(ξ ⊕ τ) = λ·Aξ + μ·τ·x`,   `B₀ y = (λ·By) ⊕ (μ·b y)`,

with `λ² + μ² = 1`, which is again a contraction pair, now for `Δₖ₊₁(S)`. Above
the corner, the last column of the matrix of `B₀SA₀` is the combination of the
first `k` columns with coefficients `(μ/λ)·ζ`, where `ζ := T⁻¹B(Sx)`, so
`det_eq_corner_mul_det_submatrix` gives

  `det (B₀SA₀) = λ^{2k}·μ²·b((S - L)x)·det T`.

The weights `λ² = k/(k+1)`, `μ² = 1/(k+1)` maximise `λ^{2k}μ²`, whose value is
then exactly `kᵏ/(k+1)^{k+1}`. -/
lemma approximationNumber_mul_detNumber_le_detNumber_succ (S : X →L[𝕜] Y) (k : ℕ) :
    (k : ℝ) ^ k / ((k : ℝ) + 1) ^ (k + 1) * approximationNumber S k * detNumber S k
      ≤ detNumber S (k + 1) := by
  classical
  set cst : ℝ := (k : ℝ) ^ k / ((k : ℝ) + 1) ^ (k + 1) with hcst
  have hcst0 : 0 ≤ cst := (growth_ratio_pos' k).le
  -- Every admissible value `r` for `Δₖ(S)` satisfies `cst · aₖ(S) · r ≤ Δₖ₊₁(S)`.
  have hkey : ∀ r ∈ detSet S k, cst * approximationNumber S k * r
      ≤ detNumber S (k + 1) := by
    rintro r ⟨A, B, hA, hB, rfl⟩
    set T : EuclideanSpace 𝕜 (Fin k) →L[𝕜] EuclideanSpace 𝕜 (Fin k) :=
      B.comp (S.comp A) with hTdef
    have hTapp : ∀ z, T z = B (S (A z)) := fun z => by
      rw [hTdef, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]
    set rT : ℝ :=
      ‖LinearMap.det (T : EuclideanSpace 𝕜 (Fin k) →ₗ[𝕜] EuclideanSpace 𝕜 (Fin k))‖ with hrT
    -- A singular compression contributes nothing.
    by_cases hdet0 : LinearMap.det
        (T : EuclideanSpace 𝕜 (Fin k) →ₗ[𝕜] EuclideanSpace 𝕜 (Fin k)) = 0
    · rw [hrT, hdet0, norm_zero, mul_zero]
      exact detNumber_nonneg S (k + 1)
    -- The rank-`k` approximant `L = S∘A∘T⁻¹∘B∘S`.
    set E := T.toContinuousLinearEquivOfDetNeZero hdet0 with hEdef
    have hEapp : ∀ z, E z = T z := fun z => by
      rw [hEdef]
      exact ContinuousLinearMap.toContinuousLinearEquivOfDetNeZero_apply T hdet0 z
    set L : X →L[𝕜] Y := (S.comp A).comp
      ((E.symm : EuclideanSpace 𝕜 (Fin k) →L[𝕜] EuclideanSpace 𝕜 (Fin k)).comp
        (B.comp S)) with hLdef
    have hLrank : L.rank ≤ (k : Cardinal) := by
      rw [hLdef]
      exact rank_comp_le_of_euclidean _ _
    have hSL : approximationNumber S k ≤ ‖S - L‖ :=
      approximationNumber_le_norm_sub hLrank
    -- The main estimate, for every `η` strictly below `‖S - L‖`.
    have hinner : ∀ η : ℝ, 0 ≤ η → η < ‖S - L‖ →
        cst * η * rT ≤ detNumber S (k + 1) := by
      intro η hη0 hηlt
      obtain ⟨x, hx1, hxη⟩ := (S - L).exists_lt_apply_of_lt_opNorm hηlt
      obtain ⟨b, hb1, hbval⟩ := exists_dual_vector'' 𝕜 ((S - L) x)
      have hbη : η < ‖b ((S - L) x)‖ := by
        rw [hbval, RCLike.norm_ofReal, abs_of_nonneg (norm_nonneg _)]
        exact hxη
      -- The optimal weights.
      have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
      set lam : ℝ := Real.sqrt ((k : ℝ) / ((k : ℝ) + 1)) with hlamdef
      set mu : ℝ := Real.sqrt (1 / ((k : ℝ) + 1)) with hmudef
      have hlam0 : 0 ≤ lam := Real.sqrt_nonneg _
      have hmu0 : 0 ≤ mu := Real.sqrt_nonneg _
      have hlam2 : lam ^ 2 = (k : ℝ) / ((k : ℝ) + 1) := Real.sq_sqrt (by positivity)
      have hmu2 : mu ^ 2 = 1 / ((k : ℝ) + 1) := Real.sq_sqrt (by positivity)
      have hlm : lam ^ 2 + mu ^ 2 = 1 := by rw [hlam2, hmu2]; field_simp
      have hcval : lam ^ (2 * k) * mu ^ 2 = cst := by
        rw [pow_mul, hlam2, hmu2, div_pow, div_mul_div_comm, mul_one, hcst, pow_succ]
      -- `lam` is positive as soon as `k ≥ 1`.
      have hlampos : 0 < k → (lam : 𝕜) ≠ 0 := by
        intro hkpos
        have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hkpos
        have hpos : 0 < lam := by rw [hlamdef]; exact Real.sqrt_pos.mpr (by positivity)
        simpa only [ne_eq, RCLike.ofReal_eq_zero] using hpos.ne'
      -- The bordered pair and the facts about it proved above.
      set A' := borderDom A x lam mu with hA'def
      set B' := borderCod B b lam mu with hB'def
      have hA'cs : ∀ j : Fin k, A' (EuclideanSpace.single (Fin.castSucc j) (1 : 𝕜))
          = (lam : 𝕜) • A (EuclideanSpace.single j (1 : 𝕜)) := fun j => by
        rw [hA'def]; exact borderDom_single_castSucc A x lam mu j
      have hA'last : A' (EuclideanSpace.single (Fin.last k) (1 : 𝕜)) = (mu : 𝕜) • x := by
        rw [hA'def]; exact borderDom_single_last A x lam mu
      have hB'cs : ∀ (y : Y) (i : Fin k),
          (B' y) (Fin.castSucc i) = (lam : 𝕜) * (B y) i := fun y i => by
        rw [hB'def]; exact borderCod_castSucc B b lam mu y i
      have hB'last : ∀ y : Y, (B' y) (Fin.last k) = (mu : 𝕜) * b y := fun y => by
        rw [hB'def]; exact borderCod_last B b lam mu y
      have hA'norm : ‖A'‖ ≤ 1 := by
        rw [hA'def]; exact norm_borderDom_le A x lam mu hA hx1.le hlam0 hmu0 hlm
      have hB'norm : ‖B'‖ ≤ 1 := by
        rw [hB'def]; exact norm_borderCod_le B b lam mu hB hb1 hlam0 hmu0 hlm
      -- The matrices of the two compositions in the standard bases.
      set bk := EuclideanSpace.basisFun (Fin k) 𝕜 with hbk
      set bk1 := EuclideanSpace.basisFun (Fin (k + 1)) 𝕜 with hbk1
      set Nmat := LinearMap.toMatrix bk.toBasis bk.toBasis
        (T : EuclideanSpace 𝕜 (Fin k) →ₗ[𝕜] EuclideanSpace 𝕜 (Fin k)) with hNmat
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
          EuclideanSpace.basisFun_apply, ContinuousLinearMap.coe_coe, hTapp]
      -- The four kinds of entries of the bordered matrix.
      have hMcc : ∀ i j : Fin k, Mmat (Fin.castSucc i) (Fin.castSucc j)
          = (lam : 𝕜) ^ 2 * Nmat i j := by
        intro i j
        rw [hMapp, hA'cs j, map_smul, map_smul, PiLp.smul_apply, hB'cs, hNapp,
          smul_eq_mul]
        ring
      have hMlc : ∀ j : Fin k, Mmat (Fin.last k) (Fin.castSucc j)
          = (lam : 𝕜) * (mu : 𝕜) * b (S (A (EuclideanSpace.single j (1 : 𝕜)))) := by
        intro j
        rw [hMapp, hA'cs j, map_smul, map_smul, PiLp.smul_apply, hB'last, smul_eq_mul]
        ring
      have hMcl : ∀ i : Fin k, Mmat (Fin.castSucc i) (Fin.last k)
          = (lam : 𝕜) * (mu : 𝕜) * (B (S x)) i := by
        intro i
        rw [hMapp, hA'last, map_smul, map_smul, PiLp.smul_apply, hB'cs, smul_eq_mul]
        ring
      have hMll : Mmat (Fin.last k) (Fin.last k) = (mu : 𝕜) ^ 2 * b (S x) := by
        rw [hMapp, hA'last, map_smul, map_smul, PiLp.smul_apply, hB'last, smul_eq_mul]
        ring
      -- The coefficients realising the last column as a combination of the others.
      set ζ : EuclideanSpace 𝕜 (Fin k) := E.symm (B (S x)) with hζdef
      have hTζ : T ζ = B (S x) := by
        rw [hζdef, ← hEapp, E.apply_symm_apply]
      have hLx : L x = S (A ζ) := by
        rw [hLdef, hζdef]
        simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe]
      have hbdiff : b ((S - L) x) = b (S x) - b (S (A ζ)) := by
        rw [sub_apply, hLx, map_sub]
      set w : Fin k → 𝕜 := fun j => ((mu : 𝕜) / (lam : 𝕜)) * ζ j with hwdef
      -- Above the corner, the last column is the `ζ`-combination of the first `k`.
      have hwrel : ∀ i : Fin k, Mmat i.castSucc (Fin.last k)
          = ∑ j, Mmat i.castSucc j.castSucc * w j := by
        intro i
        have hlamne : (lam : 𝕜) ≠ 0 := hlampos i.pos
        have hcoord : (B (S x)) i
            = ∑ j, ζ j * (B (S (A (EuclideanSpace.single j (1 : 𝕜))))) i := by
          rw [← hTζ]
          simpa only [hTapp] using coord_apply_eq_sum T ζ i
        rw [hMcl i, hcoord, Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [hMcc i j, hNapp i j, hwdef]
        field_simp
      -- The minor at the corner is `λ²` times the old matrix.
      have hsub : Mmat.submatrix Fin.castSucc Fin.castSucc = ((lam : 𝕜) ^ 2) • Nmat := by
        ext i j
        rw [Matrix.submatrix_apply, hMcc i j, Matrix.smul_apply, smul_eq_mul]
      have hminor : (Mmat.submatrix Fin.castSucc Fin.castSucc).det
          = (lam : 𝕜) ^ (2 * k) * Nmat.det := by
        rw [hsub, Matrix.det_smul, Fintype.card_fin, pow_mul]
      -- The corner entry after the column operation is `μ²·b((S - L)x)`.
      have hcorner : Mmat (Fin.last k) (Fin.last k)
            - ∑ j, Mmat (Fin.last k) j.castSucc * w j
          = (mu : 𝕜) ^ 2 * b ((S - L) x) := by
        rw [hMll, hbdiff, mul_sub]
        congr 1
        rcases Nat.eq_zero_or_pos k with rfl | hkpos
        · -- `ℓ₂⁰` is trivial, so `Aζ = 0` and both sides vanish.
          have hζ0 : ζ = 0 := PiLp.ext fun j => j.elim0
          simp [hζ0]
        · have hlamne : (lam : 𝕜) ≠ 0 := hlampos hkpos
          have hbSAζ : b (S (A ζ))
              = ∑ j, ζ j * b (S (A (EuclideanSpace.single j (1 : 𝕜)))) := by
            simpa only [ContinuousLinearMap.comp_apply, smul_eq_mul] using
              clm_apply_eq_sum (b.comp (S.comp A)) ζ
          rw [hbSAζ, Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [hMlc j, hwdef]
          field_simp
      -- Hence the determinant identity (∗).
      have hdetM : Mmat.det
          = (lam : 𝕜) ^ (2 * k) * (mu : 𝕜) ^ 2 * b ((S - L) x) * Nmat.det := by
        rw [det_eq_corner_mul_det_submatrix Mmat w hwrel, hcorner, hminor]
        ring
      have hnormdet : ‖LinearMap.det (B'.comp (S.comp A') :
            EuclideanSpace 𝕜 (Fin (k + 1)) →ₗ[𝕜] EuclideanSpace 𝕜 (Fin (k + 1)))‖
          = cst * ‖b ((S - L) x)‖ * rT := by
        rw [hrT, ← LinearMap.det_toMatrix bk1.toBasis
            (B'.comp (S.comp A') :
              EuclideanSpace 𝕜 (Fin (k + 1)) →ₗ[𝕜] EuclideanSpace 𝕜 (Fin (k + 1))),
          ← LinearMap.det_toMatrix bk.toBasis
            (T : EuclideanSpace 𝕜 (Fin k) →ₗ[𝕜] EuclideanSpace 𝕜 (Fin k)),
          ← hMmat, ← hNmat, hdetM, norm_mul, norm_mul, norm_mul, norm_pow, norm_pow,
          RCLike.norm_ofReal, RCLike.norm_ofReal, abs_of_nonneg hlam0,
          abs_of_nonneg hmu0, ← hcval]
      calc cst * η * rT
          ≤ cst * ‖b ((S - L) x)‖ * rT := by gcongr
        _ = ‖LinearMap.det (B'.comp (S.comp A') :
              EuclideanSpace 𝕜 (Fin (k + 1)) →ₗ[𝕜] EuclideanSpace 𝕜 (Fin (k + 1)))‖ :=
            hnormdet.symm
        _ ≤ detNumber S (k + 1) := norm_det_le_detNumber S hA'norm hB'norm
    -- Let `η ↗ ‖S - L‖`, which is at least `aₖ(S)`.
    have hrT0 : 0 ≤ rT := by rw [hrT]; exact norm_nonneg _
    have hfin : cst * rT * approximationNumber S k ≤ detNumber S (k + 1) := by
      refine mul_le_of_forall_lt_of_nonneg (by positivity)
        (detNumber_nonneg S (k + 1)) ?_
      intro a' ha'0 ha'lt η hη0 hηlt
      calc a' * η ≤ (cst * rT) * η := by gcongr
        _ = cst * η * rT := by ring
        _ ≤ detNumber S (k + 1) := hinner η hη0 (hηlt.trans_le hSL)
    calc cst * approximationNumber S k * rT
        = cst * rT * approximationNumber S k := by ring
      _ ≤ detNumber S (k + 1) := hfin
  -- Pass to the supremum over the admissible values.
  have hsmul : (cst * approximationNumber S k) • detNumber S k ≤ detNumber S (k + 1) := by
    rw [detNumber,
      ← Real.sSup_smul_of_nonneg (mul_nonneg hcst0 (approximationNumber_nonneg S k))]
    refine csSup_le ((detSet_nonempty S k).smul_set) ?_
    rintro y ⟨r, hr, rfl⟩
    simpa using hkey r hr
  simpa using hsmul

/-! ### Positivity of the determinant quantities -/

/-- **Positivity.** If `aₙ(S) > 0` — equivalently, if `S` has rank `> n` — then
`Δₖ(S) > 0` for all `k ≤ n+1`. Induction from `Δ₀(S) = 1` using the growth
lemma, whose factor `aₖ(S) ≥ aₙ(S)` is positive for `k ≤ n` by antitonicity. -/
lemma detNumber_pos_of_approximationNumber_pos (S : X →L[𝕜] Y) {n : ℕ}
    (h : 0 < approximationNumber S n) : ∀ k, k ≤ n + 1 → 0 < detNumber S k := by
  intro k
  induction k with
  | zero => intro _; rw [detNumber_zero]; exact one_pos
  | succ m ih =>
    intro hm
    have hm' : m ≤ n := Nat.lt_succ_iff.mp hm
    have ham : 0 < approximationNumber S m :=
      h.trans_le (approximationNumber_antitone' hm')
    have hpos : 0 < (m : ℝ) ^ m / ((m : ℝ) + 1) ^ (m + 1) *
        approximationNumber S m * detNumber S m :=
      mul_pos (mul_pos (growth_ratio_pos' m) ham) (ih (hm'.trans (Nat.le_succ n)))
    exact hpos.trans_le (approximationNumber_mul_detNumber_le_detNumber_succ S m)

/-! ### The bound between all s-numbers -/

/-- **`aₙ(S) ≤ ((n+1)^{n+1}/nⁿ)·hₙ(S)`**, the sharp form of the constant.
Chaining the growth lemma at `k = n` with the upper bound
`Δₙ₊₁(S) ≤ hₙ(S)·Δₙ(S)` gives

  `(nⁿ/(n+1)^{n+1})·aₙ(S)·Δₙ(S) ≤ Δₙ₊₁(S) ≤ hₙ(S)·Δₙ(S)`,

and `Δₙ(S) > 0` may be cancelled. -/
theorem approximationNumber_le_mul_hilbertNumber (S : X →L[𝕜] Y) (n : ℕ) :
    approximationNumber S n
      ≤ ((n : ℝ) + 1) ^ (n + 1) / (n : ℝ) ^ n * hilbertNumber S n := by
  rcases le_or_gt (approximationNumber S n) 0 with hle | hpos
  · exact hle.trans (mul_nonneg (div_nonneg (by positivity) (pow_self_pos' n).le)
      (hilbertNumber_nonneg S n))
  -- The determinant quantities are positive, so the chain can be divided by `Δₙ(S)`.
  have hΔ : 0 < detNumber S n :=
    detNumber_pos_of_approximationNumber_pos S hpos n (Nat.le_succ n)
  have hchain : (n : ℝ) ^ n / ((n : ℝ) + 1) ^ (n + 1) * approximationNumber S n *
      detNumber S n ≤ hilbertNumber S n * detNumber S n :=
    (approximationNumber_mul_detNumber_le_detNumber_succ S n).trans
      (detNumber_succ_le_hilbertNumber_mul S n)
  have hkey : (n : ℝ) ^ n / ((n : ℝ) + 1) ^ (n + 1) * approximationNumber S n
      ≤ hilbertNumber S n := le_of_mul_le_mul_right hchain hΔ
  -- Rearrange.
  rw [div_mul_eq_mul_div,
    div_le_iff₀ (pow_pos (by positivity : (0 : ℝ) < (n : ℝ) + 1) (n + 1))] at hkey
  rw [div_mul_eq_mul_div, le_div_iff₀ (pow_self_pos' n)]
  calc approximationNumber S n * (n : ℝ) ^ n
      = (n : ℝ) ^ n * approximationNumber S n := mul_comm _ _
    _ ≤ hilbertNumber S n * ((n : ℝ) + 1) ^ (n + 1) := hkey
    _ = ((n : ℝ) + 1) ^ (n + 1) * hilbertNumber S n := mul_comm _ _

/-- **The bound between all s-numbers: `aₙ(S) ≤ e·(n+1)·hₙ(S)`.** The
approximation numbers — the largest s-numbers — exceed the Hilbert numbers —
the smallest ones — by at most a factor linear in `n`. -/
theorem approximationNumber_le_e_mul_hilbertNumber (S : X →L[𝕜] Y) (n : ℕ) :
    approximationNumber S n ≤ Real.exp 1 * ((n : ℝ) + 1) * hilbertNumber S n :=
  (approximationNumber_le_mul_hilbertNumber S n).trans
    (mul_le_mul_of_nonneg_right (ratio_le_exp_mul' n) (hilbertNumber_nonneg S n))

/-- **`aₙ(S) ≤ e·(n+1)·sₙ(S)` for every s-number sequence `s`**, since the
Hilbert numbers are the smallest s-number sequence (`hilbertNumber_le_sn`). -/
theorem approximationNumber_le_e_mul_sn {s : Family 𝕜} (hs : IsSNumberSequence s)
    (S : X →L[𝕜] Y) (n : ℕ) :
    approximationNumber S n ≤ Real.exp 1 * ((n : ℝ) + 1) * s S n :=
  (approximationNumber_le_e_mul_hilbertNumber S n).trans
    (mul_le_mul_of_nonneg_left (hilbertNumber_le_sn hs S n) (by positivity))

/-- **A bound between arbitrary s-numbers: `sₙ(S) ≤ e·(n+1)·tₙ(S)`.** Any two
s-number sequences differ at most by a factor linear in `n`: bound `s` by the
largest s-numbers `aₙ` (`sn_le_approximationNumber`) and then apply the theorem
to `t`. -/
theorem sn_le_e_mul_tn {s t : Family 𝕜} (hs : IsSNumberSequence s)
    (ht : IsSNumberSequence t) (S : X →L[𝕜] Y) (n : ℕ) :
    s S n ≤ Real.exp 1 * ((n : ℝ) + 1) * t S n :=
  (sn_le_approximationNumber hs S n).trans
    (approximationNumber_le_e_mul_sn ht S n)

end SNumbers
