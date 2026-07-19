/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
import SNumbers.Inequalities
import SNumbers.PiLpCoordinates
import BasicResults.Determinant
import BasicResults.SVD

/-!
# The maximal difference theorem: `max(cₙ, dₙ) ≤ e·(n+1)·hₙ`

For every bounded operator `S : X →L[𝕜] Y` between normed spaces over
`𝕜 ∈ {ℝ, ℂ}` and every `n`, the **maximal difference theorem**:

  `max (cₙ(S), dₙ(S)) ≤ e·(n+1)·hₙ(S)`,

where `cₙ, dₙ, hₙ` are the Gelfand, Kolmogorov and Hilbert numbers — the
maximal possible difference between the Gelfand/Kolmogorov numbers and the
*smallest* s-number sequence `hₙ` is a factor linear in `n`. Consequently the
right-hand side may be replaced by `e·(n+1)·sₙ(S)` for any s-number sequence
`s` (`max_gelfandNumber_kolmogorovNumber_le_e_mul_sn`), in particular by the
Bernstein numbers — this proves the **Mityagin–Henkin conjecture** up to the
constant `e` (`max_gelfandNumber_kolmogorovNumber_le_e_mul_bernsteinNumber`).

The proof in fact gives the slightly sharper constant
`(n+1)^{n+1}/nⁿ ≤ e·(n+1)` (the `..._le_mul_hilbertNumber` versions). By
telescoping, `∏_{k=0}^n (k+1)^{k+1}/kᵏ = (n+1)^{n+1}`, the theorem recovers
the previous geometric-mean bound
`max(cₙ, dₙ) ≤ (n+1)·(∏_{k=0}^n hₖ)^{1/(n+1)}` (Pietsch, *Operator Ideals*;
see also Ullrich, *Inequalities between s-numbers*, arXiv:2405.05509).

## The determinant quantities `Δₖ(S)`

Everything runs through the quantities

  `Δₖ(S) := sup { |det (B ∘ S ∘ A)| : A : ℓ₂ᵏ → X, B : Y → ℓ₂ᵏ, ‖A‖ ≤ 1, ‖B‖ ≤ 1 }`

(`detNumber`). Here `B ∘ S ∘ A` is an endomorphism of the `k`-dimensional
Hilbert space `ℓ₂ᵏ = EuclideanSpace 𝕜 (Fin k)`, so its determinant is a
scalar; for `k = 0` the space is trivial and every determinant equals `1`, so
`Δ₀(S) = 1` automatically. One has `Δₖ(S) ≤ ‖S‖ᵏ < ∞`
(`detNumber_le_pow_norm`, via `∏ aᵢ(T) = |det T|`). Two features make these
quantities work: they are **closed under contractive compressions** (any
contraction pair composed with an admissible pair is again admissible), and
they **do not decay too fast** from `Δₖ` to `Δₖ₊₁`:

1. **Extension lemma** (`exists_det_extension`): from an admissible pair
   `(A, B)` for `Δₖ`, a vector `u ∈ B_X`, a functional `ρ ∈ B_{Y'}`, and
   weights `λ² + μ² = 1`, build an admissible pair `(A', B')` for `Δₖ₊₁` with

     `|det (B'∘S∘A')| = λ^{2k} · μ² · |ρ(Su)| · |det (B∘S∘A)|`,

   provided the bordered matrix is block-triangular: either `B(Su) = 0`
   (Gelfand case) or `ρ` kills the range of `S∘A` (Kolmogorov case). With
   `A'(s ⊕ t) = λ·As + μ·t·u` and `B'y = (λ·By) ⊕ (μ·ρ(y))`, contractivity
   of `A'` is the two-term Cauchy–Schwarz inequality `λa + μb ≤ √(a² + b²)`,
   contractivity of `B'` is `‖B'y‖² = λ²‖By‖² + μ²|ρ(y)|²`, and the
   determinant identity is Laplace expansion along the bordered line.
2. **Oracles.** If `γ < cₙ(S)`, then for any `k ≤ n` functionals (the rows
   of an admissible `B`) there is `u ∈ B_X` with `B(Su) = 0` and
   `‖Su‖ > γ`; a Hahn–Banach functional `ρ` norms `Su`
   (`exists_gelfand_pair`). Dually for `γ < dₙ(S)`: there is `u ∈ B_X`
   whose image has distance `> γ` from `V = span(S(A(ℓ₂ᵏ)))`, and a
   functional `ρ` vanishing on `V` realises that distance
   (`exists_kolmogorov_pair`).
3. **Growth lemma.** Feeding an oracle output into the extension lemma with
   the optimal weights `λ² = k/(k+1)`, `μ² = 1/(k+1)` gives, for
   `0 ≤ γ < max(cₙ, dₙ)` and `k ≤ n`:

     `(kᵏ/(k+1)^{k+1}) · γ · Δₖ(S) ≤ Δₖ₊₁(S)`

   (`mul_detNumber_le_detNumber_succ`). In particular `Δₖ(S) > 0` for all
   `k ≤ n+1` when `γ > 0` (`detNumber_pos`).
4. **Compression bound.** For any admissible pair `(A, B)` for `Δₙ₊₁` and
   `T := B∘S∘A`, the product of the top `n` approximation numbers of `T` is
   at most `Δₙ(S)`: the diagonal factorisation `B₁∘T∘A₁ = diag(a₀,…,aₙ)`
   (`SVD.IsCompactOperator.diagonalFactorisation`), compressed to the first
   `n` coordinates, is itself an admissible pair for `Δₙ`
   (`prod_approximationNumber_le_detNumber`).
5. **Upper bound.** Combining `|det T| = ∏ₖ aₖ(T)`
   (`prod_approximationNumber_eq_norm_det`) with step 4 and
   `aₙ(T) ≤ hₙ(S)` yields `Δₙ₊₁(S) ≤ hₙ(S)·Δₙ(S)`
   (`detNumber_succ_le_hilbertNumber_mul`). Note that this bounds **every**
   element of the sup defining `Δₙ₊₁`, so no near-maximiser needs to be
   selected.
6. Chaining steps 3 (at `k = n`) and 5 and cancelling `Δₙ(S) > 0` gives
   `γ·nⁿ/(n+1)^{n+1} ≤ hₙ(S)` for every `γ < cₙ(S)` (resp. `dₙ(S)`), hence
   the theorem; finally `(n+1)^{n+1}/nⁿ = (n+1)·(1+1/n)ⁿ ≤ e·(n+1)` via
   `1 + x ≤ eˣ`.

## References

* M. Ullrich, *On bounds between s-numbers and widths of convex sets*
  (preprint, 2026): the bound `max(cₙ, dₙ) ≤ e·(n+1)·hₙ`, which proves the
  Mityagin–Henkin/Pietsch conjecture `cₙ ≲ n·bₙ` up to the constant `e`.
* A. Pietsch, *Operator Ideals*, North-Holland, 1980: the geometric-mean
  bound.
-/

universe u

open ContinuousLinearMap
open scoped Pointwise

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
    rw [hA'def, add_apply, smul_apply,
      smul_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, heL,
      EuclideanSpace.inner_single_left, map_one, one_mul, smul_smul]
  -- Coordinate formulas for `B'`.
  have hB'cs : ∀ (y : Y) (i : Fin k),
      (B' y) (Fin.castSucc i) = (lam : 𝕜) * (B y) i := by
    intro y i
    rw [hB'def, add_apply, PiLp.add_apply,
      smul_apply, smul_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply,
      PiLp.smul_apply, PiLp.smul_apply, PiLp.smul_apply, ← hcast i, padFin_castLE, heL,
      PiLp.single_apply,
      if_neg ((Fin.castSucc_lt_last i).ne ∘ (hcast i ▸ ·)), smul_zero, smul_zero, add_zero,
      smul_eq_mul]
  have hB'last : ∀ y : Y, (B' y) (Fin.last k) = (mu : 𝕜) * ρ y := by
    intro y
    rw [hB'def, add_apply, PiLp.add_apply,
      smul_apply, smul_apply,
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


/-! ### The two oracles -/

/-- **Gelfand oracle.** If `γ < cₙ(S)` and `k ≤ n`, then given
`B : Y → ℓ₂ᵏ` there are `u ∈ B_X` with `B(Su) = 0` and a norming functional
`ρ ∈ B_{Y'}` with `‖ρ(Su)‖ = ‖Su‖ > γ`. Indeed the common kernel of the `k`
functionals `y ↦ (By)ᵢ` composed with `S` is closed of codimension `≤ k ≤ n`,
so `S` retains norm `> γ` on it (`exists_mem_norm_gt_of_lt_gelfandNumber`);
Hahn–Banach (`exists_dual_vector''`) provides `ρ`. -/
lemma exists_gelfand_pair (S : X →L[𝕜] Y) {n k : ℕ} (hk : k ≤ n) {γ : ℝ}
    (hγ : γ < gelfandNumber S n) (B : Y →L[𝕜] EuclideanSpace 𝕜 (Fin k)) :
    ∃ (u : X) (ρ : Y →L[𝕜] 𝕜), ‖u‖ ≤ 1 ∧ ‖ρ‖ ≤ 1 ∧
      (∀ i, B (S u) i = 0) ∧ γ < ‖ρ (S u)‖ := by
  classical
  -- The coordinates of `B` as functionals on `Y`.
  set g : Fin k → (Y →L[𝕜] 𝕜) :=
    fun i => (innerSL 𝕜 (EuclideanSpace.single i (1 : 𝕜))).comp B with hg
  obtain ⟨M, hMc, hMr, hM0⟩ := exists_closed_codim_forall_eq_zero S g
  obtain ⟨u, huM, hu1, huγ⟩ := exists_mem_norm_gt_of_lt_gelfandNumber S hMc
    (hMr.trans (Nat.cast_le.mpr hk)) hγ
  obtain ⟨ρ, hρ1, hρval⟩ := exists_dual_vector'' 𝕜 (S u)
  refine ⟨u, ρ, hu1, hρ1, fun i => ?_, ?_⟩
  · have h0 := hM0 u huM i
    rw [hg, ContinuousLinearMap.comp_apply, innerSL_apply_apply,
      EuclideanSpace.inner_single_left, map_one, one_mul] at h0
    exact h0
  · rw [hρval, RCLike.norm_ofReal, abs_of_nonneg (norm_nonneg _)]
    exact huγ

/-- **Kolmogorov oracle.** If `γ < dₙ(S)` and `k ≤ n`, then given
`A : ℓ₂ᵏ → X` there are `u ∈ B_X` and `ρ ∈ B_{Y'}` vanishing on the range of
`S∘A` with `‖ρ(Su)‖ > γ`. Indeed `V := span{S(A eⱼ)}` has dimension
`≤ k ≤ n`, so some `u ∈ B_X` has `‖π_V(Su)‖ > γ`
(`exists_norm_mkQL_gt_of_lt_kolmogorovNumber`); a Hahn–Banach functional on
`Y ⧸ V` realising that quotient norm pulls back to `ρ`. -/
lemma exists_kolmogorov_pair (S : X →L[𝕜] Y) {n k : ℕ} (hk : k ≤ n) {γ : ℝ}
    (hγ : γ < kolmogorovNumber S n) (A : EuclideanSpace 𝕜 (Fin k) →L[𝕜] X) :
    ∃ (u : X) (ρ : Y →L[𝕜] 𝕜), ‖u‖ ≤ 1 ∧ ‖ρ‖ ≤ 1 ∧
      (∀ j, ρ (S (A (EuclideanSpace.single j (1 : 𝕜)))) = 0) ∧ γ < ‖ρ (S u)‖ := by
  classical
  set V : Submodule 𝕜 Y := Submodule.span 𝕜
    ↑(Finset.image (fun j : Fin k => S (A (EuclideanSpace.single j (1 : 𝕜))))
      Finset.univ) with hVdef
  haveI : FiniteDimensional 𝕜 V := FiniteDimensional.span_of_finite 𝕜 (Finset.finite_toSet _)
  haveI : IsClosed (V : Set Y) := V.closed_of_finiteDimensional
  have hVrank : Module.rank 𝕜 V ≤ (n : Cardinal) := by
    rw [hVdef]
    refine (rank_span_finset_le _).trans (Nat.cast_le.mpr ?_)
    exact (Finset.card_image_le.trans_eq
      (by rw [Finset.card_univ, Fintype.card_fin])).trans hk
  obtain ⟨u, hu1, huγ⟩ := exists_norm_mkQL_gt_of_lt_kolmogorovNumber S hVrank hγ
  obtain ⟨h, hh1, hhval⟩ := exists_dual_vector'' 𝕜 (V.mkQL (S u))
  refine ⟨u, h.comp V.mkQL, hu1, ?_, fun j => ?_, ?_⟩
  · exact (h.opNorm_comp_le V.mkQL).trans
      (mul_le_one₀ hh1 (norm_nonneg _) V.norm_mkQL_le)
  · have hmem : S (A (EuclideanSpace.single j (1 : 𝕜))) ∈ V := by
      rw [hVdef]
      exact Submodule.subset_span
        (Finset.mem_coe.mpr (Finset.mem_image_of_mem _ (Finset.mem_univ j)))
    rw [ContinuousLinearMap.comp_apply, V.mkQL_apply, V.mkQ_apply,
      (Submodule.Quotient.mk_eq_zero V).mpr hmem, map_zero]
  · rw [ContinuousLinearMap.comp_apply, hhval, RCLike.norm_ofReal,
      abs_of_nonneg (norm_nonneg _)]
    exact huγ

/-! ### The growth lemma -/

/-- `0 < nⁿ` in `ℝ` (with the convention `0⁰ = 1`). -/
private lemma pow_self_pos (n : ℕ) : (0 : ℝ) < (n : ℝ) ^ n := by
  cases n with
  | zero => norm_num
  | succ m => exact pow_pos (by exact_mod_cast Nat.succ_pos m) _

/-- The per-step growth factor `kᵏ/(k+1)^{k+1}` is positive. -/
private lemma growth_ratio_pos (k : ℕ) :
    (0 : ℝ) < (k : ℝ) ^ k / ((k : ℝ) + 1) ^ (k + 1) :=
  div_pos (pow_self_pos k) (pow_pos (by positivity) _)

/-- **Growth lemma (one step).** If `0 ≤ γ` is below `cₙ(S)` or below
`dₙ(S)`, then for every `k ≤ n`

  `(kᵏ/(k+1)^{k+1}) · γ · Δₖ(S) ≤ Δₖ₊₁(S)`.

For each admissible pair `(A, B)` for `Δₖ`, the appropriate oracle provides
`(u, ρ)` with `‖ρ(Su)‖ > γ` and the triangularity needed by the extension
lemma; the weights `λ² = k/(k+1)`, `μ² = 1/(k+1)` maximise `λ^{2k}μ²` and
give exactly the factor `kᵏ/(k+1)^{k+1}`. -/
lemma mul_detNumber_le_detNumber_succ (S : X →L[𝕜] Y) {n k : ℕ} (hk : k ≤ n)
    {γ : ℝ} (hγ0 : 0 ≤ γ)
    (hγ : γ < gelfandNumber S n ∨ γ < kolmogorovNumber S n) :
    (k : ℝ) ^ k / ((k : ℝ) + 1) ^ (k + 1) * γ * detNumber S k
      ≤ detNumber S (k + 1) := by
  set c : ℝ := (k : ℝ) ^ k / ((k : ℝ) + 1) ^ (k + 1) with hc
  have hc0 : 0 ≤ c := (growth_ratio_pos k).le
  -- Each admissible value `r` for `Δₖ` satisfies `c·γ·r ≤ Δₖ₊₁`.
  have hkey : ∀ r ∈ detSet S k, c * γ * r ≤ detNumber S (k + 1) := by
    rintro r ⟨A, B, hA, hB, rfl⟩
    -- The oracle, in either case.
    obtain ⟨u, ρ, hu, hρ, htri, hβ⟩ :
        ∃ (u : X) (ρ : Y →L[𝕜] 𝕜), ‖u‖ ≤ 1 ∧ ‖ρ‖ ≤ 1 ∧
          ((∀ i, B (S u) i = 0) ∨
            (∀ j, ρ (S (A (EuclideanSpace.single j (1 : 𝕜)))) = 0)) ∧
          γ < ‖ρ (S u)‖ := by
      rcases hγ with hγc | hγd
      · obtain ⟨u, ρ, h1, h2, h3, h4⟩ := exists_gelfand_pair S hk hγc B
        exact ⟨u, ρ, h1, h2, Or.inl h3, h4⟩
      · obtain ⟨u, ρ, h1, h2, h3, h4⟩ := exists_kolmogorov_pair S hk hγd A
        exact ⟨u, ρ, h1, h2, Or.inr h3, h4⟩
    -- The optimal weights.
    have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    set lam : ℝ := Real.sqrt ((k : ℝ) / ((k : ℝ) + 1)) with hlamdef
    set mu : ℝ := Real.sqrt (1 / ((k : ℝ) + 1)) with hmudef
    have hlam2 : lam ^ 2 = (k : ℝ) / ((k : ℝ) + 1) :=
      Real.sq_sqrt (by positivity)
    have hmu2 : mu ^ 2 = 1 / ((k : ℝ) + 1) := Real.sq_sqrt (by positivity)
    have hlm : lam ^ 2 + mu ^ 2 = 1 := by
      rw [hlam2, hmu2]; field_simp
    obtain ⟨A', B', hA', hB', hdet⟩ := exists_det_extension S hA hB hu hρ
      (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) hlm htri
    -- `λ^{2k}·μ² = kᵏ/(k+1)^{k+1}`.
    have hcval : lam ^ (2 * k) * mu ^ 2 = c := by
      rw [pow_mul, hlam2, hmu2, div_pow, div_mul_div_comm, mul_one, hc, pow_succ]
    calc c * γ * ‖LinearMap.det (B.comp (S.comp A) :
            EuclideanSpace 𝕜 (Fin k) →ₗ[𝕜] EuclideanSpace 𝕜 (Fin k))‖
        ≤ c * ‖ρ (S u)‖ * ‖LinearMap.det (B.comp (S.comp A) :
            EuclideanSpace 𝕜 (Fin k) →ₗ[𝕜] EuclideanSpace 𝕜 (Fin k))‖ := by
          gcongr
      _ = ‖LinearMap.det (B'.comp (S.comp A') :
            EuclideanSpace 𝕜 (Fin (k + 1)) →ₗ[𝕜] EuclideanSpace 𝕜 (Fin (k + 1)))‖ := by
          rw [hdet, hcval]
      _ ≤ detNumber S (k + 1) := norm_det_le_detNumber S hA' hB'
  -- Pass to the supremum over the admissible values.
  have hsmul : (c * γ) • detNumber S k ≤ detNumber S (k + 1) := by
    rw [detNumber, ← Real.sSup_smul_of_nonneg (mul_nonneg hc0 hγ0)]
    refine csSup_le ((detSet_nonempty S k).smul_set) ?_
    rintro x ⟨r, hr, rfl⟩
    simpa using hkey r hr
  simpa using hsmul

/-- **Positivity of the determinant quantities.** If `0 < γ` lies below
`cₙ(S)` or below `dₙ(S)`, then `Δₖ(S) > 0` for all `k ≤ n + 1`, by induction
from `Δ₀ = 1` via the growth lemma. -/
lemma detNumber_pos (S : X →L[𝕜] Y) {n : ℕ} {γ : ℝ} (hγ0 : 0 < γ)
    (hγ : γ < gelfandNumber S n ∨ γ < kolmogorovNumber S n) :
    ∀ k, k ≤ n + 1 → 0 < detNumber S k := by
  intro k
  induction k with
  | zero => intro _; rw [detNumber_zero]; exact one_pos
  | succ m ih =>
    intro hm
    have hm' : m ≤ n := Nat.lt_succ_iff.mp hm
    have hpos : 0 < (m : ℝ) ^ m / ((m : ℝ) + 1) ^ (m + 1) * γ * detNumber S m :=
      mul_pos (mul_pos (growth_ratio_pos m) hγ0) (ih (hm'.trans (Nat.le_succ n)))
    exact hpos.trans_le (mul_detNumber_le_detNumber_succ S hm' hγ0.le hγ)

/-! ### The compression bound and the upper bound `Δₙ₊₁ ≤ hₙ·Δₙ` -/

/-- **Compression bound.** For contractions `A : ℓ₂ⁿ⁺¹ → X`,
`B : Y → ℓ₂ⁿ⁺¹` and `T := B∘S∘A`, the product of the top `n` approximation
numbers of `T` is at most `Δₙ(S)`: the diagonal factorisation
`B₁∘T∘A₁ = diag(a₀(T),…,aₙ(T))` through contractions
(`SVD.IsCompactOperator.diagonalFactorisation`), compressed to the first `n`
coordinates by `padFin`/`projFin`, realises `∏_{k<n} aₖ(T)` as an admissible
determinant for `Δₙ(S)`. -/
lemma prod_approximationNumber_le_detNumber (S : X →L[𝕜] Y) {n : ℕ}
    {A : EuclideanSpace 𝕜 (Fin (n + 1)) →L[𝕜] X}
    {B : Y →L[𝕜] EuclideanSpace 𝕜 (Fin (n + 1))}
    (hA : ‖A‖ ≤ 1) (hB : ‖B‖ ≤ 1) :
    ∏ i ∈ Finset.range n, approximationNumber (B.comp (S.comp A)) i
      ≤ detNumber S n := by
  classical
  haveI : Nontrivial (EuclideanSpace 𝕜 (Fin (n + 1))) :=
    Module.nontrivial_of_finrank_pos (by rw [finrank_euclideanSpace_fin]; omega)
  set T := B.comp (S.comp A) with hTdef
  have hTc : IsCompactOperator T := isCompactOperator_of_locallyCompactSpace_rng T
  obtain ⟨A₁, B₁, hA₁, hB₁, hdiag⟩ := SVD.IsCompactOperator.diagonalFactorisation hTc n
  have hle : n ≤ n + 1 := Nat.le_succ n
  have hcast : ∀ i : Fin n, Fin.castLE hle i = Fin.castSucc i := fun i => rfl
  -- The compressed admissible pair.
  set A₂ : EuclideanSpace 𝕜 (Fin n) →L[𝕜] X :=
    (A.comp A₁).comp (padFin (p := 2)) with hA₂def
  set B₂ : Y →L[𝕜] EuclideanSpace 𝕜 (Fin n) :=
    (projFin (p := 2) hle).comp (B₁.comp B) with hB₂def
  have hA₂n : ‖A₂‖ ≤ 1 := by
    refine (opNorm_comp_le _ _).trans (mul_le_one₀ ?_ (norm_nonneg _)
      (norm_padFin_clm_le hle))
    exact (opNorm_comp_le _ _).trans (mul_le_one₀ hA (norm_nonneg _) hA₁)
  have hB₂n : ‖B₂‖ ≤ 1 := by
    refine (opNorm_comp_le _ _).trans (mul_le_one₀ (norm_projFin_clm_le hle)
      (norm_nonneg _) ?_)
    exact (opNorm_comp_le _ _).trans (mul_le_one₀ hB₁ (norm_nonneg _) hB)
  -- `padFin`/`projFin` act on standard basis vectors as expected.
  have hpad_single : ∀ j : Fin n,
      padFin (p := 2) (EuclideanSpace.single j (1 : 𝕜))
        = EuclideanSpace.single (Fin.castSucc j) (1 : 𝕜) := by
    intro j
    ext i
    rw [padFin_apply, PiLp.single_apply]
    by_cases hi : (i : ℕ) < n
    · rw [dif_pos hi, PiLp.single_apply]
      refine if_congr ?_ rfl rfl
      rw [Fin.ext_iff, Fin.ext_iff, Fin.val_castSucc]
    · rw [dif_neg hi, if_neg fun h => hi (by rw [h, Fin.val_castSucc]; exact j.isLt)]
  have hproj_single : ∀ j : Fin n,
      projFin (p := 2) hle (EuclideanSpace.single (Fin.castSucc j) (1 : 𝕜))
        = EuclideanSpace.single j (1 : 𝕜) := by
    intro j
    ext i
    rw [projFin_apply, PiLp.single_apply, PiLp.single_apply, hcast i]
    exact if_congr Fin.castSucc_inj.symm.symm rfl rfl
  -- The compressed operator is diagonal with entries `a₀(T), …, a_{n-1}(T)`.
  have hD : ∀ j : Fin n, (B₂.comp (S.comp A₂)) (EuclideanSpace.single j (1 : 𝕜))
      = (approximationNumber T (j : ℕ) : 𝕜) • EuclideanSpace.single j (1 : 𝕜) := by
    intro j
    have h1 : (B₂.comp (S.comp A₂)) (EuclideanSpace.single j (1 : 𝕜))
        = projFin (p := 2) hle
            (B₁ (T (A₁ (EuclideanSpace.single (Fin.castSucc j) (1 : 𝕜))))) := by
      rw [hA₂def, hB₂def, hTdef]
      simp only [ContinuousLinearMap.comp_apply, hpad_single j]
    rw [h1, hdiag (Fin.castSucc j), map_smul, hproj_single j, Fin.val_castSucc]
  -- Its determinant is the product of the diagonal entries (it is diagonal in the
  -- standard basis, by `hD`), via the general `det_eq_prod_of_apply_eq_smul`.
  have hdet : LinearMap.det (B₂.comp (S.comp A₂) :
        EuclideanSpace 𝕜 (Fin n) →ₗ[𝕜] EuclideanSpace 𝕜 (Fin n))
      = ∏ j : Fin n, (approximationNumber T (j : ℕ) : 𝕜) :=
    LinearMap.det_eq_prod_of_apply_eq_smul
      (EuclideanSpace.basisFun (Fin n) 𝕜).toBasis
      (B₂.comp (S.comp A₂) : EuclideanSpace 𝕜 (Fin n) →ₗ[𝕜] EuclideanSpace 𝕜 (Fin n))
      (fun j => (approximationNumber T (j : ℕ) : 𝕜))
      (fun j => by
        simpa [OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply] using hD j)
  -- Conclude.
  have hnorm : ‖LinearMap.det (B₂.comp (S.comp A₂) :
        EuclideanSpace 𝕜 (Fin n) →ₗ[𝕜] EuclideanSpace 𝕜 (Fin n))‖
      = ∏ i ∈ Finset.range n, approximationNumber T i := by
    rw [hdet, norm_prod, ← Fin.prod_univ_eq_prod_range (fun i => approximationNumber T i) n]
    exact Finset.prod_congr rfl fun j _ => by
      rw [RCLike.norm_ofReal, abs_of_nonneg (approximationNumber_nonneg _ _)]
  calc ∏ i ∈ Finset.range n, approximationNumber T i
      = ‖LinearMap.det (B₂.comp (S.comp A₂) :
          EuclideanSpace 𝕜 (Fin n) →ₗ[𝕜] EuclideanSpace 𝕜 (Fin n))‖ := hnorm.symm
    _ ≤ detNumber S n := norm_det_le_detNumber S hA₂n hB₂n

/-- **Upper bound `Δₙ₊₁(S) ≤ hₙ(S)·Δₙ(S)`.** For every admissible pair for
`Δₙ₊₁` and `T := B∘S∘A`, split `|det T| = ∏_{k≤n} aₖ(T)` into the top `n`
factors (at most `Δₙ(S)`, by the compression bound) and the last factor
`aₙ(T) ≤ hₙ(S)`. This bounds **every** element of the supremum defining
`Δₙ₊₁(S)`, so no near-maximiser is needed. -/
lemma detNumber_succ_le_hilbertNumber_mul (S : X →L[𝕜] Y) (n : ℕ) :
    detNumber S (n + 1) ≤ hilbertNumber S n * detNumber S n := by
  refine csSup_le (detSet_nonempty S (n + 1)) ?_
  rintro r ⟨A, B, hA, hB, rfl⟩
  haveI : Nontrivial (EuclideanSpace 𝕜 (Fin (n + 1))) :=
    Module.nontrivial_of_finrank_pos (by rw [finrank_euclideanSpace_fin]; omega)
  have h1 : ‖LinearMap.det (B.comp (S.comp A) :
        EuclideanSpace 𝕜 (Fin (n + 1)) →ₗ[𝕜] EuclideanSpace 𝕜 (Fin (n + 1)))‖
      = ∏ i ∈ Finset.range (n + 1), approximationNumber (B.comp (S.comp A)) i := by
    have h := prod_approximationNumber_eq_norm_det (B.comp (S.comp A))
    rw [finrank_euclideanSpace_fin] at h
    exact h.symm
  have h2 : ∏ i ∈ Finset.range n, approximationNumber (B.comp (S.comp A)) i
      ≤ detNumber S n := prod_approximationNumber_le_detNumber S hA hB
  have h3 : approximationNumber (B.comp (S.comp A)) n ≤ hilbertNumber S n := by
    have h := approximationNumber_eucl_comp_comp_le_mul_hilbertNumber S n n A B
    calc approximationNumber (B.comp (S.comp A)) n
        ≤ ‖B‖ * ‖A‖ * hilbertNumber S n := h
      _ ≤ 1 * hilbertNumber S n :=
          mul_le_mul_of_nonneg_right (mul_le_one₀ hB (norm_nonneg _) hA)
            (hilbertNumber_nonneg S n)
      _ = hilbertNumber S n := one_mul _
  rw [h1, Finset.prod_range_succ]
  calc (∏ i ∈ Finset.range n, approximationNumber (B.comp (S.comp A)) i) *
        approximationNumber (B.comp (S.comp A)) n
      ≤ detNumber S n * hilbertNumber S n :=
        mul_le_mul h2 h3 (approximationNumber_nonneg _ _) (detNumber_nonneg S n)
    _ = hilbertNumber S n * detNumber S n := mul_comm _ _

/-! ### The maximal difference theorem -/

/-- **Gelfand vs. Hilbert numbers, sharp constant.**
`cₙ(S) ≤ ((n+1)^{n+1}/nⁿ)·hₙ(S)`. -/
theorem gelfandNumber_le_mul_hilbertNumber (S : X →L[𝕜] Y) (n : ℕ) :
    gelfandNumber S n ≤ ((n : ℝ) + 1) ^ (n + 1) / (n : ℝ) ^ n * hilbertNumber S n := by
  by_contra hcon
  rw [not_le] at hcon
  have hR0 : 0 ≤ ((n : ℝ) + 1) ^ (n + 1) / (n : ℝ) ^ n * hilbertNumber S n :=
    mul_nonneg (div_nonneg (by positivity) (pow_self_pos n).le)
      (hilbertNumber_nonneg S n)
  obtain ⟨γ, hγR, hγc⟩ := exists_between hcon
  have hγ0 : 0 < γ := lt_of_le_of_lt hR0 hγR
  have hor : γ < gelfandNumber S n ∨ γ < kolmogorovNumber S n := Or.inl hγc
  have hΔ : 0 < detNumber S n := detNumber_pos S hγ0 hor n (Nat.le_succ n)
  have hchain : (n : ℝ) ^ n / ((n : ℝ) + 1) ^ (n + 1) * γ * detNumber S n
      ≤ hilbertNumber S n * detNumber S n :=
    (mul_detNumber_le_detNumber_succ S le_rfl hγ0.le hor).trans
      (detNumber_succ_le_hilbertNumber_mul S n)
  have hkey : (n : ℝ) ^ n / ((n : ℝ) + 1) ^ (n + 1) * γ ≤ hilbertNumber S n :=
    le_of_mul_le_mul_right hchain hΔ
  have h1 : (n : ℝ) ^ n * γ ≤ hilbertNumber S n * ((n : ℝ) + 1) ^ (n + 1) := by
    rw [div_mul_eq_mul_div,
      div_le_iff₀ (pow_pos (by positivity : (0 : ℝ) < (n : ℝ) + 1) (n + 1))] at hkey
    exact hkey
  have h2 : γ ≤ ((n : ℝ) + 1) ^ (n + 1) / (n : ℝ) ^ n * hilbertNumber S n := by
    rw [div_mul_eq_mul_div, le_div_iff₀ (pow_self_pos n)]
    calc γ * (n : ℝ) ^ n = (n : ℝ) ^ n * γ := mul_comm _ _
      _ ≤ hilbertNumber S n * ((n : ℝ) + 1) ^ (n + 1) := h1
      _ = ((n : ℝ) + 1) ^ (n + 1) * hilbertNumber S n := mul_comm _ _
  exact absurd h2 (not_le.mpr hγR)

/-- **Kolmogorov vs. Hilbert numbers, sharp constant.**
`dₙ(S) ≤ ((n+1)^{n+1}/nⁿ)·hₙ(S)`. -/
theorem kolmogorovNumber_le_mul_hilbertNumber (S : X →L[𝕜] Y) (n : ℕ) :
    kolmogorovNumber S n
      ≤ ((n : ℝ) + 1) ^ (n + 1) / (n : ℝ) ^ n * hilbertNumber S n := by
  by_contra hcon
  rw [not_le] at hcon
  have hR0 : 0 ≤ ((n : ℝ) + 1) ^ (n + 1) / (n : ℝ) ^ n * hilbertNumber S n :=
    mul_nonneg (div_nonneg (by positivity) (pow_self_pos n).le)
      (hilbertNumber_nonneg S n)
  obtain ⟨γ, hγR, hγd⟩ := exists_between hcon
  have hγ0 : 0 < γ := lt_of_le_of_lt hR0 hγR
  have hor : γ < gelfandNumber S n ∨ γ < kolmogorovNumber S n := Or.inr hγd
  have hΔ : 0 < detNumber S n := detNumber_pos S hγ0 hor n (Nat.le_succ n)
  have hchain : (n : ℝ) ^ n / ((n : ℝ) + 1) ^ (n + 1) * γ * detNumber S n
      ≤ hilbertNumber S n * detNumber S n :=
    (mul_detNumber_le_detNumber_succ S le_rfl hγ0.le hor).trans
      (detNumber_succ_le_hilbertNumber_mul S n)
  have hkey : (n : ℝ) ^ n / ((n : ℝ) + 1) ^ (n + 1) * γ ≤ hilbertNumber S n :=
    le_of_mul_le_mul_right hchain hΔ
  have h1 : (n : ℝ) ^ n * γ ≤ hilbertNumber S n * ((n : ℝ) + 1) ^ (n + 1) := by
    rw [div_mul_eq_mul_div,
      div_le_iff₀ (pow_pos (by positivity : (0 : ℝ) < (n : ℝ) + 1) (n + 1))] at hkey
    exact hkey
  have h2 : γ ≤ ((n : ℝ) + 1) ^ (n + 1) / (n : ℝ) ^ n * hilbertNumber S n := by
    rw [div_mul_eq_mul_div, le_div_iff₀ (pow_self_pos n)]
    calc γ * (n : ℝ) ^ n = (n : ℝ) ^ n * γ := mul_comm _ _
      _ ≤ hilbertNumber S n * ((n : ℝ) + 1) ^ (n + 1) := h1
      _ = ((n : ℝ) + 1) ^ (n + 1) * hilbertNumber S n := mul_comm _ _
  exact absurd h2 (not_le.mpr hγR)

/-- **Maximal difference theorem, sharp constant.**
`max(cₙ(S), dₙ(S)) ≤ ((n+1)^{n+1}/nⁿ)·hₙ(S)`. -/
theorem max_gelfandNumber_kolmogorovNumber_le_mul_hilbertNumber
    (S : X →L[𝕜] Y) (n : ℕ) :
    max (gelfandNumber S n) (kolmogorovNumber S n)
      ≤ ((n : ℝ) + 1) ^ (n + 1) / (n : ℝ) ^ n * hilbertNumber S n :=
  max_le (gelfandNumber_le_mul_hilbertNumber S n)
    (kolmogorovNumber_le_mul_hilbertNumber S n)

/-! ### The constant `(n+1)^{n+1}/nⁿ ≤ e·(n+1)` -/

/-- `(n+1)^{n+1}/nⁿ = (n+1)·(1+1/n)ⁿ ≤ e·(n+1)`, from `1 + x ≤ eˣ` at
`x = 1/n` raised to the `n`-th power. -/
private lemma ratio_le_exp_mul (n : ℕ) :
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
    rw [div_le_iff₀ (pow_self_pos n)]
    calc ((n : ℝ) + 1) ^ (n + 1) = ((n : ℝ) + 1) ^ n * ((n : ℝ) + 1) := pow_succ _ _
      _ ≤ Real.exp 1 * (n : ℝ) ^ n * ((n : ℝ) + 1) :=
          mul_le_mul_of_nonneg_right h3 (by positivity)
      _ = Real.exp 1 * ((n : ℝ) + 1) * (n : ℝ) ^ n := by ring

/-- **Maximal difference theorem.** `max(cₙ(S), dₙ(S)) ≤ e·(n+1)·hₙ(S)`: the Gelfand and
Kolmogorov numbers exceed the (smallest) s-numbers `hₙ` by at most a factor
linear in `n`. -/
theorem max_gelfandNumber_kolmogorovNumber_le_e_mul_hilbertNumber
    (S : X →L[𝕜] Y) (n : ℕ) :
    max (gelfandNumber S n) (kolmogorovNumber S n)
      ≤ Real.exp 1 * ((n : ℝ) + 1) * hilbertNumber S n :=
  (max_gelfandNumber_kolmogorovNumber_le_mul_hilbertNumber S n).trans
    (mul_le_mul_of_nonneg_right (ratio_le_exp_mul n) (hilbertNumber_nonneg S n))

/-- **Maximal difference theorem for arbitrary s-numbers.** Since the Hilbert numbers are
the smallest s-number sequence (`hilbertNumber_le_sn`), the bound holds with
`hₙ` replaced by any s-number sequence:
`max(cₙ(S), dₙ(S)) ≤ e·(n+1)·sₙ(S)`. -/
theorem max_gelfandNumber_kolmogorovNumber_le_e_mul_sn {s : Family 𝕜}
    (hs : IsSNumberSequence s) (S : X →L[𝕜] Y) (n : ℕ) :
    max (gelfandNumber S n) (kolmogorovNumber S n)
      ≤ Real.exp 1 * ((n : ℝ) + 1) * s S n :=
  (max_gelfandNumber_kolmogorovNumber_le_e_mul_hilbertNumber S n).trans
    (mul_le_mul_of_nonneg_left (hilbertNumber_le_sn hs S n) (by positivity))

/-- **The Mityagin–Henkin conjecture, up to the constant `e`.** The Gelfand
and Kolmogorov numbers are bounded by the Bernstein numbers:
`max(cₙ(S), dₙ(S)) ≤ e·(n+1)·bₙ(S)`. -/
theorem max_gelfandNumber_kolmogorovNumber_le_e_mul_bernsteinNumber
    (S : X →L[𝕜] Y) (n : ℕ) :
    max (gelfandNumber S n) (kolmogorovNumber S n)
      ≤ Real.exp 1 * ((n : ℝ) + 1) * bernsteinNumber S n :=
  max_gelfandNumber_kolmogorovNumber_le_e_mul_sn
    isSNumberSequence_bernsteinNumber S n

end SNumbers
