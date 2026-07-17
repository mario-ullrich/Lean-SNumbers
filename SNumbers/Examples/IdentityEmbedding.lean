/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
import SNumbers.Examples.DiagonalMatrices
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.Convex.KreinMilman

/-!
# Example: s-numbers of the identity embedding `ℓ^q_m → ℓ^p_m`

The identity map `id : ℓ^q_m → ℓ^p_m` between finite-dimensional sequence spaces
with **different** exponents (`p ≤ q`). Its s-numbers are a classical example
(Pietsch, *Eigenvalues and s-numbers*, §11.11).

This file develops the case `1 ≤ p ≤ q < ∞`:

* `piLp_norm_restrict_le` / `piLp_norm_le_card_rpow_mul` — the cross-exponent
  norm comparison `‖f‖_p ≤ (card s)^{1/p-1/q} · ‖f‖_q` (via the
  power-mean inequality `Real.rpow_sum_le_const_mul_sum_rpow_of_nonneg`);
* `idEmbed` and `norm_idEmbed` — the embedding and its operator norm
  `‖id‖ = m^{1/p-1/q}` (sharp, attained at the all-ones vector);
* `approximationNumber_idEmbed_le` — the upper bound `aₙ(id) ≤ (m-n)^{1/p-1/q}`
  (hence `sₙ(id) ≤ (m-n)^{1/p-1/q}` for every s-number, via `sₙ ≤ aₙ`);
* `approximationNumber_idEmbed_eq` — the exact value `aₙ(id) = (m-n)^{1/p-1/q}`,
  via the geometric input `exists_norm_ratio_ge_idEmbed` (the classical
  Gelfand-width lower bound, Pietsch §11.11): every subspace of dimension `≥ m-n`
  contains a vector with `p`/`q`-norm ratio `≥ (m-n)^{1/p-1/q}`, proved by a
  flatness / extreme-point argument (`exists_flat_vector`).
-/

universe u

open scoped ENNReal
open ContinuousLinearMap

namespace SNumbers

variable {𝕜 : Type u} [RCLike 𝕜] {m : ℕ}

/-- A finite exponent `p` with `1 ≤ p` has `0 < p.toReal`. -/
private lemma fact_toReal_pos {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ∞) : 0 < p.toReal :=
  ENNReal.toReal_pos (lt_of_lt_of_le zero_lt_one Fact.out).ne' hp

/-- **Cross-exponent norm comparison, restricted to a finite support.** For
`1 ≤ p ≤ q` (with `q ≠ ∞`) and `f` supported on a finite set `s`,
`‖f‖_p ≤ (card s)^{1/p - 1/q} · ‖f‖_q`. The power-mean inequality, applied over
the support `s`. -/
lemma piLp_norm_restrict_le {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (hpq : p ≤ q) (hq : q ≠ ∞) (s : Finset (Fin m)) (f : Fin m → 𝕜)
    (hf : ∀ i ∉ s, f i = 0) :
    ‖(WithLp.toLp p f : PiLp p (fun _ : Fin m => 𝕜))‖
      ≤ (s.card : ℝ) ^ (1 / p.toReal - 1 / q.toReal) *
        ‖(WithLp.toLp q f : PiLp q (fun _ : Fin m => 𝕜))‖ := by
  have hpf : p ≠ ∞ := ne_top_of_le_ne_top hq hpq
  have hP : 0 < p.toReal := fact_toReal_pos hpf
  have hQ : 0 < q.toReal := fact_toReal_pos hq
  have hPQ : p.toReal ≤ q.toReal := ENNReal.toReal_mono hq hpq
  set P := p.toReal
  set Q := q.toReal
  rw [PiLp.norm_eq_sum hP, PiLp.norm_eq_sum hQ]
  -- Restrict both sums to the support `s` (the other terms vanish).
  rw [← Finset.sum_subset (Finset.subset_univ s) (fun i _ hi => by
        rw [show (WithLp.toLp p f) i = f i from rfl, hf i hi, norm_zero, Real.zero_rpow hP.ne']),
    ← Finset.sum_subset (Finset.subset_univ s) (fun i _ hi => by
        rw [show (WithLp.toLp q f) i = f i from rfl, hf i hi, norm_zero, Real.zero_rpow hQ.ne'])]
  set SP : ℝ := ∑ i ∈ s, ‖(WithLp.toLp p f) i‖ ^ P with hSP_def
  set SQ : ℝ := ∑ i ∈ s, ‖(WithLp.toLp q f) i‖ ^ Q with hSQ_def
  have hSP : 0 ≤ SP := Finset.sum_nonneg fun i _ => Real.rpow_nonneg (norm_nonneg _) _
  have hSQ : 0 ≤ SQ := Finset.sum_nonneg fun i _ => Real.rpow_nonneg (norm_nonneg _) _
  have hr : 1 ≤ Q / P := (one_le_div hP).mpr hPQ
  have hPQe : P * (Q / P) = Q := by field_simp
  -- Power-mean over `s`: `SP^(Q/P) ≤ (card s)^(Q/P - 1) * SQ`.
  have key : SP ^ (Q / P) ≤ (s.card : ℝ) ^ (Q / P - 1) * SQ := by
    have h := Real.rpow_sum_le_const_mul_sum_rpow_of_nonneg
      (s := s) (f := fun i => ‖(WithLp.toLp p f) i‖ ^ P)
      hr (fun i _ => Real.rpow_nonneg (norm_nonneg _) _)
    rw [hSP_def, hSQ_def]
    refine h.trans_eq ?_
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Real.rpow_mul (norm_nonneg _), hPQe]
  -- Raise to the power `1/Q` and simplify the exponents.
  have h2 := Real.rpow_le_rpow (Real.rpow_nonneg hSP _) key
    (le_of_lt (by positivity : (0 : ℝ) < 1 / Q))
  rw [Real.mul_rpow (by positivity) hSQ, ← Real.rpow_mul (by positivity : (0:ℝ) ≤ (s.card:ℝ)),
    ← Real.rpow_mul hSP] at h2
  have e1 : Q / P * (1 / Q) = 1 / P := by field_simp
  have e2 : (Q / P - 1) * (1 / Q) = 1 / P - 1 / Q := by field_simp
  rwa [e1, e2] at h2

/-- **Cross-exponent norm comparison** on all of `ℓ^p_m`: for `1 ≤ p ≤ q`
(`q ≠ ∞`), `‖f‖_p ≤ m^{1/p - 1/q} · ‖f‖_q`. Sharp, with equality at the
all-ones vector. -/
lemma piLp_norm_le_card_rpow_mul {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (hpq : p ≤ q) (hq : q ≠ ∞) (f : Fin m → 𝕜) :
    ‖(WithLp.toLp p f : PiLp p (fun _ : Fin m => 𝕜))‖
      ≤ (m : ℝ) ^ (1 / p.toReal - 1 / q.toReal) *
        ‖(WithLp.toLp q f : PiLp q (fun _ : Fin m => 𝕜))‖ := by
  have h := piLp_norm_restrict_le hpq hq Finset.univ f (fun i hi => absurd (Finset.mem_univ i) hi)
  rwa [Finset.card_univ, Fintype.card_fin] at h

/-- The `L^p` norm of the all-ones vector on `Fin m` is `m^{1/p}`. -/
lemma piLp_norm_const_one {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ∞) :
    ‖(WithLp.toLp p (fun _ : Fin m => (1 : 𝕜)))‖ = (m : ℝ) ^ (1 / p.toReal) := by
  have hP : 0 < p.toReal := fact_toReal_pos hp
  rw [PiLp.norm_eq_sum hP]
  have hsum : (∑ i : Fin m, ‖(WithLp.toLp p (fun _ : Fin m => (1 : 𝕜))) i‖ ^ p.toReal)
      = (m : ℝ) := by simp [Real.one_rpow]
  rw [hsum]

/-! ## Stage 1 — the identity embedding and its operator norm -/

/-- The **identity embedding** `id : ℓ^q_m → ℓ^p_m`: the same underlying vector,
re-measured in the `p`-norm. -/
noncomputable def idEmbed (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)] :
    PiLp q (fun _ : Fin m => 𝕜) →L[𝕜] PiLp p (fun _ : Fin m => 𝕜) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x => WithLp.toLp p (WithLp.ofLp x)
      map_add' := fun x y => by ext i; simp
      map_smul' := fun c x => by ext i; simp }

@[simp] lemma idEmbed_apply {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (x : PiLp q (fun _ : Fin m => 𝕜)) (i : Fin m) : (idEmbed p q x) i = x i := rfl

/-- **Operator norm of the identity embedding** (`p ≤ q`):
`‖id : ℓ^q_m → ℓ^p_m‖ = m^{1/p - 1/q}`. -/
theorem norm_idEmbed [NeZero m] {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (hpq : p ≤ q) (hq : q ≠ ∞) :
    ‖idEmbed (𝕜 := 𝕜) (m := m) p q‖ = (m : ℝ) ^ (1 / p.toReal - 1 / q.toReal) := by
  have hpf : p ≠ ∞ := ne_top_of_le_ne_top hq hpq
  have hm : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne m)
  refine le_antisymm (opNorm_le_bound _ (by positivity) fun x => ?_) ?_
  · exact piLp_norm_le_card_rpow_mul hpq hq (WithLp.ofLp x)
  · have hb := (idEmbed (𝕜 := 𝕜) (m := m) p q).le_opNorm
      (WithLp.toLp q (fun _ : Fin m => (1 : 𝕜)))
    rw [show idEmbed (𝕜 := 𝕜) (m := m) p q (WithLp.toLp q (fun _ : Fin m => (1 : 𝕜)))
          = WithLp.toLp p (fun _ : Fin m => (1 : 𝕜)) from rfl,
      piLp_norm_const_one hpf, piLp_norm_const_one hq] at hb
    rw [Real.rpow_sub hm, div_le_iff₀ (by positivity)]
    exact hb

/-! ## Stage 2 — the upper bound `aₙ(id) ≤ (m-n)^{1/p-1/q}` for every s-number

Truncating to the first `n` coordinates gives a rank-`≤ n` approximant; the
residual is the embedding on the remaining `m-n` coordinates, of norm
`(m-n)^{1/p-1/q}` by the restricted norm comparison. As the approximation
numbers are the largest s-numbers, the bound holds for every s-number. -/

/-- The number of coordinates of `Fin m` at or beyond index `n` is `m - n`. -/
private lemma card_filter_ge (n : ℕ) (hn : n ≤ m) :
    (Finset.univ.filter (fun i : Fin m => ¬ (i : ℕ) < n)).card = m - n := by
  have hlt : (Finset.univ.filter (fun i : Fin m => (i : ℕ) < n)).card = n := by
    rw [show (Finset.univ.filter (fun i : Fin m => (i : ℕ) < n))
          = Finset.univ.image (Fin.castLE hn) from ?_,
      Finset.card_image_of_injective _ (Fin.castLE_injective hn), Finset.card_univ,
      Fintype.card_fin]
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro hi; exact ⟨⟨(i : ℕ), hi⟩, by simp⟩
    · rintro ⟨j, rfl⟩; simp only [Fin.val_castLE]; exact j.isLt
  have hsum := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin m))) (p := fun i : Fin m => (i : ℕ) < n)
  rw [hlt, Finset.card_univ, Fintype.card_fin] at hsum
  omega

/-- **Upper bound.** The `n`-th approximation number of `id : ℓ^q_m → ℓ^p_m`
(`p ≤ q`) is at most `(m-n)^{1/p-1/q}`. -/
theorem approximationNumber_idEmbed_le {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (hpq : p ≤ q) (hq : q ≠ ∞) {n : ℕ} (hn : n ≤ m) :
    approximationNumber (idEmbed (𝕜 := 𝕜) (m := m) p q) n
      ≤ ((m - n : ℕ) : ℝ) ^ (1 / p.toReal - 1 / q.toReal) := by
  -- The rank-`≤ n` approximant `L = id ∘ Pₙ`, written `B ∘ id_{ℓ^q_n} ∘ A`.
  set A : PiLp q (fun _ : Fin m => 𝕜) →L[𝕜] PiLp q (fun _ : Fin n => 𝕜) :=
    projFin hn with hA
  set B : PiLp q (fun _ : Fin n => 𝕜) →L[𝕜] PiLp p (fun _ : Fin m => 𝕜) :=
    (idEmbed p q).comp padFin with hB
  set L := B.comp ((ContinuousLinearMap.id 𝕜 (PiLp q (fun _ : Fin n => 𝕜))).comp A) with hL
  have hLrank : L.rank ≤ (n : Cardinal) :=
    (ContinuousLinearMap.rank_comp_comp_le A _ B).trans_eq (rank_id_piLp n)
  -- The residual zeros the first `n` coordinates.
  have hres : ∀ x : PiLp q (fun _ : Fin m => 𝕜), (idEmbed (𝕜 := 𝕜) (m := m) p q - L) x
      = WithLp.toLp p (fun i : Fin m => if (i : ℕ) < n then 0 else (WithLp.ofLp x) i) := by
    intro x; ext i
    simp only [hL, hA, hB, ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.id_apply, PiLp.sub_apply, idEmbed_apply]
    rw [padFin_projFin_apply]
    by_cases hi : (i : ℕ) < n <;> simp [hi]
  have hbound : ‖idEmbed (𝕜 := 𝕜) (m := m) p q - L‖
      ≤ ((m - n : ℕ) : ℝ) ^ (1 / p.toReal - 1 / q.toReal) := by
    refine opNorm_le_bound _ (by positivity) fun x => ?_
    rw [hres x]
    set g : Fin m → 𝕜 := fun i => if (i : ℕ) < n then 0 else (WithLp.ofLp x) i with hg
    have hsupp : ∀ i ∉ Finset.univ.filter (fun i : Fin m => ¬ (i : ℕ) < n), g i = 0 := by
      intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hi
      simp [hg, hi]
    have hmono : ‖(WithLp.toLp q g : PiLp q (fun _ : Fin m => 𝕜))‖ ≤ ‖x‖ :=
      piLp_norm_mono fun i => by
        simp only [hg]; split_ifs with h <;> simp
    calc ‖(WithLp.toLp p g : PiLp p (fun _ : Fin m => 𝕜))‖
        ≤ ((Finset.univ.filter (fun i : Fin m => ¬ (i : ℕ) < n)).card : ℝ)
            ^ (1 / p.toReal - 1 / q.toReal) * ‖(WithLp.toLp q g : PiLp q (fun _ : Fin m => 𝕜))‖ :=
          piLp_norm_restrict_le hpq hq _ g hsupp
      _ = ((m - n : ℕ) : ℝ) ^ (1 / p.toReal - 1 / q.toReal)
            * ‖(WithLp.toLp q g : PiLp q (fun _ : Fin m => 𝕜))‖ := by rw [card_filter_ge n hn]
      _ ≤ ((m - n : ℕ) : ℝ) ^ (1 / p.toReal - 1 / q.toReal) * ‖x‖ := by gcongr
  exact (approximationNumber_le_norm_sub hLrank).trans hbound

/-! ## Stage 3 — the lower bound `(m-n)^{1/p-1/q} ≤ aₙ(id)`

For any rank-`≤ n` operator `L`, its kernel has dimension `≥ m - n`, and
`(id - L)` agrees with `id` there. The crux is a **classical geometric fact**
(Pietsch, *Eigenvalues and s-numbers*, §11.11; the Gelfand-width lower bound):
every subspace of dimension `≥ m - n` contains a vector whose `p`-norm is at
least `(m-n)^{1/p-1/q}` times its `q`-norm. Its proof is a volumetric/averaging
argument. -/

/-- **Coordinate pigeonhole.** A subspace `V ⊆ 𝕜^m` whose dimension exceeds the
size of a coordinate set `A` contains a nonzero vector vanishing on `A`. The
restriction `V → (A → 𝕜)` has range of dimension `≤ |A| < dim V`, so a nonzero
kernel by rank–nullity. -/
private lemma exists_mem_ker_coords {V : Submodule 𝕜 (Fin m → 𝕜)}
    {A : Finset (Fin m)} (hA : A.card < Module.finrank 𝕜 V) :
    ∃ y ∈ V, y ≠ 0 ∧ ∀ i ∈ A, y i = 0 := by
  classical
  set r : V →ₗ[𝕜] (A → 𝕜) :=
    LinearMap.pi (fun i : A => (LinearMap.proj (i : Fin m)).comp V.subtype) with hr
  have hrange : Module.finrank 𝕜 (LinearMap.range r) ≤ A.card := by
    calc Module.finrank 𝕜 (LinearMap.range r)
        ≤ Module.finrank 𝕜 (A → 𝕜) := Submodule.finrank_le _
      _ = A.card := by rw [Module.finrank_pi, Fintype.card_coe]
  have hker : 0 < Module.finrank 𝕜 (LinearMap.ker r) := by
    have hrn := r.finrank_range_add_finrank_ker
    omega
  have hne : LinearMap.ker r ≠ ⊥ := by
    intro h; rw [h, finrank_bot] at hker; exact lt_irrefl 0 hker
  obtain ⟨z, hzmem, hz0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  refine ⟨(z : Fin m → 𝕜), z.2, fun h => hz0 (Submodule.coe_eq_zero.mp h), fun i hi => ?_⟩
  have hz : r z = 0 := LinearMap.mem_ker.mp hzmem
  have hzi := congrFun hz ⟨i, hi⟩
  simpa [hr, LinearMap.pi_apply, LinearMap.comp_apply, LinearMap.proj_apply,
    Submodule.subtype_apply] using hzi

/-- **Flatness lemma.** A subspace `V ⊆ 𝕜^m` of dimension `≥ k ≥ 1` contains a
nonzero vector `x` with `‖x i‖ ≤ 1` everywhere and `‖x i‖ = 1` on at least `k`
coordinates. An extreme point `x` of the compact set `B = {x ∈ V : ‖x‖_∞ ≤ 1}`
(Krein–Milman) must saturate `≥ dim V` coordinates: otherwise the
coordinate-pigeonhole vector `w` vanishing on the saturated set `S` makes `x` the
midpoint of a nondegenerate segment `x ± ε·w ⊆ B`, contradicting extremality. -/
private lemma exists_flat_vector {V : Submodule 𝕜 (Fin m → 𝕜)} {k : ℕ}
    (hk : 1 ≤ k) (hkV : k ≤ Module.finrank 𝕜 V) :
    ∃ x ∈ V, x ≠ 0 ∧ (∀ i, ‖x i‖ ≤ 1) ∧
      k ≤ (Finset.univ.filter (fun i => ‖x i‖ = 1)).card := by
  classical
  set B : Set (Fin m → 𝕜) := {x | x ∈ V ∧ ∀ i, ‖x i‖ ≤ 1} with hBdef
  have hBne : B.Nonempty := ⟨0, V.zero_mem, by simp⟩
  have hBeq : B = (V : Set (Fin m → 𝕜)) ∩ ⋂ i, {x : Fin m → 𝕜 | ‖x i‖ ≤ 1} := by
    ext x; simp only [hBdef, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter, SetLike.mem_coe]
  have hBclosed : IsClosed B := by
    rw [hBeq]
    refine V.closed_of_finiteDimensional.inter (isClosed_iInter fun i => ?_)
    exact isClosed_le ((continuous_apply i).norm) continuous_const
  have hBbdd : Bornology.IsBounded B := by
    refine (Metric.isBounded_closedBall (x := (0 : Fin m → 𝕜)) (r := 1)).subset ?_
    intro x hx
    simp only [Metric.mem_closedBall, dist_zero_right]
    exact (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun i => by simpa using hx.2 i
  have hBcompact : IsCompact B := Metric.isCompact_of_isClosed_isBounded hBclosed hBbdd
  obtain ⟨x, hxep⟩ := hBcompact.extremePoints_nonempty hBne
  rw [mem_extremePoints_iff_left] at hxep
  obtain ⟨hxB, hxext⟩ := hxep
  set S : Finset (Fin m) := Finset.univ.filter (fun i => ‖x i‖ = 1) with hSdef
  have hxle : ∀ i, ‖x i‖ ≤ 1 := hxB.2
  have hmemS : ∀ i, i ∈ S ↔ ‖x i‖ = 1 := by
    intro i; rw [hSdef, Finset.mem_filter]; simp [Finset.mem_univ]
  have hcard : Module.finrank 𝕜 V ≤ S.card := by
    by_contra hlt
    push Not at hlt
    obtain ⟨w, hwV, hw0, hwS⟩ := exists_mem_ker_coords (V := V) (A := S) hlt
    have hSc : (Finset.univ.filter (fun i => i ∉ S)).Nonempty := by
      rw [Finset.filter_nonempty_iff]
      by_contra h
      push Not at h
      have : S = Finset.univ := Finset.eq_univ_of_forall fun i => h i (Finset.mem_univ i)
      rw [this, Finset.card_univ, Fintype.card_fin] at hlt
      exact absurd (lt_of_lt_of_le hlt (Submodule.finrank_le V)) (by simp)
    have hMpos : 0 < ‖w‖ := norm_pos_iff.mpr hw0
    set d : ℝ := (Finset.univ.filter (fun i => i ∉ S)).inf' hSc (fun i => 1 - ‖x i‖) with hd
    have hdpos : 0 < d := by
      rw [hd, Finset.lt_inf'_iff]
      intro i hi
      rw [Finset.mem_filter] at hi
      have : ‖x i‖ < 1 := lt_of_le_of_ne (hxle i) (fun hh => hi.2 ((hmemS i).mpr hh))
      linarith
    set ε : ℝ := d / ‖w‖ with hε
    have hεpos : 0 < ε := div_pos hdpos hMpos
    set c : 𝕜 := RCLike.ofReal ε with hc
    have hcnorm : ‖c‖ = ε := by rw [hc, RCLike.norm_ofReal, abs_of_pos hεpos]
    have hpm : ∀ (σ : 𝕜), ‖σ‖ ≤ ε → ∀ i, ‖x i + σ • w i‖ ≤ 1 := by
      intro σ hσ i
      by_cases hi : i ∈ S
      · rw [hwS i hi, smul_zero, add_zero]; exact le_of_eq ((hmemS i).mp hi)
      · have hxi1 : ‖x i‖ < 1 := lt_of_le_of_ne (hxle i) (fun hh => hi ((hmemS i).mpr hh))
        have hslack : d ≤ 1 - ‖x i‖ :=
          hd ▸ Finset.inf'_le _ (by rw [Finset.mem_filter]; exact ⟨Finset.mem_univ i, hi⟩)
        calc ‖x i + σ • w i‖ ≤ ‖x i‖ + ‖σ • w i‖ := norm_add_le _ _
          _ = ‖x i‖ + ‖σ‖ * ‖w i‖ := by rw [norm_smul]
          _ ≤ ‖x i‖ + ε * ‖w‖ := by gcongr; exact norm_le_pi_norm w i
          _ = ‖x i‖ + d := by rw [hε, div_mul_cancel₀ _ (ne_of_gt hMpos)]
          _ ≤ 1 := by linarith
    have hmem1 : x + c • w ∈ B :=
      ⟨V.add_mem hxB.1 (V.smul_mem c hwV), fun i => by
        simpa [Pi.add_apply, Pi.smul_apply] using hpm c (le_of_eq hcnorm) i⟩
    have hmem2 : x - c • w ∈ B :=
      ⟨V.sub_mem hxB.1 (V.smul_mem c hwV), fun i => by
        have h := hpm (-c) (by rw [norm_neg]; exact le_of_eq hcnorm) i
        simpa [Pi.sub_apply, Pi.smul_apply, sub_eq_add_neg, neg_smul] using h⟩
    have hseg : x ∈ openSegment ℝ (x + c • w) (x - c • w) :=
      ⟨1/2, 1/2, by norm_num, by norm_num, by norm_num, by module⟩
    have heq := hxext (x + c • w) hmem1 (x - c • w) hmem2 hseg
    have hcw : c • w = 0 := by
      have h2 : x + c • w = x + 0 := by rw [add_zero]; exact heq
      exact add_left_cancel h2
    rcases smul_eq_zero.mp hcw with h | h
    · exact (RCLike.ofReal_ne_zero.mpr (ne_of_gt hεpos)) h
    · exact hw0 h
  refine ⟨x, hxB.1, fun hx0 => ?_, hxB.2, le_trans hkV hcard⟩
  obtain ⟨i, hi⟩ := Finset.card_pos.mp (le_trans hk (le_trans hkV hcard))
  have hxi := (hmemS i).mp hi
  rw [hx0] at hxi
  simp at hxi

/-- **Interpolation for a flat vector.** If `‖w i‖ ≤ 1` everywhere and `‖w i‖ = 1`
on at least `k` coordinates (`1 ≤ p ≤ q < ∞`), then `k^{1/p-1/q}·‖w‖_q ≤ ‖w‖_p`.
With `Sp = ∑‖w i‖^p`, `Sq = ∑‖w i‖^q`: `k ≤ Sp` (the `k` saturated coordinates),
`Sq ≤ Sp` (each `‖w i‖^q ≤ ‖w i‖^p` on `[0,1]`), and the exponent bookkeeping. -/
private lemma norm_ratio_of_flat {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (hpq : p ≤ q) (hq : q ≠ ∞) {k : ℕ} (hk : 1 ≤ k) (w : Fin m → 𝕜)
    (hle : ∀ i, ‖w i‖ ≤ 1)
    (hk_card : k ≤ (Finset.univ.filter (fun i => ‖w i‖ = 1)).card) :
    (k : ℝ) ^ (1 / p.toReal - 1 / q.toReal) *
        ‖(WithLp.toLp q w : PiLp q (fun _ : Fin m => 𝕜))‖
      ≤ ‖(WithLp.toLp p w : PiLp p (fun _ : Fin m => 𝕜))‖ := by
  have hpf : p ≠ ∞ := ne_top_of_le_ne_top hq hpq
  have hP : 0 < p.toReal := fact_toReal_pos hpf
  have hQ : 0 < q.toReal := fact_toReal_pos hq
  have hPQ : p.toReal ≤ q.toReal := ENNReal.toReal_mono hq hpq
  set P := p.toReal
  set Q := q.toReal
  set Sp : ℝ := ∑ i, ‖w i‖ ^ P with hSp
  set Sq : ℝ := ∑ i, ‖w i‖ ^ Q with hSq
  have hSpnn : 0 ≤ Sp := Finset.sum_nonneg fun i _ => Real.rpow_nonneg (norm_nonneg _) _
  have hSqnn : 0 ≤ Sq := Finset.sum_nonneg fun i _ => Real.rpow_nonneg (norm_nonneg _) _
  have hnp : ‖(WithLp.toLp p w : PiLp p (fun _ : Fin m => 𝕜))‖ = Sp ^ (1 / P) := by
    rw [PiLp.norm_eq_sum hP]
  have hnq : ‖(WithLp.toLp q w : PiLp q (fun _ : Fin m => 𝕜))‖ = Sq ^ (1 / Q) := by
    rw [PiLp.norm_eq_sum hQ]
  rw [hnp, hnq]
  have hkSp : (k : ℝ) ≤ Sp := by
    have hcard_le : ((Finset.univ.filter (fun i => ‖w i‖ = 1)).card : ℝ) ≤ Sp := by
      rw [hSp]
      calc ((Finset.univ.filter (fun i => ‖w i‖ = 1)).card : ℝ)
          = ∑ _i ∈ Finset.univ.filter (fun i => ‖w i‖ = 1), (1 : ℝ) := by
            rw [Finset.sum_const, nsmul_eq_mul, mul_one]
        _ = ∑ i ∈ Finset.univ.filter (fun i => ‖w i‖ = 1), ‖w i‖ ^ P := by
            refine Finset.sum_congr rfl fun i hi => ?_
            rw [Finset.mem_filter] at hi; rw [hi.2, Real.one_rpow]
        _ ≤ ∑ i, ‖w i‖ ^ P :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
              (fun i _ _ => Real.rpow_nonneg (norm_nonneg _) _)
    exact le_trans (Nat.cast_le.mpr hk_card) hcard_le
  have hSp_pos : 0 < Sp := lt_of_lt_of_le (by exact_mod_cast hk) hkSp
  have hSqSp : Sq ≤ Sp := by
    rw [hSq, hSp]
    refine Finset.sum_le_sum fun i _ => ?_
    by_cases h0 : ‖w i‖ = 0
    · simp only [h0, Real.zero_rpow hP.ne', Real.zero_rpow hQ.ne', le_refl]
    · exact Real.rpow_le_rpow_of_exponent_ge (lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0))
        (hle i) hPQ
  have hexp : 0 ≤ 1 / P - 1 / Q := by
    have : 1 / Q ≤ 1 / P := one_div_le_one_div_of_le hP hPQ
    linarith
  calc (k : ℝ) ^ (1 / P - 1 / Q) * Sq ^ (1 / Q)
      ≤ (k : ℝ) ^ (1 / P - 1 / Q) * Sp ^ (1 / Q) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hSqnn hSqSp (by positivity))
          (Real.rpow_nonneg (Nat.cast_nonneg k) _)
    _ ≤ Sp ^ (1 / P - 1 / Q) * Sp ^ (1 / Q) :=
        mul_le_mul_of_nonneg_right (Real.rpow_le_rpow (Nat.cast_nonneg k) hkSp hexp)
          (Real.rpow_nonneg hSpnn _)
    _ = Sp ^ (1 / P) := by rw [← Real.rpow_add hSp_pos]; congr 1; ring

/-- **Geometric input.** Every subspace `V ⊆ ℓ^q_m` of dimension `≥ m - n`
contains a nonzero `x` with `(m-n)^{1/p-1/q} · ‖x‖_q ≤ ‖x‖_p` (`= ‖id x‖`).
The classical Gelfand-width lower bound (Pietsch §11.11). -/
lemma exists_norm_ratio_ge_idEmbed {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (hpq : p ≤ q) (hq : q ≠ ∞) {n : ℕ} (hn : n < m)
    (V : Submodule 𝕜 (PiLp q (fun _ : Fin m => 𝕜))) (hV : m - n ≤ Module.finrank 𝕜 V) :
    ∃ x ∈ V, x ≠ 0 ∧ ((m - n : ℕ) : ℝ) ^ (1 / p.toReal - 1 / q.toReal) * ‖x‖
      ≤ ‖idEmbed (𝕜 := 𝕜) (m := m) p q x‖ := by
  set e : PiLp q (fun _ : Fin m => 𝕜) ≃ₗ[𝕜] (Fin m → 𝕜) :=
    WithLp.linearEquiv q 𝕜 (Fin m → 𝕜) with he
  have hkV' : m - n ≤
      Module.finrank 𝕜 (V.map (e : PiLp q (fun _ : Fin m => 𝕜) →ₗ[𝕜] (Fin m → 𝕜))) :=
    le_of_le_of_eq hV (LinearEquiv.finrank_map_eq e V).symm
  obtain ⟨w, hwV', hw0, hwle, hwcard⟩ := exists_flat_vector (k := m - n) (by omega) hkV'
  obtain ⟨v, hvV, hev⟩ := Submodule.mem_map.mp hwV'
  have hxV : e.symm w ∈ V := by rw [← hev]; simpa using hvV
  refine ⟨e.symm w, hxV, fun h0 => hw0 (by simpa using congrArg e h0),
    norm_ratio_of_flat hpq hq (by omega) w hwle hwcard⟩

/-- **Lower bound.** `(m-n)^{1/p-1/q} ≤ aₙ(id : ℓ^q_m → ℓ^p_m)` (`p ≤ q`),
via the geometric input `exists_norm_ratio_ge_idEmbed`. -/
theorem le_approximationNumber_idEmbed {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (hpq : p ≤ q) (hq : q ≠ ∞) {n : ℕ} (hn : n < m) :
    ((m - n : ℕ) : ℝ) ^ (1 / p.toReal - 1 / q.toReal)
      ≤ approximationNumber (idEmbed (𝕜 := 𝕜) (m := m) p q) n := by
  refine le_csInf (approximationSet_nonempty _ _) ?_
  rintro r ⟨L, hL, rfl⟩
  -- The kernel of a rank-`≤ n` operator has dimension `≥ m - n`.
  have hker : m - n ≤ Module.finrank 𝕜 (LinearMap.ker (L : PiLp q (fun _ : Fin m => 𝕜) →ₗ[𝕜] PiLp p (fun _ : Fin m => 𝕜))) := by
    have hrn := (L : PiLp q (fun _ : Fin m => 𝕜) →ₗ[𝕜]
      PiLp p (fun _ : Fin m => 𝕜)).finrank_range_add_finrank_ker
    have hrange : Module.finrank 𝕜 (LinearMap.range (L : PiLp q (fun _ : Fin m => 𝕜) →ₗ[𝕜] PiLp p (fun _ : Fin m => 𝕜))) ≤ n :=
      Module.finrank_le_of_rank_le hL
    rw [finrank_piLp] at hrn
    omega
  obtain ⟨x, hxV, hxne, hxbound⟩ := exists_norm_ratio_ge_idEmbed hpq hq hn
    (LinearMap.ker (L : PiLp q (fun _ : Fin m => 𝕜) →ₗ[𝕜] PiLp p (fun _ : Fin m => 𝕜))) hker
  have hLx : L x = 0 := LinearMap.mem_ker.mp hxV
  have happ : (idEmbed (𝕜 := 𝕜) (m := m) p q - L) x = idEmbed p q x := by
    simp [ContinuousLinearMap.sub_apply, hLx]
  have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hxne
  refine le_of_mul_le_mul_right ?_ hxpos
  calc ((m - n : ℕ) : ℝ) ^ (1 / p.toReal - 1 / q.toReal) * ‖x‖
      ≤ ‖idEmbed p q x‖ := hxbound
    _ = ‖(idEmbed (𝕜 := 𝕜) (m := m) p q - L) x‖ := by rw [happ]
    _ ≤ ‖idEmbed (𝕜 := 𝕜) (m := m) p q - L‖ * ‖x‖ :=
        (idEmbed (𝕜 := 𝕜) (m := m) p q - L).le_opNorm x

/-- **The approximation numbers of the identity embedding** (`p ≤ q`):
`aₙ(id : ℓ^q_m → ℓ^p_m) = (m-n)^{1/p-1/q}`, via the geometric input
`exists_norm_ratio_ge_idEmbed`. -/
theorem approximationNumber_idEmbed_eq {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (hpq : p ≤ q) (hq : q ≠ ∞) {n : ℕ} (hn : n < m) :
    approximationNumber (idEmbed (𝕜 := 𝕜) (m := m) p q) n
      = ((m - n : ℕ) : ℝ) ^ (1 / p.toReal - 1 / q.toReal) :=
  le_antisymm (approximationNumber_idEmbed_le hpq hq hn.le) (le_approximationNumber_idEmbed hpq hq hn)
