/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
import SNumbers.Approximation
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Spectral representation and the spectral projection of `S*S`

This file develops the part of the **spectral theorem** that the
`s`-numbers *uniqueness* theorem needs for **arbitrary bounded** operators
(not just compact ones).

## Why this is needed

`SNumbers.Uniqueness` rests on the single `sorry`
`SVD.exists_scalar_factorisation`: for `c < aₙ(S)` it asks for contractions
`A : ℓ₂ⁿ⁺¹ → H₁`, `B : H₂ → ℓ₂ⁿ⁺¹` with `B ∘ S ∘ A = c • id`. That
factorisation reduces to a single geometric fact:

> **(★)** for `c < aₙ(S)` there is an `(n+1)`-dimensional subspace
> `M ⊆ H₁` with `‖S x‖ ≥ c ‖x‖` for all `x ∈ M`.

The embedding `A : ℓ₂ⁿ⁺¹ ↪ M` and the left inverse `B = c · (S|_M)⁻¹` are
then elementary.

For **compact** `S`, `(★)` comes for free from the eigenvector subspace of
`S*S` (Mathlib's compact self-adjoint spectral theorem). For an **arbitrary
bounded** `S` — whose `S*S` may have purely continuous spectrum and *no*
eigenvectors — `(★)` genuinely needs the **spectral projection**
`E = E_{[c²,∞)}(S*S)` of the positive operator `P := S*S`:

* on `ran E` one has `⟨P x, x⟩ ≥ c² ‖x‖²`, i.e. `‖S x‖ ≥ c ‖x‖`;
* `‖S ∘ (1 - E)‖ ≤ c`, so if `dim (ran E) ≤ n` then `S E` is a rank `≤ n`
  operator with `‖S - S E‖ ≤ c`, contradicting `aₙ(S) > c`; hence
  `dim (ran E) ≥ n + 1`.

So the uniqueness theorem for all bounded operators needs exactly the
**spectral projection of `S*S`**, a corollary of the spectral theorem. The
full measure-theoretic multiplication-operator representation
(Dunford–Schwartz, *Linear Operators II*, p. 911) is *not* needed as an end
product, only as the cleanest vehicle to produce that projection.

## Construction plan (the engine — to be filled in)

The spectral projection is built from the **multiplication-operator
representation** of the bounded self-adjoint operator `P = S*S`. For a
separable Hilbert space this reads: there is a finite measure space
`(Ω, μ)`, a bounded measurable `f : Ω → ℝ`, and a unitary
`U : L²(Ω, μ) ≃ᵢ H` with `U⁻¹ P U = M_f` (multiplication by `f`). Then
`E := U ∘ M_{𝟙_{[t,∞)} ∘ f} ∘ U⁻¹` is the spectral projection at threshold
`t`.

Phases (each a separate, reusable building block; see the chat plan):

* **Phase 0 — `mulL2`. ✓ DONE** (`BasicResults.MultiplicationOperator`): the
  multiplication operator `M_f` on `Lp 𝕜 2 μ` for bounded measurable `f`;
  `‖M_f‖ ≤ ‖f‖∞`, `M_f ∘ M_g = M_{f g}`, `M_1 = id`, and `M_f` self-adjoint
  when `f` is real. (Adjoint `M_{f̄}` for general `f` still to add if needed.)
* **Phase 1 — CFC wiring.** Package Mathlib's `cfcHom` for the self-adjoint
  `P` as a `*`-homomorphism `Φ : C(sp P, ℂ) → (H →L H)` with `Φ id = P`,
  `Φ 1 = 1`, `Φ (star g) = (Φ g)†`, `‖Φ g‖ ≤ ‖g‖`.
* **Phase 2 — spectral measure.** For `x : H`, `g ↦ re ⟪Φ g x, x⟫` is a
  positive functional on `C(sp P, ℝ)`; Riesz–Markov
  (`MeasureTheory.…RieszMarkovKakutani`) gives a finite measure `μ_x` with
  `∫ g dμ_x = re ⟪Φ g x, x⟫` and `μ_x univ = ‖x‖²`.
* **Phase 3 — cyclic unitary.** `‖Φ g x‖ = ‖g‖_{L²(μ_x)}` (since
  `‖Φ g x‖² = ⟪Φ(ḡ g) x, x⟫`), so `g ↦ Φ g x` extends to a unitary
  `U_x : L²(μ_x) ≃ᵢ H_x` onto the cyclic subspace
  `H_x = closure {Φ g x}`.
* **Phase 4 — representation.** On the dense set `U_x⁻¹ P (Φ g x) = id · g`,
  so `U_x⁻¹ P U_x = M_{coord}`. A countable orthogonal family of cyclic
  subspaces exhausts a separable `H`; gluing the `μ_{xᵢ}` (weights `2⁻ⁱ`)
  into one finite measure yields the single `(Ω, μ, f, U)`.

## What this file states now

* `SpectralRepresentation.exists_spectral_projection` — the spectral
  projection of `S*S` at a threshold `c`, with its two bounds. This is the
  output of Phases 0–4. **Still `sorry`** (the engine).
* `SpectralRepresentation.exists_lowerBound_subspace` — the geometric fact
  `(★)`. **Proved**, depending only on `exists_spectral_projection`: the
  projection's range has dimension `≥ n+1` (else `S∘E` is low rank with
  `‖S - S∘E‖ ≤ c`, contradicting `aₙ(S) > c`), and `S` is bounded below by
  `c` there.

Wiring `SVD.exists_scalar_factorisation` to `(★)` (the elementary
embed/left-inverse construction) is the remaining downstream step.

## Status

The only remaining `sorry` is `exists_spectral_projection` — the single
spectral-theory input. Everything else (the reduction `(★)`, and the
`s`-number uniqueness proof on top of it) is complete.
-/

universe u

open scoped Cardinal
open ContinuousLinearMap

namespace SpectralRepresentation

variable {𝕜 : Type u} [RCLike 𝕜]
variable {H₁ H₂ : Type u}
variable [NormedAddCommGroup H₁] [InnerProductSpace 𝕜 H₁] [CompleteSpace H₁]
variable [NormedAddCommGroup H₂] [InnerProductSpace 𝕜 H₂] [CompleteSpace H₂]

/-! ### The positive self-adjoint operator `P = S*S`

Foundational facts about `P := S* ∘ S` used to build the spectral projection
(any construction route needs these). `P` is self-adjoint, and its quadratic
form is `⟨P x, x⟩ = ‖S x‖²` — the bridge translating spectral bounds on `P`
back into the operator-norm bounds on `S` that `exists_spectral_projection`
states. These hold over any `RCLike` field. -/

/-- `S* ∘ S` is self-adjoint. -/
theorem isSelfAdjoint_adjoint_comp_self (S : H₁ →L[𝕜] H₂) :
    IsSelfAdjoint ((adjoint S).comp S) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff', ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.adjoint_adjoint]

/-- The quadratic form of `S* ∘ S` is the squared norm of `S`:
`⟨S*S x, x⟩ = ⟨S x, S x⟩` (so its real part is `‖S x‖² ≥ 0`). -/
theorem inner_adjoint_comp_self (S : H₁ →L[𝕜] H₂) (x : H₁) :
    inner 𝕜 ((adjoint S).comp S x) x = inner 𝕜 (S x) (S x) := by
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_left]

/-- **Spectral projection of `S*S` at threshold `c`.**

There is an operator `E` on `H₁` — the spectral projection `E_{[c²,∞)}(S*S)` —
such that

* `c · ‖E x‖ ≤ ‖S (E x)‖` for every `x` — on the range of `E`, `S` is
  bounded below by `c` (the spectral lower bound `S*S ≥ c²`);
* `‖S ∘ (1 - E)‖ ≤ c` — on the complementary range, `S` is bounded above by
  `c` (`S*S ≤ c²`).

These two operator-norm bounds are all that `exists_lowerBound_subspace`
consumes; self-adjointness and idempotency of `E`, while true, are not needed
downstream and are omitted to keep the obligation minimal. This is the single
spectral-theory input needed to extend `s`-number uniqueness to arbitrary
bounded operators.

**Status: `sorry`** — the construction (Phase 2/3, `BasicResults.Spectral`)
is in progress. -/
theorem exists_spectral_projection (S : H₁ →L[𝕜] H₂) {c : ℝ} (hc0 : 0 ≤ c) :
    ∃ E : H₁ →L[𝕜] H₁,
      (∀ x : H₁, c * ‖E x‖ ≤ ‖S (E x)‖) ∧
      ‖S.comp (1 - E)‖ ≤ c := by
  sorry

/-- **(★) Lower-bound subspace.**

For a bounded `S : H₁ →L[𝕜] H₂` between Hilbert spaces and a real `c` with
`0 ≤ c < aₙ(S)`, there is an `(n+1)`-dimensional subspace `M ⊆ H₁` on which
`S` is bounded below by `c`: `‖S x‖ ≥ c ‖x‖` for all `x ∈ M`.

This is the geometric heart of `SVD.exists_scalar_factorisation` (and hence
of the `s`-number uniqueness theorem) for *arbitrary bounded* operators. It
follows from `exists_spectral_projection`: take the spectral projection `E`
of `S*S` at threshold `c`; its range has dimension `≥ n + 1` (else `S E`
would be a rank `≤ n` operator with `‖S - S E‖ ≤ c`, contradicting
`aₙ(S) > c`), and `S` is bounded below by `c` there; choose any
`(n+1)`-dimensional subspace `M` of that range.

This reduction is **proved** here; it now depends only on
`exists_spectral_projection`. -/
theorem exists_lowerBound_subspace
    (S : H₁ →L[𝕜] H₂) (n : ℕ) {c : ℝ} (hc0 : 0 ≤ c)
    (hca : c < SNumbers.approximationNumber S n) :
    ∃ M : Submodule 𝕜 H₁, FiniteDimensional 𝕜 M ∧
      Module.finrank 𝕜 M = n + 1 ∧
      ∀ x ∈ M, c * ‖x‖ ≤ ‖S x‖ := by
  classical
  obtain ⟨E, hElb, hEub⟩ := exists_spectral_projection S hc0
  set V : Submodule 𝕜 H₁ := LinearMap.range (E : H₁ →ₗ[𝕜] H₁) with hVdef
  -- `S` is bounded below by `c` on the range of `E`: every element is `E y`.
  have hbound : ∀ x ∈ V, c * ‖x‖ ≤ ‖S x‖ := by
    intro x hx
    obtain ⟨y, hy⟩ := hx
    have hEy : E y = x := hy
    have := hElb y; rwa [hEy] at this
  -- `S ∘ (1 - E)` is small, so `S ∘ E` cannot be low rank.
  have hSE : S - S.comp E = S.comp (1 - E) := by
    ext x
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.one_apply, map_sub]
  have hrank_se : (S.comp E).rank ≤ E.rank := by
    have h := ContinuousLinearMap.rank_comp_comp_le (ContinuousLinearMap.id 𝕜 H₁) E S
    rwa [ContinuousLinearMap.comp_id] at h
  -- The range of `E` has dimension at least `n + 1`.
  have hrankV : ((n + 1 : ℕ) : Cardinal) ≤ Module.rank 𝕜 V := by
    by_contra hcon
    rw [not_le] at hcon
    have hEn : E.rank ≤ (n : Cardinal) := by
      apply Order.lt_succ_iff.mp
      have hcast : ((n + 1 : ℕ) : Cardinal) = (n : Cardinal) + 1 := by push_cast; ring
      rw [Cardinal.succ_natCast, ← hcast]
      exact hcon
    have hbad : SNumbers.approximationNumber S n ≤ c :=
      le_trans (SNumbers.approximationNumber_le_norm_sub (le_trans hrank_se hEn))
        (by rw [hSE]; exact hEub)
    exact absurd hca (not_lt.mpr hbad)
  -- Extract `n + 1` independent vectors of `V`; their span is the subspace `M`.
  obtain ⟨v, hv⟩ := Module.le_rank_iff.mp hrankV
  set w : Fin (n + 1) → H₁ := fun i => (v i : H₁) with hwdef
  have hw : LinearIndependent 𝕜 w := hv.map' V.subtype (Submodule.ker_subtype V)
  refine ⟨Submodule.span 𝕜 (Set.range w),
    FiniteDimensional.span_of_finite 𝕜 (Set.finite_range w), ?_, ?_⟩
  · rw [finrank_span_eq_card hw, Fintype.card_fin]
  · intro x hx
    refine hbound x ?_
    refine (Submodule.span_le.mpr ?_) hx
    rintro _ ⟨i, rfl⟩
    exact (v i).2

end SpectralRepresentation
