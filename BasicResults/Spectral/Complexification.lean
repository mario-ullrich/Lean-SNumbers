/-
# Complexification of a real inner product space

Given a real inner product space `H`, this file builds its **complexification**
`Complexification H`: the complex inner product space whose elements are thought
of as formal sums `x + i·y` with `x, y ∈ H`.

Concretely we model `Complexification H` as the pair type `H × H` (the pair
`(x, y)` standing for `x + i·y`), equip it with

* the complex scalar multiplication
  `(a + b·i) • (x, y) = (a·x - b·y, a·y + b·x)`, and
* the Hermitian inner product
  `⟪(x₁,y₁), (x₂,y₂)⟫ = (⟪x₁,x₂⟫ + ⟪y₁,y₂⟫) + i·(⟪x₁,y₂⟫ - ⟪y₁,x₂⟫)`,

and prove that this makes `Complexification H` a complex inner product space
(`InnerProductSpace ℂ`). The canonical real-linear isometric embedding
`x ↦ x + i·0` is provided as `Complexification.ofRealLi`.

**Note.** Mathlib (as of this writing) has base change of *modules*
(`ℂ ⊗[ℝ] M` is a `Module ℂ`) but no construction equipping the complexification
of a real *inner product space* with its complex inner product. This file
supplies that missing piece, kept deliberately elementary and self-contained.
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic.Module

noncomputable section

open RCLike
open scoped ComplexConjugate

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The **complexification** of a real inner product space `H`, modelled as the
pair type `H × H`; the pair `(x, y)` represents the formal sum `x + i·y`. -/
def Complexification (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H] :
    Type _ := H × H

namespace Complexification

/-- The underlying additive group is that of `H × H`. -/
instance : AddCommGroup (Complexification H) := inferInstanceAs (AddCommGroup (H × H))

/-- The ambient real scalar multiplication is the component-wise one of `H × H`.
It is used only to state that the embedding `ofRealLi` is real-linear. -/
instance : Module ℝ (Complexification H) := inferInstanceAs (Module ℝ (H × H))

/-- Complex scalar multiplication: `(a + b·i) • (x, y) = (a·x - b·y, a·y + b·x)`. -/
instance : SMul ℂ (Complexification H) where
  smul c u := (c.re • u.1 - c.im • u.2, c.re • u.2 + c.im • u.1)

@[simp] lemma smul_fst (c : ℂ) (u : Complexification H) :
    (c • u).1 = c.re • u.1 - c.im • u.2 := rfl

@[simp] lemma smul_snd (c : ℂ) (u : Complexification H) :
    (c • u).2 = c.re • u.2 + c.im • u.1 := rfl

@[simp] lemma add_fst (u v : Complexification H) : (u + v).1 = u.1 + v.1 := rfl
@[simp] lemma add_snd (u v : Complexification H) : (u + v).2 = u.2 + v.2 := rfl
@[simp] lemma zero_fst : (0 : Complexification H).1 = 0 := rfl
@[simp] lemma zero_snd : (0 : Complexification H).2 = 0 := rfl
@[simp] lemma rsmul_fst (r : ℝ) (u : Complexification H) : (r • u).1 = r • u.1 := rfl
@[simp] lemma rsmul_snd (r : ℝ) (u : Complexification H) : (r • u).2 = r • u.2 := rfl

instance : Module ℂ (Complexification H) where
  one_smul u := by
    apply Prod.ext <;> simp only [smul_fst, smul_snd, Complex.one_re, Complex.one_im] <;> module
  mul_smul c d u := by
    apply Prod.ext <;>
      simp only [smul_fst, smul_snd, Complex.mul_re, Complex.mul_im] <;> module
  smul_zero c := by
    apply Prod.ext <;> simp only [smul_fst, smul_snd, zero_fst, zero_snd] <;> module
  smul_add c u v := by
    apply Prod.ext <;> simp only [smul_fst, smul_snd, add_fst, add_snd] <;> module
  add_smul c d u := by
    apply Prod.ext <;>
      simp only [smul_fst, smul_snd, Complex.add_re, Complex.add_im, add_fst, add_snd] <;> module
  zero_smul u := by
    apply Prod.ext <;>
      simp only [smul_fst, smul_snd, Complex.zero_re, Complex.zero_im, zero_fst, zero_snd] <;>
      module

/-- The Hermitian inner product:
`⟪(x₁,y₁), (x₂,y₂)⟫ = (⟪x₁,x₂⟫ + ⟪y₁,y₂⟫) + i·(⟪x₁,y₂⟫ - ⟪y₁,x₂⟫)`. -/
instance : Inner ℂ (Complexification H) where
  inner u v := ⟨inner ℝ u.1 v.1 + inner ℝ u.2 v.2, inner ℝ u.1 v.2 - inner ℝ u.2 v.1⟩

@[simp] lemma inner_re (u v : Complexification H) :
    (inner ℂ u v).re = inner ℝ u.1 v.1 + inner ℝ u.2 v.2 := rfl

@[simp] lemma inner_im (u v : Complexification H) :
    (inner ℂ u v).im = inner ℝ u.1 v.2 - inner ℝ u.2 v.1 := rfl

/-- The `InnerProductSpace.Core` packaging all the axioms of the complex inner
product on the complexification. -/
@[reducible] def core : InnerProductSpace.Core ℂ (Complexification H) where
  inner u v := inner ℂ u v
  conj_inner_symm u v := by
    apply Complex.ext
    all_goals
      simp only [Complex.conj_re, Complex.conj_im, inner_re, inner_im,
        real_inner_comm u.1 v.1, real_inner_comm u.2 v.2,
        real_inner_comm v.1 u.2, real_inner_comm v.2 u.1]
    all_goals ring
  re_inner_nonneg u := by
    rw [RCLike.re_to_complex, inner_re]
    exact add_nonneg real_inner_self_nonneg real_inner_self_nonneg
  add_left u v w := by
    apply Complex.ext <;>
      simp only [inner_re, inner_im, Complex.add_re, Complex.add_im, add_fst, add_snd,
        inner_add_left] <;> ring
  smul_left u v c := by
    apply Complex.ext <;>
      simp only [inner_re, inner_im, smul_fst, smul_snd, inner_sub_left, inner_add_left,
        real_inner_smul_left, Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im] <;>
      ring
  definite u h := by
    have hre : inner ℝ u.1 u.1 + inner ℝ u.2 u.2 = 0 := by
      have := congrArg Complex.re h; simpa using this
    have n1 : (0 : ℝ) ≤ inner ℝ u.1 u.1 := real_inner_self_nonneg
    have n2 : (0 : ℝ) ≤ inner ℝ u.2 u.2 := real_inner_self_nonneg
    have h1 : inner ℝ u.1 u.1 = 0 := le_antisymm (by linarith) n1
    have h2 : inner ℝ u.2 u.2 = 0 := le_antisymm (by linarith) n2
    exact Prod.ext ((inner_self_eq_zero (𝕜 := ℝ)).mp h1) ((inner_self_eq_zero (𝕜 := ℝ)).mp h2)

/-- The norm coming from the complex inner product. -/
instance : NormedAddCommGroup (Complexification H) :=
  @InnerProductSpace.Core.toNormedAddCommGroup ℂ (Complexification H) _ _ _ core

/-- The complexification of a real inner product space is a complex inner
product space. -/
instance : InnerProductSpace ℂ (Complexification H) :=
  letI : InnerProductSpace.Core ℂ (Complexification H) := core
  InnerProductSpace.ofCore inferInstance

/-- The canonical embedding `x ↦ x + i·0` of `H` into its complexification. -/
def ofReal (x : H) : Complexification H := (x, 0)

@[simp] lemma ofReal_fst (x : H) : (ofReal x).1 = x := rfl
@[simp] lemma ofReal_snd (x : H) : (ofReal x).2 = 0 := rfl

/-- The embedding `ofReal` preserves norms: `‖x + i·0‖ = ‖x‖`. -/
@[simp] lemma norm_ofReal (x : H) : ‖ofReal x‖ = ‖x‖ := by
  rw [norm_eq_sqrt_re_inner (𝕜 := ℂ)]
  simp only [RCLike.re_to_complex, inner_re, ofReal_fst, ofReal_snd, inner_zero_left, add_zero,
    real_inner_self_eq_norm_sq]
  exact Real.sqrt_sq (norm_nonneg x)

/-- The embedding `ofReal` as a real-linear isometry `H →ₗᵢ[ℝ] Complexification H`. -/
def ofRealLi : H →ₗᵢ[ℝ] Complexification H where
  toFun := ofReal
  map_add' x y := by apply Prod.ext <;> simp [ofReal, add_fst, add_snd]
  map_smul' r x := by apply Prod.ext <;> simp [ofReal, rsmul_fst, rsmul_snd]
  norm_map' := norm_ofReal

end Complexification
