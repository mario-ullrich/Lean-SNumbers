# Candidates for Mathlib

Much of the project is general functional analysis that Mathlib currently
lacks, kept here only because the s-numbers need it. Grouped by topic, with the
main declarations:

* **Determinants** (`BasicResults/Determinant.lean`, entirely in Mathlib
  namespaces): `det T* = conj (det T)` (`LinearMap.det_adjoint`),
  `det T = ∏ᵢ μᵢ` for an eigenbasis (`LinearMap.det_eq_prod_of_apply_eq_smul`),
  and the bordered determinant over any commutative ring — the elementary
  column-operation form of the Schur formula
  (`Matrix.det_eq_corner_mul_det_submatrix`).
* **Quotient operator norms** (`SNumbers/Helpers.lean`): Mathlib has
  `Submodule.mkQL` and `liftQL` but no norm bounds for them —
  `Submodule.norm_mkQL_le`, `norm_mkQL_apply_le`, `norm_liftQL_le`,
  `liftQL_mkQL`. Plus the rank API for continuous maps
  (`ContinuousLinearMap.rank`, `rank_comp_comp_le`).
* **Operator norm from the unit ball** (`SNumbers/Helpers.lean`): over a densely
  normed field, a bound on the closed unit ball bounds the operator norm
  (`ContinuousLinearMap.opNorm_le_of_unit_closedBall`). Mathlib has the
  supremum identity `sSup_unitClosedBall_eq_norm` but not the bound form.
* **John's ellipsoid** (`BasicResults/John.lean`, `JohnAux.lean`): the theorem
  itself (`John.exists_maxVolume`, `john_decomposition`) with the two projection
  theorems it yields — Kadets–Snobar `‖P‖ ≤ √n` (`exists_projection`) and
  Garling–Gordon (`exists_projection_ker`). Its general-purpose ingredients:
  compactness of the convex hull of a compact set in finite dimension
  (`IsCompact.convexHull`), the supporting-vector form of Hahn–Banach dominated
  by a *seminorm* (`Seminorm.exists_inner_le_of_apply`), trace duality
  (`ContinuousLinearMap.exists_trace_repr`, `ContinuousLinearMap.trace_adjoint`),
  and the product bound `∏(1+aᵢ) ≥ 1 − 2∑aᵢ²`
  (`one_sub_two_mul_sum_sq_le_prod_one_add`, `Real.exp_sub_two_mul_sq_le`).
  Mathlib comes close on two of these: `TotallyBounded.convexHull` gives total
  boundedness of the hull, hence compactness only of its closure, and the
  Carathéodory argument supplies the missing closedness; and
  `Module.Dual.exists_extension_of_le_seminorm` gives the extension, on top of
  which Riesz produces the representing vector.
* **Auerbach's lemma** (`BasicResults/Auerbach.lean`): every finite-dimensional
  real normed space has a basis with `‖eᵢ‖ = ‖eᵢ*‖ = 1`
  (`exists_isAuerbachBasis`).
* **SVD of a compact operator** (`BasicResults/SVD.lean`, `AddOns/`): the
  Schmidt representation (`SVD.IsCompactOperator.SVD`), norm attainment
  (`SVD.IsCompactOperator.norm_isSingularValue`), Eckart–Young, and
  compact ⇔ approximable on
  Hilbert spaces (`SVD.isApproximable_iff_isCompactOperator`). Mathlib's
  `LinearMap.singularValues` is finite-dimensional and carries no decomposition;
  its own file lists as a goal the generalisation to *approximation numbers* of a
  `ContinuousLinearMap` in possibly infinite dimension — which is what this
  project builds — so `Analysis/InnerProductSpace/SingularValues.lean` is the
  natural home.
* **Complexification** (`BasicResults/Spectral/Complexification.lean`): Mathlib
  has base change of modules, but not the complexification of a real *inner
  product* space — the space, its Hermitian inner product, conjugation, and the
  norm-preserving complexification of operators (`Complexification.complexify`).
* **Multiplication operators on `L²`**
  (`BasicResults/Spectral/MultiplicationOperator.lean`, already in the
  `MeasureTheory` namespace): `Mf : L² → L²` for essentially bounded `f`, with
  multiplicativity and self-adjointness for real `f`. The norm bound
  `‖Mf‖ ≤ ‖f‖_∞` follows from Mathlib's `ContinuousLinearMap.holderL` at the
  Hölder triple `(∞, 2, 2)`.
* **Spectral toolkit** (`BasicResults/Spectral/`): monotone convergence for
  positive operators (`exists_tendsto_of_antitone_isPositive`), the Cauchy
  estimate `‖Ax‖² ≤ ‖A‖·re⟨Ax,x⟩`, commutation with the continuous functional
  calculus (`cfc_comm_of_comm`), and the spectral projection of `S*S`
  (`exists_spectral_projection`, over any `RCLike` field).
* **`PiLp` coordinates** (`SNumbers/PiLpCoordinates.lean`, flagged as
  upstreamable in its own header): the projection/embedding contractions
  `projFin`/`padFin`, `finrank_piLp`, coordinatewise norm monotonicity
  (`piLp_norm_mono`).
* **`PiLp` norm comparisons across exponents**, developed with the examples that
  need them: `‖x‖_p ≤ ‖x‖_q` for `q ≤ p`
  (`piLp_norm_le_of_exponent_ge`, `SNumbers/Examples/DiagonalMatrices.lean`) and
  `‖x‖_p ≤ m^{1/p−1/q}‖x‖_q` (`piLp_norm_le_card_rpow_mul`,
  `SNumbers/Examples/Identity.lean`). Both belong in `PiLp.lean`; the second is the
  `PiLp` reading of Mathlib's `eLpNorm_le_eLpNorm_mul_rpow_measure_univ` for the
  counting measure.
* **Sign averaging and little Grothendieck**
  (`BasicResults/LittleGrothendieck.lean`): the Rademacher identity that the
  average of `‖∑ εⱼwⱼ‖²` over all sign patterns is `∑ ‖wⱼ‖²`
  (`sum_powerset_norm_signedSum_sq`), and the resulting bounds
  `∑ ‖Beⱼ‖² ≤ ‖B‖²` for `B : ℓ_∞ → H` and `∑ ‖rowⱼ‖² ≤ ‖A‖²` for `A : H → ℓ₁`.
* **The `ℓ₁` quotient** (`SNumbers/KolmogorovLifting.lean`): the summation map
  `Q_X : ℓ¹(B_X) →L[𝕜] X`, `α ↦ ∑' x, α x • x`, with `‖Q_X‖ ≤ 1`, the
  basis-vector identity `Q_single`, the norm identity `‖B ∘ Q_X‖ = ‖B‖`
  (`norm_le_norm_comp_Q`), and the lifting `liftA` / `Q_comp_liftA`. Mathlib
  has only the vector-valued `lp.tsumCLM` and `lp.mapCLM`, which `Q_X` factors
  through.
* **Coordinate pigeonhole and flatness**
  (`SNumbers/Examples/ExHelpers.lean`): a subspace of `𝕜^m` of dimension
  `> |A|` contains a nonzero vector vanishing on `A`
  (`exists_mem_ker_coords`), and the (weighted) flatness lemma
  (`exists_flat_vector_weighted`).
