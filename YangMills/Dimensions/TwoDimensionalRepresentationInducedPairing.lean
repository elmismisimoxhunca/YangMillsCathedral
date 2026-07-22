/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Dimensions.TwoDimensionalLatticeSpacingActionFamily
import YangMills.Geometry.InvariantInnerProduct
import YangMills.Mathematics.FiniteMatrixRealContinuousBilinear
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions

/-!
# Driver's representation differential and induced Lie-algebra pairing

Driver §2 fixes a representation `p`, defines `p_*` as its derivative, assumes `p_*` injective, and
uses the real pairing `(X,Y)_p = -Re tr(p_*X p_*Y)` to define the Casimir and heat semigroup. This
module records that exact common-representation chain. It does not construct such a representation,
inner product, heat kernel, or convergence theorem.
-/

namespace YangMills.Dimensions

open YangMills.Mathematics
open scoped Manifold ContDiff BigOperators

noncomputable section

universe uE uG

variable
    {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {G : Type uG} [Group G] [TopologicalSpace G]
    [T2Space G] [SecondCountableTopology G] [ChartedSpace E G]
    [LieGroup (modelWithCornersSelf ℝ E) ∞ G]

/-- One actual smooth unitary matrix representation with Driver's injective differential `p_*`. -/
structure SmoothUnitaryRepresentationDifferentialData extends
    FiniteDimensionalUnitaryRepresentationCharacterData G where
  representation_contMDiff : ContMDiff (modelWithCornersSelf ℝ E)
    (modelWithCornersSelf ℝ
      (Fin toFiniteDimensionalUnitaryRepresentationCharacterData.dimension →
        Fin toFiniteDimensionalUnitaryRepresentationCharacterData.dimension → ℂ)) ∞
    (fun g i j => toFiniteDimensionalUnitaryRepresentationCharacterData.representation g i j)
  differential_injective : Function.Injective
    (mfderiv (modelWithCornersSelf ℝ E)
      (modelWithCornersSelf ℝ
        (Fin toFiniteDimensionalUnitaryRepresentationCharacterData.dimension →
          Fin toFiniteDimensionalUnitaryRepresentationCharacterData.dimension → ℂ))
      (fun g i j => toFiniteDimensionalUnitaryRepresentationCharacterData.representation g i j)
      (1 : G))

namespace SmoothUnitaryRepresentationDifferentialData

/-- Driver's `p_*`, definitionally the manifold derivative of the same matrix representation at the
group identity. -/
def differential (data : SmoothUnitaryRepresentationDifferentialData (E := E) (G := G)) :
    GroupLieAlgebra (modelWithCornersSelf ℝ E) G →L[ℝ]
      (Fin data.dimension → Fin data.dimension → ℂ) :=
  mfderiv (modelWithCornersSelf ℝ E)
    (modelWithCornersSelf ℝ (Fin data.dimension → Fin data.dimension → ℂ))
    (fun g i j => data.representation g i j) (1 : G)

omit [FiniteDimensional ℝ E] [T2Space G] [SecondCountableTopology G]
    [LieGroup (modelWithCornersSelf ℝ E) ∞ G] in
/-- The stored source hypothesis is injectivity of this exact derivative. -/
theorem differential_injective_exact
    (data : SmoothUnitaryRepresentationDifferentialData (E := E) (G := G)) :
    Function.Injective data.differential :=
  data.differential_injective

omit [FiniteDimensional ℝ E] [T2Space G] [SecondCountableTopology G]
    [LieGroup (modelWithCornersSelf ℝ E) ∞ G] in
/-- Differentiated unitarity: the exact representation derivative is conjugate-transpose skew. -/
theorem representationDifferential_conjTranspose_eq_neg
    (data : SmoothUnitaryRepresentationDifferentialData (E := E) (G := G))
    (X : GroupLieAlgebra (modelWithCornersSelf ℝ E) G) :
    Matrix.conjTranspose (data.differential X) = -data.differential X := by
  let V := Fin data.dimension → Fin data.dimension → ℂ
  let ρ : G → V := fun g => data.representation g
  have hρmd : MDifferentiableAt (modelWithCornersSelf ℝ E)
      (modelWithCornersSelf ℝ V) ρ 1 := by
    exact data.representation_contMDiff.mdifferentiableAt (by simp)
  have hρ : HasMFDerivAt (modelWithCornersSelf ℝ E)
      (modelWithCornersSelf ℝ V) ρ 1 data.differential := by
    simpa [SmoothUnitaryRepresentationDifferentialData.differential, ρ, V] using
      hρmd.hasMFDerivAt
  let Slin : V →ₗ[ℝ] V :=
    { toFun := Matrix.conjTranspose
      map_add' := Matrix.conjTranspose_add
      map_smul' := by
        intro r M
        ext i j
        change star ((r : ℂ) * M j i) = (r : ℂ) * star (M j i)
        rw [star_mul]
        simp [mul_comm] }
  let S : V →L[ℝ] V := LinearMap.toContinuousLinearMap Slin
  have hS : HasMFDerivAt (modelWithCornersSelf ℝ V) (modelWithCornersSelf ℝ V)
      S (ρ 1) S := S.hasFDerivAt.hasMFDerivAt
  have hstar := hS.comp (1 : G) hρ
  let B : V →L[ℝ] V →L[ℝ] V := finiteMatrixMulContinuousBilinear data.dimension
  have hBf := B.hasFDerivAt_of_bilinear
    (hasFDerivAt_fst (𝕜 := ℝ) (p := (S (ρ 1), ρ 1)))
    (hasFDerivAt_snd (𝕜 := ℝ) (p := (S (ρ 1), ρ 1)))
  have hB := hBf.hasMFDerivAt
  have hpair := hstar.prodMk hρ
  have hprod := hB.comp (1 : G) hpair
  let I : V := fun i j => if i = j then 1 else 0
  have hfun : ((fun p : V × V => B p.1 p.2) ∘
      fun y : G => ((S ∘ ρ) y, ρ y)) = (fun _g : G => I) := by
    funext g
    ext i j
    change B (S (ρ g)) (ρ g) i j = I i j
    rw [finiteMatrixMulContinuousBilinear_apply]
    change (∑ k, (data.representation g).conjTranspose i k *
      data.representation g k j) = I i j
    have hu := data.representation_unitary g
    rw [Matrix.star_eq_conjTranspose] at hu
    simpa [I, Matrix.one_apply, Matrix.mul_apply, Matrix.conjTranspose_apply] using
      congrFun (congrFun hu i) j
  have hd := hprod.mfderiv
  rw [mfderiv_congr hfun, mfderiv_const] at hd
  have hx := congrArg (fun L => L X) hd
  ext i j
  have hxij := congrFun (congrFun hx i) j
  change 0 = (B (S (ρ 1)) (data.differential X) +
    B (S (data.differential X)) (ρ 1)) i j at hxij
  simp [ρ, V, S, Slin, B, finiteMatrixMulContinuousBilinear,
    finiteMatrixMulRealLinear, Matrix.one_apply] at hxij ⊢
  exact eq_neg_of_add_eq_zero_right hxij.symm

end SmoothUnitaryRepresentationDifferentialData

/-- Exact real trace pairing induced by the same representation differential. -/
def twoDimensionalRepresentationTracePairing
    (representation : SmoothUnitaryRepresentationDifferentialData (E := E) (G := G))
    (first second : GroupLieAlgebra (modelWithCornersSelf ℝ E) G) : ℝ :=
  -(Matrix.trace (finiteMatrixMulContinuousBilinear representation.dimension
    (representation.differential first) (representation.differential second))).re

omit [FiniteDimensional ℝ E] [T2Space G] [SecondCountableTopology G]
    [LieGroup (modelWithCornersSelf ℝ E) ∞ G] in
/-- The trace of the genuine matrix product of two exact differential values has zero imaginary
part, derived from differentiated unitarity and cyclicity of matrix trace. -/
theorem representationDifferential_trace_matrixMul_im
    (data : SmoothUnitaryRepresentationDifferentialData (E := E) (G := G))
    (X Y : GroupLieAlgebra (modelWithCornersSelf ℝ E) G) :
    (Matrix.trace (finiteMatrixMulContinuousBilinear data.dimension
      (data.differential X) (data.differential Y))).im = 0 := by
  let A : Matrix (Fin data.dimension) (Fin data.dimension) ℂ := data.differential X
  let C : Matrix (Fin data.dimension) (Fin data.dimension) ℂ := data.differential Y
  change (Matrix.trace (A * C)).im = 0
  apply Complex.conj_eq_iff_im.mp
  have hA : A.conjTranspose = -A :=
    data.representationDifferential_conjTranspose_eq_neg X
  have hC : C.conjTranspose = -C :=
    data.representationDifferential_conjTranspose_eq_neg Y
  calc
    (starRingEnd ℂ) (Matrix.trace (A * C)) =
        Matrix.trace ((A * C).conjTranspose) :=
      (Matrix.trace_conjTranspose (A * C)).symm
    _ = Matrix.trace (C.conjTranspose * A.conjTranspose) := by
      rw [Matrix.conjTranspose_mul]
    _ = Matrix.trace (C * A) := by rw [hA, hC]; simp
    _ = Matrix.trace (A * C) := Matrix.trace_mul_comm C A

omit [FiniteDimensional ℝ E] [T2Space G] [SecondCountableTopology G]
    [LieGroup (modelWithCornersSelf ℝ E) ∞ G] in
/-- Driver's real pairing is symmetric by cyclicity of the genuine matrix trace. -/
theorem twoDimensionalRepresentationTracePairing_symmetric
    (data : SmoothUnitaryRepresentationDifferentialData (E := E) (G := G))
    (X Y : GroupLieAlgebra (modelWithCornersSelf ℝ E) G) :
    twoDimensionalRepresentationTracePairing data X Y =
      twoDimensionalRepresentationTracePairing data Y X := by
  let A : Matrix (Fin data.dimension) (Fin data.dimension) ℂ := data.differential X
  let C : Matrix (Fin data.dimension) (Fin data.dimension) ℂ := data.differential Y
  change -(Matrix.trace (A * C)).re = -(Matrix.trace (C * A)).re
  rw [Matrix.trace_mul_comm A C]

omit [FiniteDimensional ℝ E] [T2Space G] [SecondCountableTopology G]
    [LieGroup (modelWithCornersSelf ℝ E) ∞ G] in
/-- Because the genuine trace product is real, the real-valued pairing recovers Driver's displayed
complex trace formula exactly. -/
theorem representationDifferential_trace_matrixMul_eq_neg_pairing
    (data : SmoothUnitaryRepresentationDifferentialData (E := E) (G := G))
    (X Y : GroupLieAlgebra (modelWithCornersSelf ℝ E) G) :
    Matrix.trace (finiteMatrixMulContinuousBilinear data.dimension
      (data.differential X) (data.differential Y)) =
      -(twoDimensionalRepresentationTracePairing data X Y : ℂ) := by
  apply Complex.ext
  · simp [twoDimensionalRepresentationTracePairing]
  · simp [representationDifferential_trace_matrixMul_im data X Y]

omit [FiniteDimensional ℝ E] [T2Space G] [SecondCountableTopology G]
    [LieGroup (modelWithCornersSelf ℝ E) ∞ G] in
/-- On one direction, Driver's negative trace pairing is the sum of the squared complex norms of all
matrix entries of the exact representation derivative. -/
theorem twoDimensionalRepresentationTracePairing_self_eq_sum_normSq
    (data : SmoothUnitaryRepresentationDifferentialData (E := E) (G := G))
    (X : GroupLieAlgebra (modelWithCornersSelf ℝ E) G) :
    twoDimensionalRepresentationTracePairing data X X =
      ∑ i, ∑ k, Complex.normSq (data.differential X k i) := by
  let A : Matrix (Fin data.dimension) (Fin data.dimension) ℂ := data.differential X
  have skew : A.conjTranspose = -A :=
    data.representationDifferential_conjTranspose_eq_neg X
  change -(Matrix.trace (A * A)).re = ∑ i, ∑ k, Complex.normSq (A k i)
  have complexEquality : -(Matrix.trace (A * A)) =
      Matrix.trace (A.conjTranspose * A) := by
    rw [skew]
    simp
  have realEquality := congrArg Complex.re complexEquality
  simpa [Matrix.trace, Matrix.mul_apply, Complex.normSq] using realEquality

omit [FiniteDimensional ℝ E] [T2Space G] [SecondCountableTopology G]
    [LieGroup (modelWithCornersSelf ℝ E) ∞ G] in
/-- Injectivity of Driver's exact `p_*` makes the genuine negative trace pairing strictly positive
on every nonzero Lie-algebra direction. -/
theorem twoDimensionalRepresentationTracePairing_self_pos
    (data : SmoothUnitaryRepresentationDifferentialData (E := E) (G := G))
    (X : GroupLieAlgebra (modelWithCornersSelf ℝ E) G) (nonzero : X ≠ 0) :
    0 < twoDimensionalRepresentationTracePairing data X X := by
  rw [twoDimensionalRepresentationTracePairing_self_eq_sum_normSq data X]
  have differential_nonzero : data.differential X ≠ 0 := by
    intro zero
    apply nonzero
    apply data.differential_injective_exact
    simpa using zero
  rw [Function.ne_iff] at differential_nonzero
  obtain ⟨row, row_nonzero⟩ := differential_nonzero
  rw [Function.ne_iff] at row_nonzero
  obtain ⟨column, entry_nonzero⟩ := row_nonzero
  apply Finset.sum_pos'
  · intro index _
    exact Finset.sum_nonneg fun innerIndex _ => Complex.normSq_nonneg _
  · exact ⟨column, Finset.mem_univ _, by
      apply Finset.sum_pos'
      · intro index _
        exact Complex.normSq_nonneg _
      · exact ⟨row, Finset.mem_univ _, Complex.normSq_pos.mpr entry_nonzero⟩⟩

/-- The continuum invariant inner product is exactly Driver's representation-induced trace pairing,
not an independently chosen normalization. -/
structure TwoDimensionalRepresentationInducedPairingCoherenceData
    (representation : SmoothUnitaryRepresentationDifferentialData (E := E) (G := G))
    (inner : Geometry.InvariantInnerProductData
      (I := modelWithCornersSelf ℝ E) (G := G)) : Prop where
  pairing_eq_trace : ∀ first second,
    inner.pairing first second =
      twoDimensionalRepresentationTracePairing representation first second

end

end YangMills.Dimensions
