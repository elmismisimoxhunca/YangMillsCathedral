/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import Mathlib.Analysis.InnerProductSpace.CanonicalTensor
import Mathlib.LinearAlgebra.TensorProduct.Associator

/-!
# Basis-independent quadratic contraction of a bilinear map

This reusable mathematics module contracts both inputs of a bilinear map with the canonical
covariant tensor of a finite-dimensional real inner-product space, then contracts the two outputs
with an arbitrary bilinear scalar pairing. Expanding the canonical tensors in any orthonormal basis
produces the familiar double sum, so that sum is basis-independent.

The codomain pairing remains an explicit `LinearMap`; no inner-product or norm instance is required
on the codomain. This is important when several normalizations of the pairing must coexist.
-/

namespace YangMills.Mathematics

open scoped BigOperators TensorProduct

universe uE uW uι uκ

noncomputable section

variable
    {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    {W : Type uW} [AddCommGroup W] [Module ℝ W]
    {ι : Type uι} [Fintype ι]
    {κ : Type uκ} [Fintype κ]

/-- The canonical double metric contraction of a bilinear map against a bilinear scalar pairing.

The tensor commutation changes `(eᵢ ⊗ eᵢ) ⊗ (eⱼ ⊗ eⱼ)` into
`(eᵢ ⊗ eⱼ) ⊗ (eᵢ ⊗ eⱼ)` before applying the two copies of `f`. -/
def canonicalBilinearQuadraticContraction
    (pairing : W →ₗ[ℝ] W →ₗ[ℝ] ℝ)
    (bilinear : E →ₗ[ℝ] E →ₗ[ℝ] W) : ℝ :=
  TensorProduct.lift pairing
    (TensorProduct.map (TensorProduct.lift bilinear) (TensorProduct.lift bilinear)
      (TensorProduct.tensorTensorTensorComm ℝ E E E E
        (InnerProductSpace.canonicalCovariantTensor E ⊗ₜ[ℝ]
          InnerProductSpace.canonicalCovariantTensor E)))

/-- Every orthonormal basis computes the canonical double contraction as the corresponding double
sum. -/
theorem canonicalBilinearQuadraticContraction_eq_sum
    (pairing : W →ₗ[ℝ] W →ₗ[ℝ] ℝ)
    (bilinear : E →ₗ[ℝ] E →ₗ[ℝ] W)
    (basis : OrthonormalBasis ι ℝ E) :
    canonicalBilinearQuadraticContraction pairing bilinear =
      ∑ i, ∑ j,
        pairing (bilinear (basis i) (basis j)) (bilinear (basis i) (basis j)) := by
  rw [canonicalBilinearQuadraticContraction,
    InnerProductSpace.canonicalCovariantTensor_eq_sum E basis]
  simp only [TensorProduct.sum_tmul, TensorProduct.tmul_sum, map_sum,
    TensorProduct.tensorTensorTensorComm_tmul, TensorProduct.map_tmul,
    TensorProduct.lift.tmul]
  rw [Finset.sum_comm]

/-- Scaling the explicit codomain pairing scales the canonical contraction by the same scalar. -/
theorem canonicalBilinearQuadraticContraction_smul_pairing
    (scalar : ℝ)
    (pairing : W →ₗ[ℝ] W →ₗ[ℝ] ℝ)
    (bilinear : E →ₗ[ℝ] E →ₗ[ℝ] W) :
    canonicalBilinearQuadraticContraction (scalar • pairing) bilinear =
      scalar * canonicalBilinearQuadraticContraction pairing bilinear := by
  let basis := stdOrthonormalBasis ℝ E
  rw [canonicalBilinearQuadraticContraction_eq_sum (scalar • pairing) bilinear basis,
    canonicalBilinearQuadraticContraction_eq_sum pairing bilinear basis]
  simp only [LinearMap.smul_apply, smul_eq_mul, Finset.mul_sum]

/-- Double contraction sums computed in two orthonormal bases agree. -/
theorem orthonormalBilinearQuadraticContraction_independent
    (pairing : W →ₗ[ℝ] W →ₗ[ℝ] ℝ)
    (bilinear : E →ₗ[ℝ] E →ₗ[ℝ] W)
    (first : OrthonormalBasis ι ℝ E)
    (second : OrthonormalBasis κ ℝ E) :
    (∑ i, ∑ j,
      pairing (bilinear (first i) (first j)) (bilinear (first i) (first j))) =
    ∑ i, ∑ j,
      pairing (bilinear (second i) (second j)) (bilinear (second i) (second j)) := by
  rw [← canonicalBilinearQuadraticContraction_eq_sum pairing bilinear first,
    canonicalBilinearQuadraticContraction_eq_sum pairing bilinear second]

end

end YangMills.Mathematics
