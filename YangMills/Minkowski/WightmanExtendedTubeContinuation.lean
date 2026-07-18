/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Minkowski.WightmanExtendedTubeGeometry
import YangMills.Minkowski.WightmanTubePolynomialGrowth

/-!
# Scalar Wightman continuation to the extended tube

Streater–Wightman Theorem 2-11 states that a tube-holomorphic covariant function has a single-valued
holomorphic continuation to the proper-complex-Lorentz extended tube. For the project's scalar
Wightman surface, the representation factor is trivial, so the continuation is invariant.

This module packages the theorem's conclusion as uninhabited acceptance data connected to the exact
polynomially bounded ordinary-tube function and its tempered boundary. It does not prove the
analytic-continuation theorem, construct the transformation-group analytic structure, or construct a
correlator or theory.
-/

namespace YangMills.Minkowski

/-- Single-valued scalar holomorphic extension of one exact polynomially bounded tube-boundary
function to the exact proper-complex-Lorentz orbit. -/
structure PolynomiallyBoundedWightmanExtendedTubeContinuationData
    (d : EuclideanDimension) (n : ℕ)
    {boundary : TemperedDistribution
      (Mathematics.FiniteConfiguration (Spacetime d) n) ℂ}
    (ordinary : PolynomiallyBoundedWightmanTubeBoundaryValueData d n boundary) where
  /-- One ambient function; single-valuedness is represented by ordinary function semantics. -/
  extendedFunction : (Fin n → ComplexifiedSpacetime d) → ℂ
  /-- Genuine holomorphy on the exact open extended tube. -/
  holomorphic : DifferentiableOn ℂ extendedFunction (wightmanExtendedTube d n)
  /-- The continuation is exactly the existing ordinary-tube function on the original domain. -/
  restricts_to_ordinary : ∀ z ∈ wightmanBackwardTube d n,
    extendedFunction z = ordinary.tubeFunction z
  /-- Scalar proper-complex-Lorentz invariance on the exact extended domain. -/
  invariant : ∀ (transformation : ProperComplexLorentzTransformation d)
    (z : Fin n → ComplexifiedSpacetime d),
    z ∈ wightmanExtendedTube d n →
      extendedFunction
          (ProperComplexLorentzTransformation.actConfiguration transformation z) =
        extendedFunction z

/-- Every extended-tube value is forced to equal the original tube function at any supplied orbit
source, blocking a disconnected ambient extension. -/
theorem PolynomiallyBoundedWightmanExtendedTubeContinuationData.value_eq_orbitSource
    {d : EuclideanDimension} {n : ℕ}
    {boundary : TemperedDistribution
      (Mathematics.FiniteConfiguration (Spacetime d) n) ℂ}
    {ordinary : PolynomiallyBoundedWightmanTubeBoundaryValueData d n boundary}
    (continuation : PolynomiallyBoundedWightmanExtendedTubeContinuationData d n ordinary)
    (transformation : ProperComplexLorentzTransformation d)
    (source : Fin n → ComplexifiedSpacetime d)
    (source_mem : source ∈ wightmanBackwardTube d n) :
    continuation.extendedFunction
        (ProperComplexLorentzTransformation.actConfiguration transformation source) =
      ordinary.tubeFunction source := by
  calc
    continuation.extendedFunction
        (ProperComplexLorentzTransformation.actConfiguration transformation source) =
      continuation.extendedFunction source :=
        continuation.invariant transformation source
          (wightmanBackwardTube_subset_extendedTube d n source_mem)
    _ = ordinary.tubeFunction source :=
      continuation.restricts_to_ordinary source source_mem

/-- Any two ordinary-tube presentations of one extended point yield the same original tube value,
which is the explicit single-valuedness coherence required by the orbit construction. -/
theorem PolynomiallyBoundedWightmanExtendedTubeContinuationData.orbitSource_independent
    {d : EuclideanDimension} {n : ℕ}
    {boundary : TemperedDistribution
      (Mathematics.FiniteConfiguration (Spacetime d) n) ℂ}
    {ordinary : PolynomiallyBoundedWightmanTubeBoundaryValueData d n boundary}
    (continuation : PolynomiallyBoundedWightmanExtendedTubeContinuationData d n ordinary)
    (firstTransformation secondTransformation : ProperComplexLorentzTransformation d)
    (firstSource secondSource : Fin n → ComplexifiedSpacetime d)
    (first_mem : firstSource ∈ wightmanBackwardTube d n)
    (second_mem : secondSource ∈ wightmanBackwardTube d n)
    (samePoint :
      ProperComplexLorentzTransformation.actConfiguration firstTransformation firstSource =
        ProperComplexLorentzTransformation.actConfiguration secondTransformation secondSource) :
    ordinary.tubeFunction firstSource = ordinary.tubeFunction secondSource := by
  rw [← continuation.value_eq_orbitSource firstTransformation firstSource first_mem,
    ← continuation.value_eq_orbitSource secondTransformation secondSource second_mem,
    samePoint]

/-- The explicit four-dimensional point outside the ordinary tube receives the value of the exact
standard ordinary-tube source rather than an unrelated extension value. -/
theorem PolynomiallyBoundedWightmanExtendedTubeContinuationData.fourDimensionalWitness_value
    {n : ℕ}
    {boundary : TemperedDistribution
      (Mathematics.FiniteConfiguration (Spacetime EuclideanDimension.four) n) ℂ}
    {ordinary : PolynomiallyBoundedWightmanTubeBoundaryValueData
      EuclideanDimension.four n boundary}
    (continuation : PolynomiallyBoundedWightmanExtendedTubeContinuationData
      EuclideanDimension.four n ordinary) :
    continuation.extendedFunction (fourDimensionalExtendedTubeWitness n) =
      ordinary.tubeFunction
        (standardWightmanBackwardTubePoint EuclideanDimension.four n) :=
  continuation.value_eq_orbitSource
    ProperComplexLorentzTransformation.fourDimensionalComplexNegation
    (standardWightmanBackwardTubePoint EuclideanDimension.four n)
    (standardWightmanBackwardTubePoint_mem EuclideanDimension.four n)

end YangMills.Minkowski
