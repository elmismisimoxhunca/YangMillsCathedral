/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Minkowski.WightmanExtendedTubeContinuation

/-!
# Hostile probes for scalar extended-tube continuation

The probes expose holomorphy, exact restriction, scalar complex-Lorentz invariance, orbit-source
independence, the value at an explicit point outside the ordinary tube, and rejection of a
disconnected extension value.
-/

namespace YangMills.Minkowski.WightmanExtendedTubeContinuation.Probes

/-- The continuation is holomorphic on the exact open extended domain. -/
theorem exact_extended_holomorphy
    {d : EuclideanDimension} {n : ℕ}
    {boundary : TemperedDistribution
      (Mathematics.FiniteConfiguration (Spacetime d) n) ℂ}
    {ordinary : PolynomiallyBoundedWightmanTubeBoundaryValueData d n boundary}
    (continuation : PolynomiallyBoundedWightmanExtendedTubeContinuationData d n ordinary) :
    DifferentiableOn ℂ continuation.extendedFunction (wightmanExtendedTube d n) :=
  continuation.holomorphic

/-- Restriction is exact and retains the same ordinary function carrying the tempered boundary. -/
theorem exact_ordinary_restriction
    {d : EuclideanDimension} {n : ℕ}
    {boundary : TemperedDistribution
      (Mathematics.FiniteConfiguration (Spacetime d) n) ℂ}
    {ordinary : PolynomiallyBoundedWightmanTubeBoundaryValueData d n boundary}
    (continuation : PolynomiallyBoundedWightmanExtendedTubeContinuationData d n ordinary)
    (z : Fin n → ComplexifiedSpacetime d) (hz : z ∈ wightmanBackwardTube d n) :
    continuation.extendedFunction z = ordinary.tubeFunction z :=
  continuation.restricts_to_ordinary z hz

/-- Scalar covariance is exact invariance under the same proper complex Lorentz action. -/
theorem exact_extended_invariance
    {d : EuclideanDimension} {n : ℕ}
    {boundary : TemperedDistribution
      (Mathematics.FiniteConfiguration (Spacetime d) n) ℂ}
    {ordinary : PolynomiallyBoundedWightmanTubeBoundaryValueData d n boundary}
    (continuation : PolynomiallyBoundedWightmanExtendedTubeContinuationData d n ordinary)
    (transformation : ProperComplexLorentzTransformation d)
    (z : Fin n → ComplexifiedSpacetime d) (hz : z ∈ wightmanExtendedTube d n) :
    continuation.extendedFunction
        (ProperComplexLorentzTransformation.actConfiguration transformation z) =
      continuation.extendedFunction z :=
  continuation.invariant transformation z hz

/-- Two orbit presentations of one point give exactly the same ordinary-tube value. -/
theorem exact_single_valued_orbit_coherence
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
    ordinary.tubeFunction firstSource = ordinary.tubeFunction secondSource :=
  continuation.orbitSource_independent firstTransformation secondTransformation
    firstSource secondSource first_mem second_mem samePoint

/-- The explicit four-dimensional point outside the original tube has its exact orbit-source value. -/
theorem exact_strict_witness_value
    {n : ℕ} (hn : 0 < n)
    {boundary : TemperedDistribution
      (Mathematics.FiniteConfiguration (Spacetime EuclideanDimension.four) n) ℂ}
    {ordinary : PolynomiallyBoundedWightmanTubeBoundaryValueData
      EuclideanDimension.four n boundary}
    (continuation : PolynomiallyBoundedWightmanExtendedTubeContinuationData
      EuclideanDimension.four n ordinary) :
    fourDimensionalExtendedTubeWitness n ∈
        wightmanExtendedTube EuclideanDimension.four n ∧
      fourDimensionalExtendedTubeWitness n ∉
        wightmanBackwardTube EuclideanDimension.four n ∧
      continuation.extendedFunction (fourDimensionalExtendedTubeWitness n) =
        ordinary.tubeFunction
          (standardWightmanBackwardTubePoint EuclideanDimension.four n) :=
  ⟨fourDimensionalExtendedTubeWitness_mem n,
    fourDimensionalExtendedTubeWitness_not_mem_backwardTube hn,
    continuation.fourDimensionalWitness_value⟩

/-- An unrelated value at a represented extended point cannot replace the connected continuation. -/
theorem disconnected_extended_value_blocked
    {d : EuclideanDimension} {n : ℕ}
    {boundary : TemperedDistribution
      (Mathematics.FiniteConfiguration (Spacetime d) n) ℂ}
    {ordinary : PolynomiallyBoundedWightmanTubeBoundaryValueData d n boundary}
    (continuation : PolynomiallyBoundedWightmanExtendedTubeContinuationData d n ordinary)
    (transformation : ProperComplexLorentzTransformation d)
    (source : Fin n → ComplexifiedSpacetime d)
    (source_mem : source ∈ wightmanBackwardTube d n)
    (replacement : ℂ) (mismatch : replacement ≠ ordinary.tubeFunction source) :
    replacement ≠ continuation.extendedFunction
      (ProperComplexLorentzTransformation.actConfiguration transformation source) := by
  rw [continuation.value_eq_orbitSource transformation source source_mem]
  exact mismatch

end YangMills.Minkowski.WightmanExtendedTubeContinuation.Probes
