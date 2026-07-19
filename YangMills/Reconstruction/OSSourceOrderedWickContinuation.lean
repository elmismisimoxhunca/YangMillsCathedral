/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Euclidean.OSOrderedFourDimensionalSourceSpace
import YangMills.Reconstruction.StrictOrderedWickContinuation

/-!
# Wick continuation on the exact four-dimensional OS-I source carrier

OS-I printed p. 98 equations (5.1)–(5.2) identify Euclidean Green functions with Wightman analytic
functions at reverse-Wick-rotated relative coordinates. This module states the smeared equality for
every exact derivative-vanishing positive-time ordered source test, not only the earlier strict
support subspace.

Integrability for every possibly noncompact source Schwartz test remains an explicit strengthening
of the source's initial compact-support integral. This is a coherence requirement between supplied
Euclidean and Wightman data, not a reconstruction theorem or an existence construction.
-/

namespace YangMills.Reconstruction

open MeasureTheory
open Minkowski
open YangMills

/-- Include a strict ordered/flat test into the exact four-dimensional source carrier without
changing its underlying Schwartz function. -/
def strictOrderedFlatTestToOSSource
    {n : ℕ} (test : MathlibPositiveTimeOrderedFlatTestFunction
      EuclideanDimension.four (n + 1)) :
    OSPositiveTimeOrderedFourDimensionalSourceSpace
      ⟨n + 1, Nat.zero_lt_succ n⟩ := by
  let candidate := OSPositiveTimeOrderedDerivativeCarrier.ofStrictOrderedFlat test
  exact ⟨candidate.toSchwartz,
    (osPositiveTimeOrderedFourDimensionalSourceTest_iff_frechet
      ⟨n + 1, Nat.zero_lt_succ n⟩ candidate.toSchwartz).mpr candidate.2⟩

@[simp] theorem strictOrderedFlatTestToOSSource_toSchwartz
    {n : ℕ} (test : MathlibPositiveTimeOrderedFlatTestFunction
      EuclideanDimension.four (n + 1)) :
    (strictOrderedFlatTestToOSSource test).toSchwartz = test.toSchwartz :=
  rfl

/-- Exact source-carrier smeared Wick-continuation coherence in four dimensions. -/
structure OSSourceOrderedScalarWickContinuationData
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {lift : ProperOrthochronousPoincareLiftData EuclideanDimension.four G}
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H]
    {U : StronglyContinuousUnitaryPoincareRepresentation lift H}
    {vacuumData : PoincareInvariantVacuumData U}
    {D : CommonInvariantDomainData vacuumData}
    {fieldData : ScalarWightmanFieldOnCommonDomainData D}
    {full : ScalarWightmanJointTemperedCorrelatorData fieldData}
    (euclidean : ScalarSchwingerDistributionFamily EuclideanDimension.four)
    (minkowski : ScalarWightmanRelativeAnalyticCorrelatorData full) where
  /-- The same analytic integrand is integrable for every exact source test. -/
  ordered_integrable : ∀ (n : ℕ)
    (test : OSPositiveTimeOrderedFourDimensionalSourceSpace
      ⟨n + 1, Nat.zero_lt_succ n⟩),
    Integrable (fun x : EuclideanNPointSpace EuclideanDimension.four (n + 1) =>
      (minkowski.analyticBoundary n).tubeFunction
          (reverseWickRotatedRelativeCoordinates EuclideanDimension.four n x) *
        test.toSchwartz x)
  /-- Exact equality between the same Euclidean distribution and analytic Wightman boundary on
  every derivative-vanishing ordered source test. -/
  ordered_coherent : ∀ (n : ℕ)
    (test : OSPositiveTimeOrderedFourDimensionalSourceSpace
      ⟨n + 1, Nat.zero_lt_succ n⟩),
    euclidean.positivePoint ⟨n + 1, Nat.zero_lt_succ n⟩ test.toSchwartz =
      ∫ x : EuclideanNPointSpace EuclideanDimension.four (n + 1),
        (minkowski.analyticBoundary n).tubeFunction
            (reverseWickRotatedRelativeCoordinates EuclideanDimension.four n x) *
          test.toSchwartz x

/-- Source-carrier continuation restricts to the earlier strict-domain continuation without
changing the Euclidean test or analytic expression. -/
noncomputable def OSSourceOrderedScalarWickContinuationData.toMathlibStrict
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {lift : ProperOrthochronousPoincareLiftData EuclideanDimension.four G}
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H]
    {U : StronglyContinuousUnitaryPoincareRepresentation lift H}
    {vacuumData : PoincareInvariantVacuumData U}
    {D : CommonInvariantDomainData vacuumData}
    {fieldData : ScalarWightmanFieldOnCommonDomainData D}
    {full : ScalarWightmanJointTemperedCorrelatorData fieldData}
    {euclidean : ScalarSchwingerDistributionFamily EuclideanDimension.four}
    {minkowski : ScalarWightmanRelativeAnalyticCorrelatorData full}
    (data : OSSourceOrderedScalarWickContinuationData euclidean minkowski) :
    MathlibStrictOrderedScalarWickContinuationData euclidean minkowski where
  ordered_integrable := fun n test => by
    simpa only [strictOrderedFlatTestToOSSource_toSchwartz] using
      data.ordered_integrable n (strictOrderedFlatTestToOSSource test)
  ordered_coherent := fun n test => by
    simpa only [strictOrderedFlatTestToOSSource_toSchwartz] using
      data.ordered_coherent n (strictOrderedFlatTestToOSSource test)

/-- Every point where an exact source test is nonzero lies in strict positive time order. -/
theorem osSourceOrderedTest_mem_of_ne_zero
    {n : ℕ}
    (test : OSPositiveTimeOrderedFourDimensionalSourceSpace
      ⟨n + 1, Nat.zero_lt_succ n⟩)
    (x : EuclideanNPointSpace EuclideanDimension.four (n + 1))
    (nonzero : test.toSchwartz x ≠ 0) :
    x ∈ strictPositiveTimeOrderedConfigurationSet EuclideanDimension.four (n + 1) := by
  by_contra notOrdered
  have frechet :=
    (osPositiveTimeOrderedFourDimensionalSourceTest_iff_frechet
      ⟨n + 1, Nat.zero_lt_succ n⟩ test.toSchwartz).mp test.2
  have derivativeZero := frechet 0 x notOrdered
  have valueZero := congrArg
    (fun derivative => derivative (fun i : Fin 0 => Fin.elim0 i)) derivativeZero
  exact nonzero (by simpa using valueZero)

/-- Every nonzero point of an exact source test reverse-Wick-rotates into the backward tube. -/
theorem osSourceOrderedTest_nonzero_maps_backwardTube
    {n : ℕ}
    (test : OSPositiveTimeOrderedFourDimensionalSourceSpace
      ⟨n + 1, Nat.zero_lt_succ n⟩)
    (x : EuclideanNPointSpace EuclideanDimension.four (n + 1))
    (nonzero : test.toSchwartz x ≠ 0) :
    reverseWickRotatedRelativeCoordinates EuclideanDimension.four n x ∈
      wightmanBackwardTube EuclideanDimension.four n :=
  reverseWickRotatedRelativeCoordinates_mem_backwardTube EuclideanDimension.four n x
    (osSourceOrderedTest_mem_of_ne_zero test x nonzero)

/-- Outside the exact backward-tube preimage, every source-test continuation integrand vanishes. -/
theorem osSourceOrderedWickIntegrand_eq_zero_of_not_mem_backwardTube
    {n : ℕ}
    (test : OSPositiveTimeOrderedFourDimensionalSourceSpace
      ⟨n + 1, Nat.zero_lt_succ n⟩)
    (F : (Fin n → ComplexifiedSpacetime EuclideanDimension.four) → ℂ)
    (x : EuclideanNPointSpace EuclideanDimension.four (n + 1))
    (notTube : reverseWickRotatedRelativeCoordinates EuclideanDimension.four n x ∉
      wightmanBackwardTube EuclideanDimension.four n) :
    F (reverseWickRotatedRelativeCoordinates EuclideanDimension.four n x) *
        test.toSchwartz x = 0 := by
  have testZero : test.toSchwartz x = 0 := by
    by_contra nonzero
    exact notTube (osSourceOrderedTest_nonzero_maps_backwardTube test x nonzero)
  rw [testZero, mul_zero]

end YangMills.Reconstruction
