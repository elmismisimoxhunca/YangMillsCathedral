/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Reconstruction.OSSourceOrderedWickContinuation

/-!
# Hostile probes for exact-source Wick continuation

These probes lock the derivative-vanishing source domain, same Euclidean/Wightman families, exact
smeared equality, backward-tube support, and one-way restriction to the old strict carrier. They do
not construct a continuation or reconstruction.
-/

namespace YangMills.Reconstruction.OSSourceOrderedWickContinuation.Probes

open YangMills
open YangMills.Minkowski
open MeasureTheory

variable
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
    (data : OSSourceOrderedScalarWickContinuationData euclidean minkowski)

/-- Every exact source test has the same analytic integrability obligation. -/
example (n : ℕ)
    (test : OSPositiveTimeOrderedFourDimensionalSourceSpace
      ⟨n + 1, Nat.zero_lt_succ n⟩) :
    Integrable (fun x : EuclideanNPointSpace EuclideanDimension.four (n + 1) =>
      (minkowski.analyticBoundary n).tubeFunction
          (reverseWickRotatedRelativeCoordinates EuclideanDimension.four n x) *
        test.toSchwartz x) :=
  data.ordered_integrable n test

/-- Coherence uses the exact Euclidean distribution and exact Wightman analytic boundary. -/
example (n : ℕ)
    (test : OSPositiveTimeOrderedFourDimensionalSourceSpace
      ⟨n + 1, Nat.zero_lt_succ n⟩) :
    euclidean.positivePoint ⟨n + 1, Nat.zero_lt_succ n⟩ test.toSchwartz =
      ∫ x : EuclideanNPointSpace EuclideanDimension.four (n + 1),
        (minkowski.analyticBoundary n).tubeFunction
            (reverseWickRotatedRelativeCoordinates EuclideanDimension.four n x) *
          test.toSchwartz x :=
  data.ordered_coherent n test

/-- Nonzero source support maps into the exact backward tube. -/
example (n : ℕ)
    (test : OSPositiveTimeOrderedFourDimensionalSourceSpace
      ⟨n + 1, Nat.zero_lt_succ n⟩)
    (x : EuclideanNPointSpace EuclideanDimension.four (n + 1))
    (nonzero : test.toSchwartz x ≠ 0) :
    reverseWickRotatedRelativeCoordinates EuclideanDimension.four n x ∈
      wightmanBackwardTube EuclideanDimension.four n :=
  osSourceOrderedTest_nonzero_maps_backwardTube test x nonzero

/-- The exact source bridge implies the old strict bridge, never conversely by declaration. -/
noncomputable example :
    MathlibStrictOrderedScalarWickContinuationData euclidean minkowski :=
  data.toMathlibStrict

/-- A strict test enters the source carrier without changing its Schwartz function. -/
example (n : ℕ)
    (test : MathlibPositiveTimeOrderedFlatTestFunction EuclideanDimension.four (n + 1)) :
    (strictOrderedFlatTestToOSSource test).toSchwartz = test.toSchwartz :=
  rfl

end YangMills.Reconstruction.OSSourceOrderedWickContinuation.Probes
