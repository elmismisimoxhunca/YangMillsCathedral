/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Dimensions.TwoDimensionalSenguptaSubdivisionFactorInvariance
import YangMills.Dimensions.TwoDimensionalSenguptaHomeomorphismFactorInvariance

/-!
# Fact 3 factor transport through preliminary subdivisions

Sengupta proves Fact 3 by first subdividing source and target until the homeomorphism is simplicial.
This file formalizes the algebraic factor composition: source subdivision invariance, one cellwise
homeomorphism factor equality, and target subdivision invariance imply the coarse source/target
ordinary and signed-twist equalities.

This does not construct the required subdivisions or cover curve-bond subdivision geometry.
-/

namespace YangMills.Dimensions

open YangMills.Mathematics
open scoped ENNReal

noncomputable section

universe uCover uSourceEdge uTargetEdge uSourceCoarseInternal uSourceCoarseFace
  uSourceFineInternal uSourceFineFace uTargetFineInternal uTargetFineFace
  uTargetCoarseInternal uTargetCoarseFace uSourceRegion uTargetRegion

variable
    {CoverGroup : Type uCover} [Group CoverGroup]
    [TopologicalSpace CoverGroup] [IsTopologicalGroup CoverGroup]
    [CompactSpace CoverGroup] [MeasurableSpace CoverGroup] [BorelSpace CoverGroup]
    {SourceEdge : Type uSourceEdge} {TargetEdge : Type uTargetEdge}
    {SourceCoarseInternal : Type uSourceCoarseInternal} [Fintype SourceCoarseInternal]
    {SourceCoarseFace : Type uSourceCoarseFace} [Fintype SourceCoarseFace]
      [DecidableEq SourceCoarseFace]
    {SourceFineInternal : Type uSourceFineInternal} [Fintype SourceFineInternal]
    {SourceFineFace : Type uSourceFineFace} [Fintype SourceFineFace]
      [DecidableEq SourceFineFace]
    {TargetFineInternal : Type uTargetFineInternal} [Fintype TargetFineInternal]
    {TargetFineFace : Type uTargetFineFace} [Fintype TargetFineFace]
      [DecidableEq TargetFineFace]
    {TargetCoarseInternal : Type uTargetCoarseInternal} [Fintype TargetCoarseInternal]
    {TargetCoarseFace : Type uTargetCoarseFace} [Fintype TargetCoarseFace]
      [DecidableEq TargetCoarseFace]
    {SourceRegion : Type uSourceRegion} [DecidableEq SourceRegion]
    {TargetRegion : Type uTargetRegion} [DecidableEq TargetRegion]
    {sourceCoarse : TwoDimensionalSenguptaTriangulatedRegionData
      SourceEdge SourceCoarseInternal SourceCoarseFace SourceRegion}
    {sourceFine : TwoDimensionalSenguptaTriangulatedRegionData
      SourceEdge SourceFineInternal SourceFineFace SourceRegion}
    {targetFine : TwoDimensionalSenguptaTriangulatedRegionData
      TargetEdge TargetFineInternal TargetFineFace TargetRegion}
    {targetCoarse : TwoDimensionalSenguptaTriangulatedRegionData
      TargetEdge TargetCoarseInternal TargetCoarseFace TargetRegion}
    {coverDensity : ℝ → CoverGroup → ℝ≥0∞}
    {bundleClass : CoverGroup}

/-- The exact three-step factor chain used in Sengupta's proof of Fact 3. -/
structure TwoDimensionalSenguptaPreliminarySubdivisionHomeomorphismFactorData where
  sourceSubdivision : TwoDimensionalSenguptaSubdivisionFactorInvarianceData
    (coverDensity := coverDensity) (coarse := sourceCoarse) (fine := sourceFine)
    (bundleClass := bundleClass)
  fineHomeomorphism : TwoDimensionalSenguptaHomeomorphismFactorInvarianceData
    (coverDensity := coverDensity) (source := sourceFine) (target := targetFine)
    (bundleClass := bundleClass)
  targetSubdivision : TwoDimensionalSenguptaSubdivisionFactorInvarianceData
    (coverDensity := coverDensity) (coarse := targetCoarse) (fine := targetFine)
    (bundleClass := senguptaTransportedBundleClass
      fineHomeomorphism.orientationSign bundleClass)

namespace TwoDimensionalSenguptaPreliminarySubdivisionHomeomorphismFactorData

/-- Coarse ordinary factors agree after the exact transported external field. -/
theorem ordinaryFactor_eq
    (data : TwoDimensionalSenguptaPreliminarySubdivisionHomeomorphismFactorData
      (coverDensity := coverDensity) (sourceCoarse := sourceCoarse) (sourceFine := sourceFine)
      (targetFine := targetFine) (targetCoarse := targetCoarse) (bundleClass := bundleClass))
    (region : SourceRegion) (external : SourceEdge → CoverGroup) :
    senguptaTriangulatedRegionFactor sourceCoarse coverDensity region external =
      senguptaTriangulatedRegionFactor targetCoarse coverDensity
        (data.fineHomeomorphism.regionEquiv region)
        (senguptaTransportExternalField data.fineHomeomorphism.externalEdgeEquiv external) := by
  rw [data.sourceSubdivision.ordinaryFactor_eq region external]
  rw [data.fineHomeomorphism.ordinaryFactor_eq region external]
  rw [data.targetSubdivision.ordinaryFactor_eq]

/-- Coarse twisted factors agree with exactly the Fact 3 `h`/`h⁻¹` transport. -/
theorem twistedFactor_eq
    (data : TwoDimensionalSenguptaPreliminarySubdivisionHomeomorphismFactorData
      (coverDensity := coverDensity) (sourceCoarse := sourceCoarse) (sourceFine := sourceFine)
      (targetFine := targetFine) (targetCoarse := targetCoarse) (bundleClass := bundleClass))
    (region : SourceRegion) (external : SourceEdge → CoverGroup) :
    senguptaTriangulatedTwistedRegionFactor sourceCoarse coverDensity bundleClass region external =
      senguptaTriangulatedTwistedRegionFactor targetCoarse coverDensity
        (senguptaTransportedBundleClass data.fineHomeomorphism.orientationSign bundleClass)
        (data.fineHomeomorphism.regionEquiv region)
        (senguptaTransportExternalField data.fineHomeomorphism.externalEdgeEquiv external) := by
  rw [data.sourceSubdivision.twistedFactor_eq region external]
  rw [data.fineHomeomorphism.twistedFactor_eq region external]
  rw [data.targetSubdivision.twistedFactor_eq]

end TwoDimensionalSenguptaPreliminarySubdivisionHomeomorphismFactorData

end

end YangMills.Dimensions
