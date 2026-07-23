/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Dimensions.TwoDimensionalSenguptaPreliminarySubdivisionHomeomorphismFactors

/-! Hostile probes for Fact 3 transport through preliminary subdivisions. -/

namespace YangMills.Dimensions.TwoDimensionalSenguptaPreliminarySubdivisionHomeomorphismFactors.Probes

open YangMills.Mathematics
open scoped ENNReal

noncomputable section

variable
    {CoverGroup : Type*} [Group CoverGroup]
    [TopologicalSpace CoverGroup] [IsTopologicalGroup CoverGroup]
    [CompactSpace CoverGroup] [MeasurableSpace CoverGroup] [BorelSpace CoverGroup]
    {SourceEdge TargetEdge SourceCoarseInternal SourceCoarseFace SourceFineInternal
      SourceFineFace TargetFineInternal TargetFineFace TargetCoarseInternal TargetCoarseFace
      SourceRegion TargetRegion : Type*}
    [Fintype SourceCoarseInternal] [Fintype SourceCoarseFace] [DecidableEq SourceCoarseFace]
    [Fintype SourceFineInternal] [Fintype SourceFineFace] [DecidableEq SourceFineFace]
    [Fintype TargetFineInternal] [Fintype TargetFineFace] [DecidableEq TargetFineFace]
    [Fintype TargetCoarseInternal] [Fintype TargetCoarseFace] [DecidableEq TargetCoarseFace]
    [DecidableEq SourceRegion] [DecidableEq TargetRegion]
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
    (data : TwoDimensionalSenguptaPreliminarySubdivisionHomeomorphismFactorData
      (coverDensity := coverDensity) (sourceCoarse := sourceCoarse) (sourceFine := sourceFine)
      (targetFine := targetFine) (targetCoarse := targetCoarse) (bundleClass := bundleClass))

/-- The target subdivision uses exactly the globally transported twist. -/
theorem exact_target_twist (region : TargetRegion) (external : TargetEdge → CoverGroup) :
    senguptaTriangulatedTwistedRegionFactor targetCoarse coverDensity
        (senguptaTransportedBundleClass data.fineHomeomorphism.orientationSign bundleClass)
        region external =
      senguptaTriangulatedTwistedRegionFactor targetFine coverDensity
        (senguptaTransportedBundleClass data.fineHomeomorphism.orientationSign bundleClass)
        region external :=
  data.targetSubdivision.twistedFactor_eq region external

/-- Hostile transitive ordinary-factor probe. -/
theorem changed_composed_ordinary_factor_blocked
    (region : SourceRegion) (external : SourceEdge → CoverGroup)
    (changed : senguptaTriangulatedRegionFactor sourceCoarse coverDensity region external ≠
      senguptaTriangulatedRegionFactor targetCoarse coverDensity
        (data.fineHomeomorphism.regionEquiv region)
        (senguptaTransportExternalField data.fineHomeomorphism.externalEdgeEquiv external)) : False :=
  changed (data.ordinaryFactor_eq region external)

/-- Hostile transitive signed-twist probe. -/
theorem changed_composed_twisted_factor_blocked
    (region : SourceRegion) (external : SourceEdge → CoverGroup)
    (changed : senguptaTriangulatedTwistedRegionFactor sourceCoarse coverDensity
        bundleClass region external ≠
      senguptaTriangulatedTwistedRegionFactor targetCoarse coverDensity
        (senguptaTransportedBundleClass data.fineHomeomorphism.orientationSign bundleClass)
        (data.fineHomeomorphism.regionEquiv region)
        (senguptaTransportExternalField data.fineHomeomorphism.externalEdgeEquiv external)) : False :=
  changed (data.twistedFactor_eq region external)

include data in
/-- Missing the source subdivision blocks the three-step source proof pattern. -/
theorem missing_source_subdivision_blocks
    (missing : TwoDimensionalSenguptaSubdivisionFactorInvarianceData
      (coverDensity := coverDensity) (coarse := sourceCoarse) (fine := sourceFine)
      (bundleClass := bundleClass) → False) : False :=
  missing data.sourceSubdivision

include data in
/-- Missing the target subdivision independently blocks the composition. -/
theorem missing_target_subdivision_blocks
    (missing : TwoDimensionalSenguptaSubdivisionFactorInvarianceData
      (coverDensity := coverDensity) (coarse := targetCoarse) (fine := targetFine)
      (bundleClass := senguptaTransportedBundleClass
        data.fineHomeomorphism.orientationSign bundleClass) → False) : False :=
  missing data.targetSubdivision

include data in
/-- Missing the fine cellwise homeomorphism independently blocks the composition. -/
theorem missing_fine_homeomorphism_blocks
    (missing : TwoDimensionalSenguptaHomeomorphismFactorInvarianceData
      (coverDensity := coverDensity) (source := sourceFine) (target := targetFine)
      (bundleClass := bundleClass) → False) : False :=
  missing data.fineHomeomorphism

end

end YangMills.Dimensions.TwoDimensionalSenguptaPreliminarySubdivisionHomeomorphismFactors.Probes
