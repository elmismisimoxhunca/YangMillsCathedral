/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Dimensions.TwoDimensionalSenguptaFactsTwoThreeBridge

/-! Hostile dependency probes for the Sengupta Facts 2--3 bridge. -/

namespace YangMills.Dimensions.TwoDimensionalSenguptaFactsTwoThreeBridge.Probes

open YangMills.Mathematics
open scoped ENNReal

noncomputable section

universe uG uCover uGauge uSample uConnection uCurve uEdge uInternal uFace uRegion uSenguptaSample
  uFineInternal uFineFace uTargetEdge uTargetInternal uTargetFace uTargetRegion

variable
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    {Gauge : Type uGauge} [Group Gauge]
    {Sample : Type uSample} [MeasurableSpace Sample]
    {Connection : Type uConnection}
    {base : TwoDimensionalGaugeFixedHolonomyMeasureData G Gauge Sample Connection}
    {law : TwoDimensionalSelectedLoopHaarDensityLawData base}
    {planarSemigroup : TwoDimensionalSelectedLoopConvolutionSemigroupData law}
    {CoverGroup : Type uCover} [Group CoverGroup]
    [TopologicalSpace CoverGroup] [IsTopologicalGroup CoverGroup]
    [CompactSpace CoverGroup] [T2Space CoverGroup]
    [MeasurableSpace CoverGroup] [BorelSpace CoverGroup]
    {Curve : Type uCurve} [Fintype Curve] [Nonempty Curve]
    {Edge : Type uEdge} [Fintype Edge] [DecidableEq Edge]
    {InternalEdge : Type uInternal} [Fintype InternalEdge]
    {Face : Type uFace} [Fintype Face] [DecidableEq Face]
    {Region : Type uRegion} [Fintype Region] [DecidableEq Region]
    {SenguptaSample : Type uSenguptaSample} [MeasurableSpace SenguptaSample]
    {finiteLaw : TwoDimensionalSenguptaCompactSurfaceFiniteHolonomyLawData
      (G := G) (CoverGroup := CoverGroup) (Curve := Curve) (Edge := Edge)
      (Region := Region) (Sample := SenguptaSample)}
    {coverDensity : ℝ → CoverGroup → ℝ≥0∞}
    {heatFactors : TwoDimensionalSenguptaTriangulatedHeatFactorBridgeData
      (planarSemigroup := planarSemigroup) (finiteLaw := finiteLaw)
      (coverDensity := coverDensity) (InternalEdge := InternalEdge) (Face := Face)}
    {FineInternal : Type uFineInternal} [Fintype FineInternal]
    {FineFace : Type uFineFace} [Fintype FineFace] [DecidableEq FineFace]
    {fine : TwoDimensionalSenguptaTriangulatedRegionData Edge FineInternal FineFace Region}
    {TargetEdge : Type uTargetEdge}
    {TargetInternal : Type uTargetInternal} [Fintype TargetInternal]
    {TargetFace : Type uTargetFace} [Fintype TargetFace] [DecidableEq TargetFace]
    {TargetRegion : Type uTargetRegion} [DecidableEq TargetRegion]
    {target : TwoDimensionalSenguptaTriangulatedRegionData
      TargetEdge TargetInternal TargetFace TargetRegion}
    (data : TwoDimensionalSenguptaFactsTwoThreeBridgeData
      (heatFactors := heatFactors) (fine := fine) (target := target))

omit [T2Space CoverGroup] [Fintype Curve] [Nonempty Curve] [DecidableEq Edge] in
include data in
/-- The subdivision equality begins at the exact triangulation realizing the finite-law weights. -/
theorem exact_base_subdivision_factor (region : Region) (external : Edge → CoverGroup) :
    senguptaTriangulatedRegionFactor heatFactors.triangulation coverDensity region external =
      senguptaTriangulatedRegionFactor fine coverDensity region external :=
  data.subdivision.ordinaryFactor_eq region external

omit [T2Space CoverGroup] [Fintype Curve] [Nonempty Curve] [DecidableEq Edge] in
/-- The homeomorphism equality begins at that same exact triangulation. -/
theorem exact_base_homeomorphism_factor (region : Region) (external : Edge → CoverGroup) :
    senguptaTriangulatedRegionFactor heatFactors.triangulation coverDensity region external =
      senguptaTriangulatedRegionFactor target coverDensity
        (data.homeomorphism.regionEquiv region)
        (senguptaTransportExternalField data.homeomorphism.externalEdgeEquiv external) :=
  data.homeomorphism.ordinaryFactor_eq region external

omit [T2Space CoverGroup] [Fintype Curve] [Nonempty Curve] [DecidableEq Edge] in
include data in
/-- The subdivision witness uses the finite law's fixed bundle class, not an arbitrary twist. -/
theorem exact_subdivision_fixed_twist (region : Region) (external : Edge → CoverGroup) :
    senguptaTriangulatedTwistedRegionFactor heatFactors.triangulation coverDensity
        finiteLaw.bundleClass region external =
      senguptaTriangulatedTwistedRegionFactor fine coverDensity
        finiteLaw.bundleClass region external :=
  data.subdivision.twistedFactor_eq region external

omit [T2Space CoverGroup] [Fintype Curve] [Nonempty Curve] [DecidableEq Edge] in
/-- The homeomorphism witness uses that same fixed twist and its source-specified sign transport. -/
theorem exact_homeomorphism_fixed_twist (region : Region) (external : Edge → CoverGroup) :
    senguptaTriangulatedTwistedRegionFactor heatFactors.triangulation coverDensity
        finiteLaw.bundleClass region external =
      senguptaTriangulatedTwistedRegionFactor target coverDensity
        (senguptaTransportedBundleClass data.homeomorphism.orientationSign
          finiteLaw.bundleClass)
        (data.homeomorphism.regionEquiv region)
        (senguptaTransportExternalField data.homeomorphism.externalEdgeEquiv external) :=
  data.homeomorphism.twistedFactor_eq region external

omit [T2Space CoverGroup] [Fintype Curve] [Nonempty Curve] [DecidableEq Edge] in
/-- A missing dependent subdivision witness blocks the joined bridge. -/
theorem missing_subdivision_blocks_bridge
    (missingSubdivision :
      TwoDimensionalSenguptaSubdivisionFactorInvarianceData
        (coverDensity := coverDensity) (coarse := heatFactors.triangulation) (fine := fine)
        (bundleClass := finiteLaw.bundleClass) → False) :
    TwoDimensionalSenguptaFactsTwoThreeBridgeData
      (heatFactors := heatFactors) (fine := fine) (target := target) → False :=
  fun bridge => missingSubdivision bridge.subdivision

omit [T2Space CoverGroup] [Fintype Curve] [Nonempty Curve] [DecidableEq Edge] in
/-- A missing dependent homeomorphism witness independently blocks the joined bridge. -/
theorem missing_homeomorphism_blocks_bridge
    (missingHomeomorphism :
      TwoDimensionalSenguptaHomeomorphismFactorInvarianceData
        (coverDensity := coverDensity) (source := heatFactors.triangulation) (target := target)
        (bundleClass := finiteLaw.bundleClass) → False) :
    TwoDimensionalSenguptaFactsTwoThreeBridgeData
      (heatFactors := heatFactors) (fine := fine) (target := target) → False :=
  fun bridge => missingHomeomorphism bridge.homeomorphism

end

end YangMills.Dimensions.TwoDimensionalSenguptaFactsTwoThreeBridge.Probes
