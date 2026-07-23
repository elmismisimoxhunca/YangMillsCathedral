/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Dimensions.TwoDimensionalSenguptaSubdivisionFactorInvariance
import YangMills.Dimensions.TwoDimensionalSenguptaHomeomorphismFactorInvariance

/-!
# Exact dependency bridge for Sengupta Facts 2 and 3

This file prevents one-pair Fact 2 and Fact 3 witnesses from floating independently of the exact
finite-law heat-factor chain. Both certificates start at the triangulation stored by one
`TwoDimensionalSenguptaTriangulatedHeatFactorBridgeData`, use its unchanged covering density, and use
its finite law's distinguished central bundle class.

The record still assumes the two one-pair certificates. It neither constructs the fine or transported
presentations nor upgrades them to universal subdivision/homeomorphism invariance.
-/

namespace YangMills.Dimensions

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

/-- Facts 2 and 3 witnesses dependently tied to one exact finite-law heat-factor bridge. -/
structure TwoDimensionalSenguptaFactsTwoThreeBridgeData where
  subdivision : TwoDimensionalSenguptaSubdivisionFactorInvarianceData
    (coverDensity := coverDensity) (coarse := heatFactors.triangulation) (fine := fine)
    (bundleClass := finiteLaw.bundleClass)
  homeomorphism : TwoDimensionalSenguptaHomeomorphismFactorInvarianceData
    (coverDensity := coverDensity) (source := heatFactors.triangulation) (target := target)
    (bundleClass := finiteLaw.bundleClass)

namespace TwoDimensionalSenguptaFactsTwoThreeBridgeData

omit [T2Space CoverGroup] [Fintype Curve] [Nonempty Curve] [DecidableEq Edge] in
/-- Exact logical audit: the joined bridge contains no synthesis beyond the two dependently indexed
one-pair certificates. -/
theorem nonempty_iff_components :
    Nonempty (TwoDimensionalSenguptaFactsTwoThreeBridgeData
      (heatFactors := heatFactors) (fine := fine) (target := target)) ↔
      Nonempty (TwoDimensionalSenguptaSubdivisionFactorInvarianceData
        (coverDensity := coverDensity) (coarse := heatFactors.triangulation) (fine := fine)
        (bundleClass := finiteLaw.bundleClass)) ∧
      Nonempty (TwoDimensionalSenguptaHomeomorphismFactorInvarianceData
        (coverDensity := coverDensity) (source := heatFactors.triangulation) (target := target)
        (bundleClass := finiteLaw.bundleClass)) := by
  constructor
  · rintro ⟨data⟩
    exact ⟨⟨data.subdivision⟩, ⟨data.homeomorphism⟩⟩
  · rintro ⟨⟨subdivision⟩, ⟨homeomorphism⟩⟩
    exact ⟨⟨subdivision, homeomorphism⟩⟩

/-- The Fact 2 witness starts at the exact triangulation used to realize the finite-law weights. -/
noncomputable def exact_subdivision
    (data : TwoDimensionalSenguptaFactsTwoThreeBridgeData
      (heatFactors := heatFactors) (fine := fine) (target := target)) :
    TwoDimensionalSenguptaSubdivisionFactorInvarianceData
      (coverDensity := coverDensity) (coarse := heatFactors.triangulation) (fine := fine)
      (bundleClass := finiteLaw.bundleClass) :=
  data.subdivision

/-- The Fact 3 witness starts at the same exact triangulation and fixed bundle class. -/
noncomputable def exact_homeomorphism
    (data : TwoDimensionalSenguptaFactsTwoThreeBridgeData
      (heatFactors := heatFactors) (fine := fine) (target := target)) :
    TwoDimensionalSenguptaHomeomorphismFactorInvarianceData
      (coverDensity := coverDensity) (source := heatFactors.triangulation) (target := target)
      (bundleClass := finiteLaw.bundleClass) :=
  data.homeomorphism

end TwoDimensionalSenguptaFactsTwoThreeBridgeData

end

end YangMills.Dimensions
