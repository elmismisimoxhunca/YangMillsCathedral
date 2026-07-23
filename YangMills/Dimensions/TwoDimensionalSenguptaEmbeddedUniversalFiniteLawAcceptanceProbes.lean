/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Dimensions.TwoDimensionalSenguptaEmbeddedUniversalFiniteLawAcceptance

/-! Hostile dependency probes for embedded-universal current Sengupta finite-law acceptance. -/

namespace YangMills.Dimensions.TwoDimensionalSenguptaEmbeddedUniversalFiniteLawAcceptance.Probes

open YangMills.Mathematics
open scoped ENNReal Manifold ContDiff

noncomputable section

universe uG uCover uGauge uSample uConnection uCurve uEdge uInternal uFace uRegion uSenguptaSample
  uSurface uBaseVertex uFineInternal uFineFace uFineVertex
  uTargetEdge uTargetInternal uTargetFace uTargetRegion uTargetVertex uTargetSurface

variable
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    {Gauge : Type uGauge} [Group Gauge]
    {Sample : Type uSample} [MeasurableSpace Sample] {Connection : Type uConnection}
    {base : TwoDimensionalGaugeFixedHolonomyMeasureData G Gauge Sample Connection}
    {law : TwoDimensionalSelectedLoopHaarDensityLawData base}
    {planarSemigroup : TwoDimensionalSelectedLoopConvolutionSemigroupData law}
    {CoverGroup : Type uCover} [Group CoverGroup]
    [TopologicalSpace CoverGroup] [IsTopologicalGroup CoverGroup]
    [CompactSpace CoverGroup] [MeasurableSpace CoverGroup] [BorelSpace CoverGroup]
    {Curve : Type uCurve} [Fintype Curve]
    {Edge : Type uEdge} [Fintype Edge] [DecidableEq Edge]
    {InternalEdge : Type uInternal} [Fintype InternalEdge] [DecidableEq InternalEdge]
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
    {Surface : Type uSurface} [TopologicalSpace Surface]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) Surface]
    {BaseVertex : Type uBaseVertex}
    {FineInternal : Type uFineInternal} [Fintype FineInternal] [DecidableEq FineInternal]
    {FineFace : Type uFineFace} [Fintype FineFace] [DecidableEq FineFace]
    {FineVertex : Type uFineVertex}
    {fine : TwoDimensionalSenguptaTriangulatedRegionData Edge FineInternal FineFace Region}
    {TargetEdge : Type uTargetEdge} [DecidableEq TargetEdge]
    {TargetInternal : Type uTargetInternal} [Fintype TargetInternal]
      [DecidableEq TargetInternal]
    {TargetFace : Type uTargetFace} [Fintype TargetFace] [DecidableEq TargetFace]
    {TargetRegion : Type uTargetRegion} [DecidableEq TargetRegion]
    {TargetVertex : Type uTargetVertex}
    {target : TwoDimensionalSenguptaTriangulatedRegionData
      TargetEdge TargetInternal TargetFace TargetRegion}
    {TargetSurface : Type uTargetSurface} [TopologicalSpace TargetSurface]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) TargetSurface]
    (data : TwoDimensionalSenguptaEmbeddedUniversalFiniteLawAcceptanceData
      (heatFactors := heatFactors) (Surface := Surface) (BaseVertex := BaseVertex)
      (FineVertex := FineVertex) (fine := fine) (TargetVertex := TargetVertex)
      (target := target) (TargetSurface := TargetSurface))

/-- Both universal subclass records use the exact embedded finite-law base and fixed twist. -/
theorem exact_universal_subclasses :
    Nonempty (TwoDimensionalSenguptaUniversalCurveFixedEmbeddedSubdivisionData.{uCover,
      uCurve, uEdge, uInternal, uFace, uRegion, uSurface, uBaseVertex, uFineInternal,
      uFineFace, uFineVertex} (baseEmbedded := data.embeddedFiniteLaw.embeddedBase)
      (coverDensity := coverDensity) (bundleClass := finiteLaw.bundleClass)) ∧
    Nonempty (TwoDimensionalSenguptaUniversalCellwiseEmbeddedHomeomorphismData.{uCover,
      uCurve, uEdge, uInternal, uFace, uRegion, uSurface, uBaseVertex, uTargetEdge,
      uTargetInternal, uTargetFace, uTargetRegion, uTargetSurface, uTargetVertex}
      (baseEmbedded := data.embeddedFiniteLaw.embeddedBase) (coverDensity := coverDensity)
      (bundleClass := finiteLaw.bundleClass)) :=
  ⟨⟨data.curveFixedFactTwo⟩, ⟨data.cellwiseFactThree⟩⟩

/-- Missing either universal subclass independently blocks the joined acceptance. -/
theorem missing_curve_fixed_fact_two_blocks
    (missing : TwoDimensionalSenguptaUniversalCurveFixedEmbeddedSubdivisionData.{uCover,
      uCurve, uEdge, uInternal, uFace, uRegion, uSurface, uBaseVertex, uFineInternal,
      uFineFace, uFineVertex} (baseEmbedded := data.embeddedFiniteLaw.embeddedBase)
      (coverDensity := coverDensity) (bundleClass := finiteLaw.bundleClass) → False) : False :=
  missing data.curveFixedFactTwo

/-- A selected one-pair comparison cannot substitute for the universal cellwise Fact 3 subclass. -/
theorem missing_cellwise_fact_three_blocks
    (missing : TwoDimensionalSenguptaUniversalCellwiseEmbeddedHomeomorphismData.{uCover,
      uCurve, uEdge, uInternal, uFace, uRegion, uSurface, uBaseVertex, uTargetEdge,
      uTargetInternal, uTargetFace, uTargetRegion, uTargetSurface, uTargetVertex}
      (baseEmbedded := data.embeddedFiniteLaw.embeddedBase) (coverDensity := coverDensity)
      (bundleClass := finiteLaw.bundleClass) → False) : False :=
  missing data.cellwiseFactThree

end

end YangMills.Dimensions.TwoDimensionalSenguptaEmbeddedUniversalFiniteLawAcceptance.Probes
