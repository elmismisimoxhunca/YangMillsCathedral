/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Dimensions.TwoDimensionalSenguptaEmbeddedComparisonBridge
import YangMills.Dimensions.TwoDimensionalSenguptaUniversalCurveFixedEmbeddedSubdivision
import YangMills.Dimensions.TwoDimensionalSenguptaUniversalCellwiseEmbeddedHomeomorphism

/-!
# Embedded-universal current Sengupta finite-law acceptance

This record joins the exact embedded finite-law base, its selected geometric Facts 2--3 comparison,
universal acceptance over the curve-fixed Fact 2 subclass, and universal acceptance over the
directly cellwise-compatible Fact 3 subclass. All components use the same base triangulation,
covering density, fixed bundle class, and embedded presentation.

This is intentionally not the final two-dimensional proposition. Curve-bond subdivisions, Fact 3
homeomorphisms requiring preliminary subdivisions, construction, and inhabitance remain open.
-/

namespace YangMills.Dimensions

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
    {TargetEdge : Type uTargetEdge} [Fintype TargetEdge] [DecidableEq TargetEdge]
    {TargetInternal : Type uTargetInternal} [Fintype TargetInternal]
      [DecidableEq TargetInternal]
    {TargetFace : Type uTargetFace} [Fintype TargetFace] [DecidableEq TargetFace]
    {TargetRegion : Type uTargetRegion} [DecidableEq TargetRegion]
    {TargetVertex : Type uTargetVertex}
    {target : TwoDimensionalSenguptaTriangulatedRegionData
      TargetEdge TargetInternal TargetFace TargetRegion}
    {TargetSurface : Type uTargetSurface} [TopologicalSpace TargetSurface]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) TargetSurface]

/-- Strongest current source-indexed finite-law acceptance, still short of full Facts 2--3. -/
structure TwoDimensionalSenguptaEmbeddedUniversalFiniteLawAcceptanceData where
  embeddedFiniteLaw : TwoDimensionalSenguptaEmbeddedFiniteLawBridgeData
    (heatFactors := heatFactors) (Surface := Surface) (BaseVertex := BaseVertex)
    (FineVertex := FineVertex) (fine := fine)
    (TargetVertex := TargetVertex) (target := target)
  selectedComparison : TwoDimensionalSenguptaEmbeddedComparisonBridgeData
    (embeddedFiniteLaw := embeddedFiniteLaw) (TargetSurface := TargetSurface)
  curveFixedFactTwo :
    TwoDimensionalSenguptaUniversalCurveFixedEmbeddedSubdivisionData.{uCover, uCurve, uEdge,
      uInternal, uFace, uRegion, uSurface, uBaseVertex, uFineInternal, uFineFace, uFineVertex}
      (baseEmbedded := embeddedFiniteLaw.embeddedBase) (coverDensity := coverDensity)
      (bundleClass := finiteLaw.bundleClass)
  cellwiseFactThree :
    TwoDimensionalSenguptaUniversalCellwiseEmbeddedHomeomorphismData.{uCover, uCurve, uEdge,
      uInternal, uFace, uRegion, uSurface, uBaseVertex, uTargetEdge, uTargetInternal,
      uTargetFace, uTargetRegion, uTargetSurface, uTargetVertex}
      (baseEmbedded := embeddedFiniteLaw.embeddedBase) (coverDensity := coverDensity)
      (bundleClass := finiteLaw.bundleClass)

namespace TwoDimensionalSenguptaEmbeddedUniversalFiniteLawAcceptanceData

omit [T2Space CoverGroup] [Nonempty Curve] [Fintype TargetEdge] in
/-- Exact inhabitance audit: all stronger components must be supplied on one dependent embedded
finite-law witness; this wrapper synthesizes none of them. -/
theorem nonempty_iff_components :
    Nonempty (TwoDimensionalSenguptaEmbeddedUniversalFiniteLawAcceptanceData
      (heatFactors := heatFactors) (Surface := Surface) (BaseVertex := BaseVertex)
      (FineVertex := FineVertex) (fine := fine) (TargetVertex := TargetVertex)
      (target := target) (TargetSurface := TargetSurface)) ↔
    ∃ embeddedFiniteLaw : TwoDimensionalSenguptaEmbeddedFiniteLawBridgeData
        (heatFactors := heatFactors) (Surface := Surface) (BaseVertex := BaseVertex)
        (FineVertex := FineVertex) (fine := fine)
        (TargetVertex := TargetVertex) (target := target),
      Nonempty (TwoDimensionalSenguptaEmbeddedComparisonBridgeData
        (embeddedFiniteLaw := embeddedFiniteLaw) (TargetSurface := TargetSurface)) ∧
      Nonempty (TwoDimensionalSenguptaUniversalCurveFixedEmbeddedSubdivisionData.{uCover,
        uCurve, uEdge, uInternal, uFace, uRegion, uSurface, uBaseVertex, uFineInternal,
        uFineFace, uFineVertex} (baseEmbedded := embeddedFiniteLaw.embeddedBase)
        (coverDensity := coverDensity) (bundleClass := finiteLaw.bundleClass)) ∧
      Nonempty (TwoDimensionalSenguptaUniversalCellwiseEmbeddedHomeomorphismData.{uCover,
        uCurve, uEdge, uInternal, uFace, uRegion, uSurface, uBaseVertex, uTargetEdge,
        uTargetInternal, uTargetFace, uTargetRegion, uTargetSurface, uTargetVertex}
        (baseEmbedded := embeddedFiniteLaw.embeddedBase) (coverDensity := coverDensity)
        (bundleClass := finiteLaw.bundleClass)) := by
  constructor
  · rintro ⟨data⟩
    exact ⟨data.embeddedFiniteLaw, ⟨data.selectedComparison⟩,
      ⟨data.curveFixedFactTwo⟩, ⟨data.cellwiseFactThree⟩⟩
  · rintro ⟨embeddedFiniteLaw, ⟨selectedComparison⟩, ⟨curveFixedFactTwo⟩,
      ⟨cellwiseFactThree⟩⟩
    exact ⟨⟨embeddedFiniteLaw, selectedComparison, curveFixedFactTwo, cellwiseFactThree⟩⟩

/-- The universal subclass records are tied to this exact embedded finite-law base. -/
noncomputable def exact_curveFixedFactTwo
    (data : TwoDimensionalSenguptaEmbeddedUniversalFiniteLawAcceptanceData
      (heatFactors := heatFactors) (Surface := Surface) (BaseVertex := BaseVertex)
      (FineVertex := FineVertex) (fine := fine) (TargetVertex := TargetVertex)
      (target := target) (TargetSurface := TargetSurface)) :
    TwoDimensionalSenguptaUniversalCurveFixedEmbeddedSubdivisionData.{uCover, uCurve, uEdge,
      uInternal, uFace, uRegion, uSurface, uBaseVertex, uFineInternal, uFineFace, uFineVertex}
      (baseEmbedded := data.embeddedFiniteLaw.embeddedBase) (coverDensity := coverDensity)
      (bundleClass := finiteLaw.bundleClass) :=
  data.curveFixedFactTwo

/-- The cellwise Fact 3 record uses the same exact embedded finite-law base. -/
noncomputable def exact_cellwiseFactThree
    (data : TwoDimensionalSenguptaEmbeddedUniversalFiniteLawAcceptanceData
      (heatFactors := heatFactors) (Surface := Surface) (BaseVertex := BaseVertex)
      (FineVertex := FineVertex) (fine := fine) (TargetVertex := TargetVertex)
      (target := target) (TargetSurface := TargetSurface)) :
    TwoDimensionalSenguptaUniversalCellwiseEmbeddedHomeomorphismData.{uCover, uCurve, uEdge,
      uInternal, uFace, uRegion, uSurface, uBaseVertex, uTargetEdge, uTargetInternal,
      uTargetFace, uTargetRegion, uTargetSurface, uTargetVertex}
      (baseEmbedded := data.embeddedFiniteLaw.embeddedBase) (coverDensity := coverDensity)
      (bundleClass := finiteLaw.bundleClass) :=
  data.cellwiseFactThree

end TwoDimensionalSenguptaEmbeddedUniversalFiniteLawAcceptanceData

end

end YangMills.Dimensions
