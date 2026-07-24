/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Dimensions.TwoDimensionalSenguptaEmbeddedUniversalFiniteLawAcceptance
import YangMills.Dimensions.TwoDimensionalSenguptaUniversalEmbeddedCurveBondSubdivision

/-!
# Split-bond embedded-universal Sengupta finite-law acceptance

This wrapper strengthens the prior embedded-universal finite-law record with universal certification
of the concrete embedded subdivision class that permits external curve bonds to split. Both layers
share the exact embedded base, finite law, covering density, and fixed bundle class.

It remains nonfinal and uninhabited. Fact 3 homeomorphisms requiring preliminary subdivisions,
unrestricted universe scope, heat-kernel integration, construction, and inhabitation remain open.
-/

namespace YangMills.Dimensions

open YangMills.Mathematics
open scoped ENNReal Manifold ContDiff

noncomputable section

universe uG uCover uGauge uSample uConnection uCurve uEdge uInternal uFace uRegion
  uSenguptaSample uSurface uBaseVertex uFineInternal uFineFace uFineVertex
  uTargetEdge uTargetInternal uTargetFace uTargetRegion uTargetVertex uTargetSurface
  uCandidateFineEdge uCandidateFineInternal uCandidateFineFace uCandidateFineVertex

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
    [MeasurableMul₂ CoverGroup] [MeasurableInv CoverGroup]
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

/-- Strongest current finite-law wrapper including universal embedded split-curve-bond Fact 2
candidates, while retaining the earlier curve-fixed and cellwise Fact 3 subclasses. -/
structure TwoDimensionalSenguptaSplitBondEmbeddedUniversalFiniteLawAcceptanceData where
  current : TwoDimensionalSenguptaEmbeddedUniversalFiniteLawAcceptanceData
    (heatFactors := heatFactors) (Surface := Surface) (BaseVertex := BaseVertex)
    (FineVertex := FineVertex) (fine := fine) (TargetVertex := TargetVertex)
    (target := target) (TargetSurface := TargetSurface)
  splitBondFactTwo :
    TwoDimensionalSenguptaUniversalEmbeddedCurveBondSubdivisionData.{uG, uCover, uGauge,
      uSample, uConnection, uCurve, uEdge, uInternal, uFace, uRegion, uSenguptaSample,
      uSurface, uBaseVertex, uFineInternal, uFineFace, uFineVertex, uTargetEdge,
      uTargetInternal, uTargetFace, uTargetRegion, uTargetVertex, uCandidateFineEdge,
      uCandidateFineInternal, uCandidateFineFace, uCandidateFineVertex}
      (embeddedFiniteLaw := current.embeddedFiniteLaw) (coverDensity := coverDensity)

namespace TwoDimensionalSenguptaSplitBondEmbeddedUniversalFiniteLawAcceptanceData

omit [T2Space CoverGroup] [Nonempty Curve] [Fintype TargetEdge]
    [MeasurableMul₂ CoverGroup] [MeasurableInv CoverGroup] in
/-- Exact inhabitance audit: this wrapper supplies neither its prior finite-law chain nor universal
split-bond certification. -/
theorem nonempty_iff_components :
    Nonempty
      (TwoDimensionalSenguptaSplitBondEmbeddedUniversalFiniteLawAcceptanceData.{uG, uCover,
        uGauge, uSample, uConnection, uCurve, uEdge, uInternal, uFace, uRegion,
        uSenguptaSample, uSurface, uBaseVertex, uFineInternal, uFineFace, uFineVertex,
        uTargetEdge, uTargetInternal, uTargetFace, uTargetRegion, uTargetVertex,
        uTargetSurface, uCandidateFineEdge, uCandidateFineInternal, uCandidateFineFace,
        uCandidateFineVertex}
        (heatFactors := heatFactors) (Surface := Surface) (BaseVertex := BaseVertex)
        (FineVertex := FineVertex) (fine := fine) (TargetVertex := TargetVertex)
        (target := target) (TargetSurface := TargetSurface)) ↔
    ∃ current : TwoDimensionalSenguptaEmbeddedUniversalFiniteLawAcceptanceData
        (heatFactors := heatFactors) (Surface := Surface) (BaseVertex := BaseVertex)
        (FineVertex := FineVertex) (fine := fine) (TargetVertex := TargetVertex)
        (target := target) (TargetSurface := TargetSurface),
      Nonempty
        (TwoDimensionalSenguptaUniversalEmbeddedCurveBondSubdivisionData.{uG, uCover,
          uGauge, uSample, uConnection, uCurve, uEdge, uInternal, uFace, uRegion,
          uSenguptaSample, uSurface, uBaseVertex, uFineInternal, uFineFace, uFineVertex,
          uTargetEdge, uTargetInternal, uTargetFace, uTargetRegion, uTargetVertex,
          uCandidateFineEdge, uCandidateFineInternal, uCandidateFineFace,
          uCandidateFineVertex}
          (embeddedFiniteLaw := current.embeddedFiniteLaw) (coverDensity := coverDensity)) := by
  constructor
  · rintro ⟨data⟩
    exact ⟨data.current, ⟨data.splitBondFactTwo⟩⟩
  · rintro ⟨current, ⟨splitBondFactTwo⟩⟩
    exact ⟨⟨current, splitBondFactTwo⟩⟩

omit [T2Space CoverGroup] [Nonempty Curve] [Fintype TargetEdge]
    [MeasurableMul₂ CoverGroup] [MeasurableInv CoverGroup] in
/-- Exact dependency projection for universal split-bond Fact 2 certification. -/
noncomputable def exact_splitBondFactTwo
    (data : TwoDimensionalSenguptaSplitBondEmbeddedUniversalFiniteLawAcceptanceData.{uG,
      uCover, uGauge, uSample, uConnection, uCurve, uEdge, uInternal, uFace, uRegion,
      uSenguptaSample, uSurface, uBaseVertex, uFineInternal, uFineFace, uFineVertex,
      uTargetEdge, uTargetInternal, uTargetFace, uTargetRegion, uTargetVertex,
      uTargetSurface, uCandidateFineEdge, uCandidateFineInternal, uCandidateFineFace,
      uCandidateFineVertex}
      (heatFactors := heatFactors) (Surface := Surface) (BaseVertex := BaseVertex)
      (FineVertex := FineVertex) (fine := fine) (TargetVertex := TargetVertex)
      (target := target) (TargetSurface := TargetSurface)) :
    TwoDimensionalSenguptaUniversalEmbeddedCurveBondSubdivisionData.{uG, uCover, uGauge,
      uSample, uConnection, uCurve, uEdge, uInternal, uFace, uRegion, uSenguptaSample,
      uSurface, uBaseVertex, uFineInternal, uFineFace, uFineVertex, uTargetEdge,
      uTargetInternal, uTargetFace, uTargetRegion, uTargetVertex, uCandidateFineEdge,
      uCandidateFineInternal, uCandidateFineFace, uCandidateFineVertex}
      (embeddedFiniteLaw := data.current.embeddedFiniteLaw) (coverDensity := coverDensity) :=
  data.splitBondFactTwo

end TwoDimensionalSenguptaSplitBondEmbeddedUniversalFiniteLawAcceptanceData

end

end YangMills.Dimensions
