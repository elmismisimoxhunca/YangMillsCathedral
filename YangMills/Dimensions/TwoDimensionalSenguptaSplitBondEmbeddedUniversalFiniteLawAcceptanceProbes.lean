/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Dimensions.TwoDimensionalSenguptaSplitBondEmbeddedUniversalFiniteLawAcceptance

/-! Hostile probes for split-bond embedded-universal finite-law acceptance. -/

namespace YangMills.Dimensions.TwoDimensionalSenguptaSplitBondEmbeddedUniversalFiniteLawAcceptance.Probes

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
    {CoverGroup : Type uCover} [Group CoverGroup] [TopologicalSpace CoverGroup]
    [IsTopologicalGroup CoverGroup] [CompactSpace CoverGroup] [T2Space CoverGroup]
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
    (data : TwoDimensionalSenguptaSplitBondEmbeddedUniversalFiniteLawAcceptanceData.{uG,
      uCover, uGauge, uSample, uConnection, uCurve, uEdge, uInternal, uFace, uRegion,
      uSenguptaSample, uSurface, uBaseVertex, uFineInternal, uFineFace, uFineVertex,
      uTargetEdge, uTargetInternal, uTargetFace, uTargetRegion, uTargetVertex,
      uTargetSurface, uCandidateFineEdge, uCandidateFineInternal, uCandidateFineFace,
      uCandidateFineVertex}
      (heatFactors := heatFactors) (Surface := Surface) (BaseVertex := BaseVertex)
      (FineVertex := FineVertex) (fine := fine) (TargetVertex := TargetVertex)
      (target := target) (TargetSurface := TargetSurface))

omit [T2Space CoverGroup] [Nonempty Curve] [Fintype TargetEdge]
    [MeasurableMul₂ CoverGroup] [MeasurableInv CoverGroup] in
/-- The split-bond universal record is indexed by the exact embedded base stored in the prior chain. -/
theorem exact_split_bond_dependency :
    TwoDimensionalSenguptaUniversalEmbeddedCurveBondSubdivisionData.{uG, uCover, uGauge,
      uSample, uConnection, uCurve, uEdge, uInternal, uFace, uRegion, uSenguptaSample,
      uSurface, uBaseVertex, uFineInternal, uFineFace, uFineVertex, uTargetEdge,
      uTargetInternal, uTargetFace, uTargetRegion, uTargetVertex, uCandidateFineEdge,
      uCandidateFineInternal, uCandidateFineFace, uCandidateFineVertex}
      (embeddedFiniteLaw := data.current.embeddedFiniteLaw) (coverDensity := coverDensity) :=
  data.exact_splitBondFactTwo

omit [T2Space CoverGroup] [Nonempty Curve] [Fintype TargetEdge]
    [MeasurableMul₂ CoverGroup] [MeasurableInv CoverGroup] in
include data in
/-- The prior curve-fixed/cellwise finite-law chain cannot be omitted. -/
theorem missing_current_blocked
    (missing : ¬ Nonempty (TwoDimensionalSenguptaEmbeddedUniversalFiniteLawAcceptanceData
      (heatFactors := heatFactors) (Surface := Surface) (BaseVertex := BaseVertex)
      (FineVertex := FineVertex) (fine := fine) (TargetVertex := TargetVertex)
      (target := target) (TargetSurface := TargetSurface))) : False :=
  missing ⟨data.current⟩

omit [T2Space CoverGroup] [Nonempty Curve] [Fintype TargetEdge]
    [MeasurableMul₂ CoverGroup] [MeasurableInv CoverGroup] in
include data in
/-- Universal split-bond certification cannot be omitted from the stronger wrapper. -/
theorem missing_split_bond_blocked
    (missing : ¬ Nonempty
      (TwoDimensionalSenguptaUniversalEmbeddedCurveBondSubdivisionData.{uG, uCover,
        uGauge, uSample, uConnection, uCurve, uEdge, uInternal, uFace, uRegion,
        uSenguptaSample, uSurface, uBaseVertex, uFineInternal, uFineFace, uFineVertex,
        uTargetEdge, uTargetInternal, uTargetFace, uTargetRegion, uTargetVertex,
        uCandidateFineEdge, uCandidateFineInternal, uCandidateFineFace,
        uCandidateFineVertex}
        (embeddedFiniteLaw := data.current.embeddedFiniteLaw)
        (coverDensity := coverDensity))) : False :=
  missing ⟨data.splitBondFactTwo⟩

end

end YangMills.Dimensions.TwoDimensionalSenguptaSplitBondEmbeddedUniversalFiniteLawAcceptance.Probes
