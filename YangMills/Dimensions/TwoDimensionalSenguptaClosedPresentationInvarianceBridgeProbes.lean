/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Dimensions.TwoDimensionalSenguptaClosedPresentationInvarianceBridge

/-! Hostile probes for the closed-presentation invariance bridge. -/

namespace YangMills.Dimensions.TwoDimensionalSenguptaClosedPresentationInvarianceBridge.Probes

open YangMills.Mathematics
open scoped ENNReal

noncomputable section

universe uG uCover uGauge uSample uConnection uCurve uEdge uInternal uFace uRegion uSenguptaSample
  uBaseVertex uFineInternal uFineFace uFineVertex
  uTargetEdge uTargetInternal uTargetFace uTargetRegion uTargetVertex

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
    (data : TwoDimensionalSenguptaClosedPresentationInvarianceBridgeData
      (heatFactors := heatFactors) (BaseVertex := BaseVertex)
      (FineVertex := FineVertex) (fine := fine)
      (TargetVertex := TargetVertex) (target := target))

omit [T2Space CoverGroup] [Fintype Curve] [Nonempty Curve] [Fintype TargetEdge] in
include data in
/-- All three exact presentations have genuine two-dimensional face witnesses. -/
theorem exact_nonempty_presentations :
    Nonempty Face ∧ Nonempty FineFace ∧ Nonempty TargetFace :=
  ⟨data.baseClosed.face_nonempty, data.fineClosed.face_nonempty,
    data.targetClosed.face_nonempty⟩

omit [T2Space CoverGroup] [Fintype Curve] [Nonempty Curve] [Fintype TargetEdge] in
include data in
/-- The selected subdivision starts at the same closed base triangulation. -/
theorem exact_base_subdivision_factor (region : Region) (external : Edge → CoverGroup) :
    senguptaTriangulatedRegionFactor heatFactors.triangulation coverDensity region external =
      senguptaTriangulatedRegionFactor fine coverDensity region external :=
  data.invariance.subdivision.ordinaryFactor_eq region external

omit [T2Space CoverGroup] [Fintype Curve] [Nonempty Curve] [Fintype TargetEdge] in
/-- Missing closed incidence for the exact heat-factor base blocks the joined bridge. -/
theorem missing_base_closed_blocks
    (missing : TwoDimensionalSenguptaClosedTriangularPresentationData
      (Vertex := BaseVertex) heatFactors.triangulation → False) :
    TwoDimensionalSenguptaClosedPresentationInvarianceBridgeData
      (heatFactors := heatFactors) (BaseVertex := BaseVertex)
      (FineVertex := FineVertex) (fine := fine)
      (TargetVertex := TargetVertex) (target := target) → False :=
  fun bridge => missing bridge.baseClosed

omit [T2Space CoverGroup] [Fintype Curve] [Nonempty Curve] [Fintype TargetEdge] in
/-- Missing closed incidence for the fine presentation blocks the bridge. -/
theorem missing_fine_closed_blocks
    (missing : TwoDimensionalSenguptaClosedTriangularPresentationData
      (Vertex := FineVertex) fine → False) :
    TwoDimensionalSenguptaClosedPresentationInvarianceBridgeData
      (heatFactors := heatFactors) (BaseVertex := BaseVertex)
      (FineVertex := FineVertex) (fine := fine)
      (TargetVertex := TargetVertex) (target := target) → False :=
  fun bridge => missing bridge.fineClosed

omit [T2Space CoverGroup] [Fintype Curve] [Nonempty Curve] [Fintype TargetEdge] in
/-- Missing closed incidence for the transported presentation independently blocks the bridge. -/
theorem missing_target_closed_blocks
    (missing : TwoDimensionalSenguptaClosedTriangularPresentationData
      (Vertex := TargetVertex) target → False) :
    TwoDimensionalSenguptaClosedPresentationInvarianceBridgeData
      (heatFactors := heatFactors) (BaseVertex := BaseVertex)
      (FineVertex := FineVertex) (fine := fine)
      (TargetVertex := TargetVertex) (target := target) → False :=
  fun bridge => missing bridge.targetClosed

omit [T2Space CoverGroup] [Fintype Curve] [Nonempty Curve] [Fintype TargetEdge] in
/-- Closed presentations cannot substitute for the exact dependent invariance witness. -/
theorem missing_invariance_blocks
    (missing : TwoDimensionalSenguptaFactsTwoThreeBridgeData
      (heatFactors := heatFactors) (fine := fine) (target := target) → False) :
    TwoDimensionalSenguptaClosedPresentationInvarianceBridgeData
      (heatFactors := heatFactors) (BaseVertex := BaseVertex)
      (FineVertex := FineVertex) (fine := fine)
      (TargetVertex := TargetVertex) (target := target) → False :=
  fun bridge => missing bridge.invariance

end

end YangMills.Dimensions.TwoDimensionalSenguptaClosedPresentationInvarianceBridge.Probes
