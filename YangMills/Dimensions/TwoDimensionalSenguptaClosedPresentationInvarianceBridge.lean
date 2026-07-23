/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Dimensions.TwoDimensionalSenguptaClosedTriangularPresentation
import YangMills.Dimensions.TwoDimensionalSenguptaFactsTwoThreeBridge

/-!
# Closed-presentation bridge for Sengupta finite invariance

This record dependently requires closed triangular incidence data for the exact heat-factor
presentation, its selected Fact 2 refinement, and its selected Fact 3 transported presentation. The
same three candidates are used by the Facts 2--3 dependency bridge; no unrelated closed presentation
can discharge the requirement.

It remains finite and combinatorial: embedded compact-surface realizations and universal source-valid
subdivision/homeomorphism quantification are not constructed.
-/

namespace YangMills.Dimensions

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

/-- Closed triangular incidence and one-pair invariance tied to one exact finite-law factor chain. -/
structure TwoDimensionalSenguptaClosedPresentationInvarianceBridgeData where
  baseClosed : TwoDimensionalSenguptaClosedTriangularPresentationData
    (Vertex := BaseVertex) heatFactors.triangulation
  fineClosed : TwoDimensionalSenguptaClosedTriangularPresentationData
    (Vertex := FineVertex) fine
  targetClosed : TwoDimensionalSenguptaClosedTriangularPresentationData
    (Vertex := TargetVertex) target
  invariance : TwoDimensionalSenguptaFactsTwoThreeBridgeData
    (heatFactors := heatFactors) (fine := fine) (target := target)

namespace TwoDimensionalSenguptaClosedPresentationInvarianceBridgeData

omit [T2Space CoverGroup] [Fintype Curve] [Nonempty Curve] [Fintype TargetEdge] in
/-- Exact inhabitance audit: all three closed presentations and their dependent invariance bridge
must be supplied; the wrapper synthesizes none of them. -/
theorem nonempty_iff_components :
    Nonempty (TwoDimensionalSenguptaClosedPresentationInvarianceBridgeData
      (heatFactors := heatFactors) (BaseVertex := BaseVertex)
      (FineVertex := FineVertex) (fine := fine)
      (TargetVertex := TargetVertex) (target := target)) ↔
    Nonempty (TwoDimensionalSenguptaClosedTriangularPresentationData
      (Vertex := BaseVertex) heatFactors.triangulation) ∧
    Nonempty (TwoDimensionalSenguptaClosedTriangularPresentationData
      (Vertex := FineVertex) fine) ∧
    Nonempty (TwoDimensionalSenguptaClosedTriangularPresentationData
      (Vertex := TargetVertex) target) ∧
    Nonempty (TwoDimensionalSenguptaFactsTwoThreeBridgeData
      (heatFactors := heatFactors) (fine := fine) (target := target)) := by
  constructor
  · rintro ⟨data⟩
    exact ⟨⟨data.baseClosed⟩, ⟨data.fineClosed⟩, ⟨data.targetClosed⟩, ⟨data.invariance⟩⟩
  · rintro ⟨⟨baseClosed⟩, ⟨fineClosed⟩, ⟨targetClosed⟩, ⟨invariance⟩⟩
    exact ⟨⟨baseClosed, fineClosed, targetClosed, invariance⟩⟩

/-- The closed base presentation is indexed by the exact finite-law factor triangulation. -/
noncomputable def exact_baseClosed
    (data : TwoDimensionalSenguptaClosedPresentationInvarianceBridgeData
      (heatFactors := heatFactors) (BaseVertex := BaseVertex)
      (FineVertex := FineVertex) (fine := fine)
      (TargetVertex := TargetVertex) (target := target)) :
    TwoDimensionalSenguptaClosedTriangularPresentationData
      (Vertex := BaseVertex) heatFactors.triangulation :=
  data.baseClosed

/-- The same exact fine and target presentations occur in the invariance witness. -/
noncomputable def exact_invariance
    (data : TwoDimensionalSenguptaClosedPresentationInvarianceBridgeData
      (heatFactors := heatFactors) (BaseVertex := BaseVertex)
      (FineVertex := FineVertex) (fine := fine)
      (TargetVertex := TargetVertex) (target := target)) :
    TwoDimensionalSenguptaFactsTwoThreeBridgeData
      (heatFactors := heatFactors) (fine := fine) (target := target) :=
  data.invariance

end TwoDimensionalSenguptaClosedPresentationInvarianceBridgeData

end

end YangMills.Dimensions
