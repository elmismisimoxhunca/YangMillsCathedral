/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Dimensions.TwoDimensionalSenguptaClosedPresentationInvarianceBridge
import YangMills.Dimensions.TwoDimensionalSenguptaEmbeddedTriangularPresentation

/-!
# Embedded Sengupta presentation tied to the exact finite law

This bridge attaches one embedded Definition 7.2 surface/path/region realization to the exact closed
base presentation used by the finite-law heat factors and their one-pair Facts 2--3 comparison
chain. Its embedded path words are exactly the finite law's holonomy words. In the combinatorially
nonorientable case it also enforces Sengupta's source condition
`h = h⁻¹` for the same finite law's fixed central bundle class.

It remains uninhabited. The fine and transported comparison presentations are only closed
combinatorial presentations, and universal subdivision/homeomorphism invariance remains open.
-/

namespace YangMills.Dimensions

open YangMills.Mathematics
open scoped ENNReal Manifold ContDiff

noncomputable section

universe uG uCover uGauge uSample uConnection uCurve uEdge uInternal uFace uRegion uSenguptaSample
  uSurface uBaseVertex uFineInternal uFineFace uFineVertex
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

/-- Exact embedded base realization plus its closed finite-invariance chain. -/
structure TwoDimensionalSenguptaEmbeddedFiniteLawBridgeData where
  closedInvariance : TwoDimensionalSenguptaClosedPresentationInvarianceBridgeData
    (heatFactors := heatFactors) (BaseVertex := BaseVertex)
    (FineVertex := FineVertex) (fine := fine)
    (TargetVertex := TargetVertex) (target := target)
  embeddedBase : TwoDimensionalSenguptaEmbeddedTriangularPresentationData
    (Surface := Surface) (Curve := Curve) (closed := closedInvariance.baseClosed)
  curveWord_eq_finiteLaw : embeddedBase.curveWord = finiteLaw.curveWord
  nonorientable_bundleClass_involutive :
    ¬ IsSenguptaCombinatoriallyOrientable heatFactors.triangulation →
      finiteLaw.bundleClass = finiteLaw.bundleClass⁻¹

namespace TwoDimensionalSenguptaEmbeddedFiniteLawBridgeData

omit [T2Space CoverGroup] [Nonempty Curve] [Fintype TargetEdge] in
/-- Exact inhabitance audit: the wrapper needs one closed-invariance chain, a dependently indexed
embedded base realization, and the nonorientable fixed-twist condition. -/
theorem nonempty_iff_components :
    Nonempty (TwoDimensionalSenguptaEmbeddedFiniteLawBridgeData
      (heatFactors := heatFactors) (Surface := Surface) (BaseVertex := BaseVertex)
      (FineVertex := FineVertex) (fine := fine)
      (TargetVertex := TargetVertex) (target := target)) ↔
    ∃ closedInvariance : TwoDimensionalSenguptaClosedPresentationInvarianceBridgeData
      (heatFactors := heatFactors) (BaseVertex := BaseVertex)
      (FineVertex := FineVertex) (fine := fine)
      (TargetVertex := TargetVertex) (target := target),
      ∃ embeddedBase : TwoDimensionalSenguptaEmbeddedTriangularPresentationData
        (Surface := Surface) (Curve := Curve) (closed := closedInvariance.baseClosed),
        embeddedBase.curveWord = finiteLaw.curveWord ∧
        (¬ IsSenguptaCombinatoriallyOrientable heatFactors.triangulation →
          finiteLaw.bundleClass = finiteLaw.bundleClass⁻¹) := by
  constructor
  · rintro ⟨data⟩
    exact ⟨data.closedInvariance, data.embeddedBase, data.curveWord_eq_finiteLaw,
      data.nonorientable_bundleClass_involutive⟩
  · rintro ⟨closedInvariance, embeddedBase, curveWordEq, nonorientableTwist⟩
    exact ⟨⟨closedInvariance, embeddedBase, curveWordEq, nonorientableTwist⟩⟩

/-- The embedded realization uses exactly the closed base triangulation stored by this bridge. -/
noncomputable def exact_embeddedBase
    (data : TwoDimensionalSenguptaEmbeddedFiniteLawBridgeData
      (heatFactors := heatFactors) (Surface := Surface) (BaseVertex := BaseVertex)
      (FineVertex := FineVertex) (fine := fine)
      (TargetVertex := TargetVertex) (target := target)) :
    TwoDimensionalSenguptaEmbeddedTriangularPresentationData
      (Surface := Surface) (Curve := Curve) (closed := data.closedInvariance.baseClosed) :=
  data.embeddedBase

omit [T2Space CoverGroup] [Nonempty Curve] [Fintype TargetEdge] in
/-- Source-faithful nonorientable specialization for the exact stored bundle class. -/
theorem bundleClass_eq_inv_of_nonorientable
    (data : TwoDimensionalSenguptaEmbeddedFiniteLawBridgeData
      (heatFactors := heatFactors) (Surface := Surface) (BaseVertex := BaseVertex)
      (FineVertex := FineVertex) (fine := fine)
      (TargetVertex := TargetVertex) (target := target))
    (nonorientable : ¬ IsSenguptaCombinatoriallyOrientable heatFactors.triangulation) :
    finiteLaw.bundleClass = finiteLaw.bundleClass⁻¹ :=
  data.nonorientable_bundleClass_involutive nonorientable

end TwoDimensionalSenguptaEmbeddedFiniteLawBridgeData

end

end YangMills.Dimensions
