/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Dimensions.TwoDimensionalSenguptaEmbeddedFiniteLawBridge

/-! Hostile dependency probes for the embedded Sengupta finite-law bridge. -/

namespace YangMills.Dimensions.TwoDimensionalSenguptaEmbeddedFiniteLawBridge.Probes

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
    (data : TwoDimensionalSenguptaEmbeddedFiniteLawBridgeData
      (heatFactors := heatFactors) (Surface := Surface) (BaseVertex := BaseVertex)
      (FineVertex := FineVertex) (fine := fine)
      (TargetVertex := TargetVertex) (target := target))

omit [T2Space CoverGroup] [Nonempty Curve] [Fintype TargetEdge] in
/-- The embedded face boundary uses the exact heat-factor triangulation and exact closed base. -/
theorem exact_embedded_heat_factor_boundary (face : Face) :
    Set.range (fun point : SenguptaUnitCircle =>
      data.embeddedBase.faceDisk face (senguptaCircleToClosedDisk point)) =
    ⋃ (oriented : OrientedEdge (Sum Edge InternalEdge))
      (_ : oriented ∈ heatFactors.triangulation.boundaryWord face),
      Set.range (data.embeddedBase.edgePath (OrientedEdge.underlying oriented)) :=
  data.embeddedBase.faceBoundary_eq_edgeImages face

omit [T2Space CoverGroup] [Nonempty Curve] [Fintype TargetEdge] in
/-- The embedded path family and finite-dimensional holonomy law use literally the same word for
every exact curve index. -/
theorem exact_finite_law_curve_word (curve : Curve) :
    data.embeddedBase.curveWord curve = finiteLaw.curveWord curve :=
  congrFun data.curveWord_eq_finiteLaw curve

omit [T2Space CoverGroup] [Nonempty Curve] [Fintype TargetEdge] in
/-- Hostile coherence probe: changing any embedded curve word blocks the finite-law bridge. -/
theorem changed_finite_law_curve_word_blocked (curve : Curve)
    (changed : data.embeddedBase.curveWord curve ≠ finiteLaw.curveWord curve) : False :=
  changed (congrFun data.curveWord_eq_finiteLaw curve)

omit [T2Space CoverGroup] [Nonempty Curve] [Fintype TargetEdge] in
include data in
/-- In the exact nonorientable case the finite law's fixed twist, not a substitute element, is
involutive. -/
theorem exact_nonorientable_fixed_twist
    (nonorientable : ¬ IsSenguptaCombinatoriallyOrientable heatFactors.triangulation) :
    finiteLaw.bundleClass = finiteLaw.bundleClass⁻¹ :=
  data.nonorientable_bundleClass_involutive nonorientable

omit [T2Space CoverGroup] [Nonempty Curve] [Fintype TargetEdge] in
include data in
/-- Hostile source probe: a changed nonorientable twist contradicts the bridge. -/
theorem changed_nonorientable_twist_blocked
    (nonorientable : ¬ IsSenguptaCombinatoriallyOrientable heatFactors.triangulation)
    (changed : finiteLaw.bundleClass ≠ finiteLaw.bundleClass⁻¹) : False :=
  changed (data.nonorientable_bundleClass_involutive nonorientable)

omit [T2Space CoverGroup] [Nonempty Curve] [Fintype TargetEdge] in
/-- Missing the exact closed-invariance chain blocks embedded finite-law acceptance. -/
theorem missing_closed_invariance_blocks
    (missing : TwoDimensionalSenguptaClosedPresentationInvarianceBridgeData
      (heatFactors := heatFactors) (BaseVertex := BaseVertex)
      (FineVertex := FineVertex) (fine := fine)
      (TargetVertex := TargetVertex) (target := target) → False) :
    TwoDimensionalSenguptaEmbeddedFiniteLawBridgeData
      (heatFactors := heatFactors) (Surface := Surface) (BaseVertex := BaseVertex)
      (FineVertex := FineVertex) (fine := fine)
      (TargetVertex := TargetVertex) (target := target) → False :=
  fun bridge => missing bridge.closedInvariance

omit [T2Space CoverGroup] [Nonempty Curve] [Fintype TargetEdge] in
/-- A closed base without its exact embedded realization is still insufficient. -/
theorem missing_embedded_base_blocks
    (missing : ∀ closedInvariance :
      TwoDimensionalSenguptaClosedPresentationInvarianceBridgeData
        (heatFactors := heatFactors) (BaseVertex := BaseVertex)
        (FineVertex := FineVertex) (fine := fine)
        (TargetVertex := TargetVertex) (target := target),
      TwoDimensionalSenguptaEmbeddedTriangularPresentationData
        (Surface := Surface) (Curve := Curve) (closed := closedInvariance.baseClosed) → False) :
    TwoDimensionalSenguptaEmbeddedFiniteLawBridgeData
      (heatFactors := heatFactors) (Surface := Surface) (BaseVertex := BaseVertex)
      (FineVertex := FineVertex) (fine := fine)
      (TargetVertex := TargetVertex) (target := target) → False :=
  fun bridge => missing bridge.closedInvariance bridge.embeddedBase

end

end YangMills.Dimensions.TwoDimensionalSenguptaEmbeddedFiniteLawBridge.Probes
