/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Dimensions.TwoDimensionalSenguptaEmbeddedComparisonBridge

/-! Hostile probes for embedded Sengupta comparison geometry. -/

namespace YangMills.Dimensions.TwoDimensionalSenguptaEmbeddedComparisonBridge.Probes

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
    [CompactSpace CoverGroup]
    [MeasurableSpace CoverGroup] [BorelSpace CoverGroup]
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
    {embeddedFiniteLaw : TwoDimensionalSenguptaEmbeddedFiniteLawBridgeData
      (heatFactors := heatFactors) (Surface := Surface) (BaseVertex := BaseVertex)
      (FineVertex := FineVertex) (fine := fine)
      (TargetVertex := TargetVertex) (target := target)}
    (data : TwoDimensionalSenguptaEmbeddedComparisonBridgeData
      (embeddedFiniteLaw := embeddedFiniteLaw) (TargetSurface := TargetSurface))

/-- Subdivision and homeomorphism curve words use the exact selected edge maps. -/
theorem exact_comparison_curve_words (curve : Curve) :
    data.embeddedFine.curveWord curve = embeddedFiniteLaw.embeddedBase.curveWord curve ∧
    data.embeddedTarget.curveWord curve =
      (embeddedFiniteLaw.embeddedBase.curveWord curve).map
        (senguptaMapOrientedEdge
          embeddedFiniteLaw.closedInvariance.invariance.homeomorphism.externalEdgeEquiv) :=
  ⟨congrFun data.fineCurveWord_eq_base curve, data.targetCurveWord_eq_map curve⟩

/-- Fine faces exactly partition each exact base face image. -/
theorem exact_embedded_subdivision (coarseFace : Face) :
    Set.range (embeddedFiniteLaw.embeddedBase.faceDisk coarseFace) =
      ⋃ (fineFace : FineFace)
        (_ : embeddedFiniteLaw.closedInvariance.invariance.subdivision.fineFaceToCoarse fineFace =
          coarseFace), Set.range (data.embeddedFine.faceDisk fineFace) :=
  data.coarseFaceImage_eq_fine_union coarseFace

/-- The fine comparison leaves exact parametrized external paths and complement regions
unchanged. -/
theorem exact_subdivision_external_geometry (edge : Edge)
    (point : SenguptaClosedUnitInterval) (region : Region) :
    data.embeddedFine.edgePath (Sum.inl edge) point =
      embeddedFiniteLaw.embeddedBase.edgePath (Sum.inl edge) point ∧
    data.embeddedFine.regionSet region = embeddedFiniteLaw.embeddedBase.regionSet region :=
  ⟨data.fineExternalEdgePath_eq edge point, data.fineRegionSet_eq region⟩

/-- Every coarse bond has an exact nonempty directed fine-edge-word realization, and coarse vertices
are retained geometrically. -/
theorem exact_bond_subdivision (edge : Sum Edge InternalEdge) (vertex : BaseVertex) :
    IsSenguptaEmbeddedPathSubdivision embeddedFiniteLaw.embeddedBase.edgePath
      data.embeddedFine.edgePath edge (data.coarseEdgeToFineWord edge) ∧
    data.embeddedFine.vertexPoint (data.baseVertexToFine vertex) =
      embeddedFiniteLaw.embeddedBase.vertexPoint vertex :=
  ⟨data.coarseEdgeToFineWord_realizes edge, data.baseVertexToFine_point vertex⟩

/-- Repeated or backtracking fine bonds cannot masquerade as a simplicial bond subdivision. -/
theorem exact_bond_subdivision_nodup (edge : Sum Edge InternalEdge) :
    ((data.coarseEdgeToFineWord edge).map OrientedEdge.underlying).Nodup :=
  (data.coarseEdgeToFineWord_realizes edge).2.1

/-- Hostile repeated-bond probe. -/
theorem repeated_fine_bond_blocks_subdivision (edge : Sum Edge InternalEdge)
    (repeated : ¬ ((data.coarseEdgeToFineWord edge).map OrientedEdge.underlying).Nodup) : False :=
  repeated (data.coarseEdgeToFineWord_realizes edge).2.1

/-- Directed substitution of coarse face bonds equals the signed fine-face boundary after internal
cancellation. -/
theorem exact_coarse_face_boundary_substitution (coarseFace : Face)
    (fineEdge : Sum Edge FineInternal) :
    senguptaOrientedWordSignedIncidence fineEdge
      (senguptaSubstituteOrientedWord data.coarseEdgeToFineWord
        (heatFactors.triangulation.boundaryWord coarseFace)) =
    ∑ fineFace ∈ Finset.univ.filter (fun fineFace =>
        embeddedFiniteLaw.closedInvariance.invariance.subdivision.fineFaceToCoarse fineFace =
          coarseFace),
      senguptaOrientedWordSignedIncidence fineEdge (fine.boundaryWord fineFace) :=
  data.coarseFaceBoundary_signedChain_eq coarseFace fineEdge

/-- Hostile oriented-boundary cancellation probe. -/
theorem changed_coarse_face_boundary_substitution_blocked (coarseFace : Face)
    (fineEdge : Sum Edge FineInternal)
    (changed : senguptaOrientedWordSignedIncidence fineEdge
      (senguptaSubstituteOrientedWord data.coarseEdgeToFineWord
        (heatFactors.triangulation.boundaryWord coarseFace)) ≠
    ∑ fineFace ∈ Finset.univ.filter (fun fineFace =>
        embeddedFiniteLaw.closedInvariance.invariance.subdivision.fineFaceToCoarse fineFace =
          coarseFace),
      senguptaOrientedWordSignedIncidence fineEdge (fine.boundaryWord fineFace)) : False :=
  changed (data.coarseFaceBoundary_signedChain_eq coarseFace fineEdge)

/-- The explicit homeomorphism transports exact vertices and face images. -/
theorem exact_homeomorphism_vertex_face (vertex : BaseVertex) (face : Face) :
    data.surfaceHomeomorphism (embeddedFiniteLaw.embeddedBase.vertexPoint vertex) =
      data.embeddedTarget.vertexPoint (data.vertexEquiv vertex) ∧
    data.surfaceHomeomorphism '' Set.range (embeddedFiniteLaw.embeddedBase.faceDisk face) =
      Set.range (data.embeddedTarget.faceDisk
        (embeddedFiniteLaw.closedInvariance.invariance.homeomorphism.faceEquiv face)) :=
  ⟨data.homeomorphism_vertex vertex, data.homeomorphism_faceImage face⟩

/-- The real homeomorphism transports every parametrized edge through an endpoint-preserving
reparametrization. -/
theorem exact_homeomorphism_edge_path (edge : Sum Edge InternalEdge)
    (point : SenguptaClosedUnitInterval) :
    data.surfaceHomeomorphism (embeddedFiniteLaw.embeddedBase.edgePath edge point) =
      data.embeddedTarget.edgePath
        (Sum.map embeddedFiniteLaw.closedInvariance.invariance.homeomorphism.externalEdgeEquiv
          embeddedFiniteLaw.closedInvariance.invariance.homeomorphism.internalEdgeEquiv edge)
        (data.targetEdgeReparam edge point) ∧
    data.targetEdgeReparam edge ⟨0, by norm_num⟩ = ⟨0, by norm_num⟩ ∧
    data.targetEdgeReparam edge ⟨1, by norm_num⟩ = ⟨1, by norm_num⟩ :=
  ⟨data.homeomorphism_edgePath edge point, data.targetEdgeReparam_initial edge,
    data.targetEdgeReparam_terminal edge⟩

/-- The actual disk-boundary action realizes each independently selected simplex orientation;
the nonorientable global negative sign does not force local reversal. -/
theorem exact_homeomorphism_face_orientation (face : Face) :
    if embeddedFiniteLaw.closedInvariance.invariance.homeomorphism.faceOrientationReversed face then
      ∀ side point,
        data.faceReparam face (senguptaCircleToClosedDisk
          (embeddedFiniteLaw.embeddedBase.faceSideParam face side point)) =
        senguptaCircleToClosedDisk
          (data.embeddedTarget.faceSideParam
            (embeddedFiniteLaw.closedInvariance.invariance.homeomorphism.faceEquiv face)
            (Fin.rev side) (senguptaReverseClosedUnitInterval point))
    else
      ∀ side point,
        data.faceReparam face (senguptaCircleToClosedDisk
          (embeddedFiniteLaw.embeddedBase.faceSideParam face side point)) =
        senguptaCircleToClosedDisk
          (data.embeddedTarget.faceSideParam
            (embeddedFiniteLaw.closedInvariance.invariance.homeomorphism.faceEquiv face)
            side point) :=
  data.faceReparam_realizes_faceOrientation face

/-- Positive is equivalent to an orientable source plus actual marked-boundary orientation
preservation. -/
theorem exact_positive_orientation_criterion :
    embeddedFiniteLaw.closedInvariance.invariance.homeomorphism.orientationSign = .positive ↔
      IsSenguptaCombinatoriallyOrientable heatFactors.triangulation ∧
      ∀ face side point,
        data.faceReparam face (senguptaCircleToClosedDisk
          (embeddedFiniteLaw.embeddedBase.faceSideParam face side point)) =
        senguptaCircleToClosedDisk
          (data.embeddedTarget.faceSideParam
            (embeddedFiniteLaw.closedInvariance.invariance.homeomorphism.faceEquiv face)
            side point) :=
  data.orientationSign_positive_iff

include data in
/-- Hostile sign probe: a nonorientable source cannot be assigned the positive Fact 3 sign. -/
theorem nonorientable_positive_sign_blocked
    (nonorientable : ¬ IsSenguptaCombinatoriallyOrientable heatFactors.triangulation)
    (positive : embeddedFiniteLaw.closedInvariance.invariance.homeomorphism.orientationSign =
      .positive) : False :=
  nonorientable (data.orientationSign_positive_iff.mp positive).1

/-- The same homeomorphism transports edge images and exact complement components. -/
theorem exact_homeomorphism_edge_region (edge : Sum Edge InternalEdge) (region : Region) :
    data.surfaceHomeomorphism ''
      Set.range (embeddedFiniteLaw.embeddedBase.edgePath edge) =
      Set.range (data.embeddedTarget.edgePath
        (Sum.map embeddedFiniteLaw.closedInvariance.invariance.homeomorphism.externalEdgeEquiv
          embeddedFiniteLaw.closedInvariance.invariance.homeomorphism.internalEdgeEquiv edge)) ∧
    data.surfaceHomeomorphism '' embeddedFiniteLaw.embeddedBase.regionSet region =
      data.embeddedTarget.regionSet
        (embeddedFiniteLaw.closedInvariance.invariance.homeomorphism.regionEquiv region) :=
  ⟨data.homeomorphism_edgeImage edge, data.homeomorphism_regionSet region⟩

/-- Hostile geometric Fact 2 probe: dropping any fine face from the exact base image is rejected. -/
theorem changed_coarse_face_partition_blocked (coarseFace : Face)
    (changed : Set.range (embeddedFiniteLaw.embeddedBase.faceDisk coarseFace) ≠
      ⋃ (fineFace : FineFace)
        (_ : embeddedFiniteLaw.closedInvariance.invariance.subdivision.fineFaceToCoarse fineFace =
          coarseFace), Set.range (data.embeddedFine.faceDisk fineFace)) : False :=
  changed (data.coarseFaceImage_eq_fine_union coarseFace)

/-- Hostile path probe: reversing or otherwise changing the required parametrized image is
rejected. -/
theorem changed_transported_edge_path_blocked (edge : Sum Edge InternalEdge)
    (point : SenguptaClosedUnitInterval)
    (changed : data.surfaceHomeomorphism
        (embeddedFiniteLaw.embeddedBase.edgePath edge point) ≠
      data.embeddedTarget.edgePath
        (Sum.map embeddedFiniteLaw.closedInvariance.invariance.homeomorphism.externalEdgeEquiv
          embeddedFiniteLaw.closedInvariance.invariance.homeomorphism.internalEdgeEquiv edge)
        (data.targetEdgeReparam edge point)) : False :=
  changed (data.homeomorphism_edgePath edge point)

/-- Hostile geometric Fact 3 probe: changing an exact transported region is rejected. -/
theorem changed_transported_region_blocked (region : Region)
    (changed : data.surfaceHomeomorphism '' embeddedFiniteLaw.embeddedBase.regionSet region ≠
      data.embeddedTarget.regionSet
        (embeddedFiniteLaw.closedInvariance.invariance.homeomorphism.regionEquiv region)) : False :=
  changed (data.homeomorphism_regionSet region)

end

end YangMills.Dimensions.TwoDimensionalSenguptaEmbeddedComparisonBridge.Probes
