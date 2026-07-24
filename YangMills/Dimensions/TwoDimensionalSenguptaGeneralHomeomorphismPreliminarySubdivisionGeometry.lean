/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Dimensions.TwoDimensionalSenguptaGeneralEmbeddedHomeomorphismCandidate
import YangMills.Dimensions.TwoDimensionalSenguptaEmbeddedCurveBondGraphMeasureBridge

/-!
# Preliminary-subdivision geometry for general Sengupta Fact 3 candidates

Sengupta's proof of Fact 3 first subdivides both triangulated surface/curve pairs and then replaces
the original homeomorphism by a simplicial one with the same action on the indexed curves. This file
states that exact geometric construction target for the already formalized general outer candidate.

Both preliminary subdivisions may split curve bonds and are certified by the parameterized embedded
curve-bond geometry. Their fine presentations are joined by the parameterized direct-cellwise
homeomorphism geometry. A continuous isotopy through actual homeomorphisms starts at the unchanged
outer candidate map and ends at that fine cellwise map, matching Sengupta's deformation step.

This file constructs none of those data. It contains no factor invariance, weighted graph-measure
pushforward, or full Fact 3 theorem.
-/

namespace YangMills.Dimensions

open YangMills.Mathematics
open scoped Manifold ContDiff ENNReal

noncomputable section

universe uCurve uEdge uInternal uFace uRegion uSurface uVertex
  uTargetEdge uTargetInternal uTargetFace uTargetRegion uTargetSurface uTargetVertex
  uSourceFineEdge uSourceFineInternal uSourceFineFace uSourceFineVertex
  uTargetFineEdge uTargetFineInternal uTargetFineFace uTargetFineVertex

variable
    {Curve : Type uCurve} [Fintype Curve] [Nonempty Curve]
    {Edge : Type uEdge} [Fintype Edge] [DecidableEq Edge]
    {InternalEdge : Type uInternal} [Fintype InternalEdge] [DecidableEq InternalEdge]
    {Face : Type uFace} [Fintype Face] [DecidableEq Face]
    {Region : Type uRegion} [Fintype Region] [DecidableEq Region]
    {Surface : Type uSurface} [TopologicalSpace Surface]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) Surface]
    {Vertex : Type uVertex}
    {baseTriangulation : TwoDimensionalSenguptaTriangulatedRegionData
      Edge InternalEdge Face Region}
    {baseClosed : TwoDimensionalSenguptaClosedTriangularPresentationData
      (Vertex := Vertex) baseTriangulation}
    {baseEmbedded : TwoDimensionalSenguptaEmbeddedTriangularPresentationData
      (Surface := Surface) (Curve := Curve) (closed := baseClosed)}

attribute [local instance]
  TwoDimensionalSenguptaGeneralEmbeddedHomeomorphismCandidateData.targetSurfaceTopology
  TwoDimensionalSenguptaGeneralEmbeddedHomeomorphismCandidateData.targetSurfaceCharted
  TwoDimensionalSenguptaGeneralEmbeddedHomeomorphismCandidateData.targetEdgeFintype
  TwoDimensionalSenguptaGeneralEmbeddedHomeomorphismCandidateData.targetEdgeDecidableEq
  TwoDimensionalSenguptaGeneralEmbeddedHomeomorphismCandidateData.targetInternalFintype
  TwoDimensionalSenguptaGeneralEmbeddedHomeomorphismCandidateData.targetInternalDecidableEq
  TwoDimensionalSenguptaGeneralEmbeddedHomeomorphismCandidateData.targetFaceFintype
  TwoDimensionalSenguptaGeneralEmbeddedHomeomorphismCandidateData.targetFaceDecidableEq
  TwoDimensionalSenguptaGeneralEmbeddedHomeomorphismCandidateData.targetRegionFintype
  TwoDimensionalSenguptaGeneralEmbeddedHomeomorphismCandidateData.targetRegionDecidableEq

/-- An isotopy through actual homeomorphisms from the original outer map to the final cellwise map.
This records Sengupta's deformation step separately from the subsequent simplicialization. -/
structure TwoDimensionalSenguptaHomeomorphismIsotopyData
    {TargetSurface : Type*} [TopologicalSpace TargetSurface]
    (initial terminal : Surface ≃ₜ TargetSurface) where
  family : SenguptaClosedUnitInterval → Surface ≃ₜ TargetSurface
  initial_eq : family ⟨0, by norm_num⟩ = initial
  terminal_eq : family ⟨1, by norm_num⟩ = terminal
  continuous_eval : Continuous (fun point : SenguptaClosedUnitInterval × Surface =>
    family point.1 point.2)

/-- One exact pair of preliminary split-bond subdivisions and a direct cellwise realization isotopic
to the original outer homeomorphism. -/
structure TwoDimensionalSenguptaGeneralHomeomorphismPreliminarySubdivisionGeometryData
    (candidate : TwoDimensionalSenguptaGeneralEmbeddedHomeomorphismCandidateData.{uCurve,
      uEdge, uInternal, uFace, uRegion, uSurface, uVertex, uTargetEdge, uTargetInternal,
      uTargetFace, uTargetRegion, uTargetSurface, uTargetVertex}
      (baseEmbedded := baseEmbedded)) where
  SourceFineEdge : Type uSourceFineEdge
  [sourceFineEdgeFintype : Fintype SourceFineEdge]
  [sourceFineEdgeDecidableEq : DecidableEq SourceFineEdge]
  SourceFineInternal : Type uSourceFineInternal
  [sourceFineInternalFintype : Fintype SourceFineInternal]
  [sourceFineInternalDecidableEq : DecidableEq SourceFineInternal]
  SourceFineFace : Type uSourceFineFace
  [sourceFineFaceFintype : Fintype SourceFineFace]
  [sourceFineFaceDecidableEq : DecidableEq SourceFineFace]
  SourceFineVertex : Type uSourceFineVertex
  sourceFine : TwoDimensionalSenguptaTriangulatedRegionData
    SourceFineEdge SourceFineInternal SourceFineFace Region
  sourceFineClosed : TwoDimensionalSenguptaClosedTriangularPresentationData
    (Vertex := SourceFineVertex) sourceFine
  sourceFineEmbedded : TwoDimensionalSenguptaEmbeddedTriangularPresentationData
    (Surface := Surface) (Curve := Curve) (closed := sourceFineClosed)
  sourceFineCurveWord : Curve → List (OrientedEdge SourceFineEdge)
  sourceCurveRefinement : TwoDimensionalSenguptaCurveBondRefinementData
    (coarseSource := fun edge => baseClosed.edgeInitial (Sum.inl edge))
    (coarseTarget := fun edge => baseClosed.edgeTerminal (Sum.inl edge))
    (fineSource := fun edge => sourceFineClosed.edgeInitial (Sum.inl edge))
    (fineTarget := fun edge => sourceFineClosed.edgeTerminal (Sum.inl edge))
    (coarseCurveWord := baseEmbedded.curveWord) (fineCurveWord := sourceFineCurveWord)
  sourceSubdivision : TwoDimensionalSenguptaParameterizedEmbeddedCurveBondSubdivisionGeometryData
    baseTriangulation baseClosed baseEmbedded baseEmbedded.curveWord sourceFine sourceFineClosed
      sourceFineEmbedded sourceFineCurveWord sourceCurveRefinement
  TargetFineEdge : Type uTargetFineEdge
  [targetFineEdgeFintype : Fintype TargetFineEdge]
  [targetFineEdgeDecidableEq : DecidableEq TargetFineEdge]
  TargetFineInternal : Type uTargetFineInternal
  [targetFineInternalFintype : Fintype TargetFineInternal]
  [targetFineInternalDecidableEq : DecidableEq TargetFineInternal]
  TargetFineFace : Type uTargetFineFace
  [targetFineFaceFintype : Fintype TargetFineFace]
  [targetFineFaceDecidableEq : DecidableEq TargetFineFace]
  TargetFineVertex : Type uTargetFineVertex
  targetFine : TwoDimensionalSenguptaTriangulatedRegionData
    TargetFineEdge TargetFineInternal TargetFineFace candidate.TargetRegion
  targetFineClosed : TwoDimensionalSenguptaClosedTriangularPresentationData
    (Vertex := TargetFineVertex) targetFine
  targetFineEmbedded : TwoDimensionalSenguptaEmbeddedTriangularPresentationData
    (Surface := candidate.TargetSurface) (Curve := Curve) (closed := targetFineClosed)
  targetFineCurveWord : Curve → List (OrientedEdge TargetFineEdge)
  targetCurveRefinement : TwoDimensionalSenguptaCurveBondRefinementData
    (coarseSource := fun edge => candidate.targetClosed.edgeInitial (Sum.inl edge))
    (coarseTarget := fun edge => candidate.targetClosed.edgeTerminal (Sum.inl edge))
    (fineSource := fun edge => targetFineClosed.edgeInitial (Sum.inl edge))
    (fineTarget := fun edge => targetFineClosed.edgeTerminal (Sum.inl edge))
    (coarseCurveWord := candidate.targetEmbedded.curveWord)
    (fineCurveWord := targetFineCurveWord)
  targetSubdivision : TwoDimensionalSenguptaParameterizedEmbeddedCurveBondSubdivisionGeometryData
    candidate.target candidate.targetClosed candidate.targetEmbedded
      candidate.targetEmbedded.curveWord targetFine targetFineClosed targetFineEmbedded
      targetFineCurveWord targetCurveRefinement
  fineCellwise : TwoDimensionalSenguptaCellwiseEmbeddedHomeomorphismGeometryData
    (baseEmbedded := sourceFineEmbedded) (targetEmbedded := targetFineEmbedded)
  fineCellwise_isotopy : TwoDimensionalSenguptaHomeomorphismIsotopyData
    candidate.surfaceHomeomorphism fineCellwise.surfaceHomeomorphism

namespace TwoDimensionalSenguptaGeneralHomeomorphismPreliminarySubdivisionGeometryData

attribute [local instance] sourceFineEdgeFintype sourceFineEdgeDecidableEq
  sourceFineInternalFintype sourceFineInternalDecidableEq sourceFineFaceFintype
  sourceFineFaceDecidableEq targetFineEdgeFintype targetFineEdgeDecidableEq
  targetFineInternalFintype targetFineInternalDecidableEq targetFineFaceFintype
  targetFineFaceDecidableEq

omit [Nonempty Curve] [Fintype Region] in
/-- The isotopy starts at the unchanged outer homeomorphism. -/
theorem exact_isotopy_initial
    {candidate : TwoDimensionalSenguptaGeneralEmbeddedHomeomorphismCandidateData.{uCurve,
      uEdge, uInternal, uFace, uRegion, uSurface, uVertex, uTargetEdge, uTargetInternal,
      uTargetFace, uTargetRegion, uTargetSurface, uTargetVertex}
      (baseEmbedded := baseEmbedded)}
    (data : TwoDimensionalSenguptaGeneralHomeomorphismPreliminarySubdivisionGeometryData
      candidate) :
    data.fineCellwise_isotopy.family ⟨0, by norm_num⟩ = candidate.surfaceHomeomorphism :=
  data.fineCellwise_isotopy.initial_eq

omit [Nonempty Curve] [Fintype Region] in
/-- The isotopy ends at the directly cellwise-compatible fine homeomorphism. -/
theorem exact_isotopy_terminal
    {candidate : TwoDimensionalSenguptaGeneralEmbeddedHomeomorphismCandidateData.{uCurve,
      uEdge, uInternal, uFace, uRegion, uSurface, uVertex, uTargetEdge, uTargetInternal,
      uTargetFace, uTargetRegion, uTargetSurface, uTargetVertex}
      (baseEmbedded := baseEmbedded)}
    (data : TwoDimensionalSenguptaGeneralHomeomorphismPreliminarySubdivisionGeometryData
      candidate) :
    data.fineCellwise_isotopy.family ⟨1, by norm_num⟩ =
      data.fineCellwise.surfaceHomeomorphism :=
  data.fineCellwise_isotopy.terminal_eq

end TwoDimensionalSenguptaGeneralHomeomorphismPreliminarySubdivisionGeometryData

namespace TwoDimensionalSenguptaGeneralEmbeddedHomeomorphismCandidateData

/-- Exact geometric preliminary-subdivision construction target for one general candidate. -/
def HasPreliminarySubdivisionGeometry
    (candidate : TwoDimensionalSenguptaGeneralEmbeddedHomeomorphismCandidateData.{uCurve,
      uEdge, uInternal, uFace, uRegion, uSurface, uVertex, uTargetEdge, uTargetInternal,
      uTargetFace, uTargetRegion, uTargetSurface, uTargetVertex}
      (baseEmbedded := baseEmbedded)) : Prop :=
  Nonempty
    (TwoDimensionalSenguptaGeneralHomeomorphismPreliminarySubdivisionGeometryData.{uCurve,
      uEdge, uInternal, uFace, uRegion, uSurface, uVertex, uTargetEdge, uTargetInternal,
      uTargetFace, uTargetRegion, uTargetSurface, uTargetVertex, uSourceFineEdge,
      uSourceFineInternal, uSourceFineFace, uSourceFineVertex, uTargetFineEdge,
      uTargetFineInternal, uTargetFineFace, uTargetFineVertex} candidate)

end TwoDimensionalSenguptaGeneralEmbeddedHomeomorphismCandidateData

/-- Fixed-universe universal geometric construction target for every general outer Fact 3 candidate.
Candidate nonemptiness prevents vacuous quantification. Analytic certification remains separate. -/
structure TwoDimensionalSenguptaUniversalGeneralHomeomorphismPreliminarySubdivisionGeometryData where
  candidate_nonempty : Nonempty
    (TwoDimensionalSenguptaGeneralEmbeddedHomeomorphismCandidateData.{uCurve,
      uEdge, uInternal, uFace, uRegion, uSurface, uVertex, uTargetEdge, uTargetInternal,
      uTargetFace, uTargetRegion, uTargetSurface, uTargetVertex}
      (baseEmbedded := baseEmbedded))
  preliminarySubdivision : ∀ candidate :
    TwoDimensionalSenguptaGeneralEmbeddedHomeomorphismCandidateData.{uCurve,
      uEdge, uInternal, uFace, uRegion, uSurface, uVertex, uTargetEdge, uTargetInternal,
      uTargetFace, uTargetRegion, uTargetSurface, uTargetVertex}
      (baseEmbedded := baseEmbedded),
    candidate.HasPreliminarySubdivisionGeometry.{uCurve, uEdge, uInternal, uFace, uRegion,
      uSurface, uVertex, uTargetEdge, uTargetInternal, uTargetFace, uTargetRegion,
      uTargetSurface, uTargetVertex, uSourceFineEdge, uSourceFineInternal, uSourceFineFace,
      uSourceFineVertex, uTargetFineEdge, uTargetFineInternal, uTargetFineFace,
      uTargetFineVertex}

namespace TwoDimensionalSenguptaUniversalGeneralHomeomorphismPreliminarySubdivisionGeometryData

omit [Nonempty Curve] [Fintype Region] in
/-- Every concrete general outer candidate receives preliminary source/target subdivision geometry. -/
theorem geometry_for
    (data : TwoDimensionalSenguptaUniversalGeneralHomeomorphismPreliminarySubdivisionGeometryData.{uCurve,
      uEdge, uInternal, uFace, uRegion, uSurface, uVertex, uTargetEdge, uTargetInternal,
      uTargetFace, uTargetRegion, uTargetSurface, uTargetVertex, uSourceFineEdge,
      uSourceFineInternal, uSourceFineFace, uSourceFineVertex, uTargetFineEdge,
      uTargetFineInternal, uTargetFineFace, uTargetFineVertex}
      (baseEmbedded := baseEmbedded))
    (candidate : TwoDimensionalSenguptaGeneralEmbeddedHomeomorphismCandidateData.{uCurve,
      uEdge, uInternal, uFace, uRegion, uSurface, uVertex, uTargetEdge, uTargetInternal,
      uTargetFace, uTargetRegion, uTargetSurface, uTargetVertex}
      (baseEmbedded := baseEmbedded)) :
    candidate.HasPreliminarySubdivisionGeometry.{uCurve, uEdge, uInternal, uFace, uRegion,
      uSurface, uVertex, uTargetEdge, uTargetInternal, uTargetFace, uTargetRegion,
      uTargetSurface, uTargetVertex, uSourceFineEdge, uSourceFineInternal, uSourceFineFace,
      uSourceFineVertex, uTargetFineEdge, uTargetFineInternal, uTargetFineFace,
      uTargetFineVertex} :=
  data.preliminarySubdivision candidate

end TwoDimensionalSenguptaUniversalGeneralHomeomorphismPreliminarySubdivisionGeometryData

end

end YangMills.Dimensions
