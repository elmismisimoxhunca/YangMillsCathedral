/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Dimensions.TwoDimensionalSenguptaEmbeddedComparisonBridge

/-!
# Universal curve-fixed embedded Sengupta subdivision subclass

A candidate bundles an arbitrary embedded refinement of one exact base presentation.
The universal record requires a factor-invariance certificate for every such candidate, with the
certificate's fine-to-coarse face map equal to the geometric refinement map. Unlike a selected
one-pair witness, the quantified candidate type is fixed by this declaration rather than supplied as
an arbitrary predicate.

The candidate class deliberately fixes the external curve-bond carrier and parametrized curve paths.
It therefore quantifies universally only over this curve-fixed subclass. Sengupta's broader Fact 2
also permits subdivision of curve bonds; that requires graph-level delta/pushforward semantics and
remains open.

This is an uninhabited acceptance interface. No universal Fact 2 theorem is proved.
-/

namespace YangMills.Dimensions

open YangMills.Mathematics
open scoped ENNReal Manifold ContDiff

noncomputable section

universe uCover uCurve uEdge uInternal uFace uRegion uSurface uVertex
  uFineInternal uFineFace uFineVertex

variable
    {CoverGroup : Type uCover} [Group CoverGroup]
    [TopologicalSpace CoverGroup] [IsTopologicalGroup CoverGroup]
    [CompactSpace CoverGroup] [MeasurableSpace CoverGroup] [BorelSpace CoverGroup]
    {Curve : Type uCurve} [Fintype Curve]
    {Edge : Type uEdge} [Fintype Edge] [DecidableEq Edge]
    {InternalEdge : Type uInternal} [Fintype InternalEdge] [DecidableEq InternalEdge]
    {Face : Type uFace} [Fintype Face] [DecidableEq Face]
    {Region : Type uRegion} [DecidableEq Region]
    {Surface : Type uSurface} [TopologicalSpace Surface]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) Surface]
    {Vertex : Type uVertex}
    {baseTriangulation : TwoDimensionalSenguptaTriangulatedRegionData
      Edge InternalEdge Face Region}
    {baseClosed : TwoDimensionalSenguptaClosedTriangularPresentationData
      (Vertex := Vertex) baseTriangulation}
    {baseEmbedded : TwoDimensionalSenguptaEmbeddedTriangularPresentationData
      (Surface := Surface) (Curve := Curve) (closed := baseClosed)}
    {coverDensity : ℝ → CoverGroup → ℝ≥0∞}
    {bundleClass : CoverGroup}

/-- One arbitrary embedded geometric subdivision in the curve-fixed subclass. -/
structure TwoDimensionalSenguptaEmbeddedSubdivisionCandidateData where
  FineInternal : Type uFineInternal
  [fineInternalFintype : Fintype FineInternal]
  [fineInternalDecidableEq : DecidableEq FineInternal]
  FineFace : Type uFineFace
  [fineFaceFintype : Fintype FineFace]
  [fineFaceDecidableEq : DecidableEq FineFace]
  FineVertex : Type uFineVertex
  fine : TwoDimensionalSenguptaTriangulatedRegionData Edge FineInternal FineFace Region
  fineClosed : TwoDimensionalSenguptaClosedTriangularPresentationData
    (Vertex := FineVertex) fine
  fineEmbedded : TwoDimensionalSenguptaEmbeddedTriangularPresentationData
    (Surface := Surface) (Curve := Curve) (closed := fineClosed)
  fineFaceToCoarse : FineFace → Face
  fineFaceToCoarse_surjective : Function.Surjective fineFaceToCoarse
  faceRegion_coherence : ∀ fineFace,
    baseTriangulation.faceRegion (fineFaceToCoarse fineFace) = fine.faceRegion fineFace
  regionArea_coherence : ∀ region,
    baseTriangulation.regionArea region = fine.regionArea region
  fineCurveWord_eq_base : fineEmbedded.curveWord = baseEmbedded.curveWord
  fineFaceImage_subset : ∀ fineFace,
    Set.range (fineEmbedded.faceDisk fineFace) ⊆
      Set.range (baseEmbedded.faceDisk (fineFaceToCoarse fineFace))
  coarseFaceImage_eq_fine_union : ∀ coarseFace,
    Set.range (baseEmbedded.faceDisk coarseFace) =
      ⋃ (fineFace : FineFace) (_ : fineFaceToCoarse fineFace = coarseFace),
        Set.range (fineEmbedded.faceDisk fineFace)
  baseVertexToFine : Vertex → FineVertex
  baseVertexToFine_injective : Function.Injective baseVertexToFine
  baseVertexToFine_point : ∀ vertex,
    fineEmbedded.vertexPoint (baseVertexToFine vertex) = baseEmbedded.vertexPoint vertex
  fineExternalEdgePath_eq : ∀ (edge : Edge) (point : SenguptaClosedUnitInterval),
    fineEmbedded.edgePath (Sum.inl edge) point = baseEmbedded.edgePath (Sum.inl edge) point
  coarseEdgeToFineWord : Sum Edge InternalEdge →
    List (OrientedEdge (Sum Edge FineInternal))
  coarseEdgeToFineWord_realizes : ∀ edge,
    IsSenguptaEmbeddedPathSubdivision baseEmbedded.edgePath fineEmbedded.edgePath edge
      (coarseEdgeToFineWord edge)
  coarseFaceBoundary_signedChain_eq : ∀ (coarseFace : Face)
      (fineEdge : Sum Edge FineInternal),
    senguptaOrientedWordSignedIncidence fineEdge
      (senguptaSubstituteOrientedWord coarseEdgeToFineWord
        (baseTriangulation.boundaryWord coarseFace)) =
    ∑ fineFace ∈ Finset.univ.filter (fun fineFace => fineFaceToCoarse fineFace = coarseFace),
      senguptaOrientedWordSignedIncidence fineEdge (fine.boundaryWord fineFace)
  fineRegionSet_eq : ∀ region : Region,
    fineEmbedded.regionSet region = baseEmbedded.regionSet region

namespace TwoDimensionalSenguptaEmbeddedSubdivisionCandidateData

/-- Exact proposition that one geometric candidate has a factor certificate using its own
fine-to-coarse face map. -/
def HasFactorCertificate
    (candidate : TwoDimensionalSenguptaEmbeddedSubdivisionCandidateData.{uCurve, uEdge, uInternal, uFace, uRegion, uSurface, uVertex, uFineInternal, uFineFace, uFineVertex}
      (baseEmbedded := baseEmbedded)) : Prop := by
  letI : Fintype candidate.FineInternal := candidate.fineInternalFintype
  letI : Fintype candidate.FineFace := candidate.fineFaceFintype
  letI : DecidableEq candidate.FineFace := candidate.fineFaceDecidableEq
  exact ∃ certificate : TwoDimensionalSenguptaSubdivisionFactorInvarianceData
      (coverDensity := coverDensity) (coarse := baseTriangulation) (fine := candidate.fine)
      (bundleClass := bundleClass),
    certificate.fineFaceToCoarse = candidate.fineFaceToCoarse

end TwoDimensionalSenguptaEmbeddedSubdivisionCandidateData

/-- Universal acceptance over the concrete curve-fixed embedded subdivision subclass at the stated
universe levels. Nonemptiness prevents a vacuous empty candidate class. The nonorientable source
condition is explicit. -/
structure TwoDimensionalSenguptaUniversalCurveFixedEmbeddedSubdivisionData where
  candidate_nonempty : Nonempty
    (TwoDimensionalSenguptaEmbeddedSubdivisionCandidateData.{uCurve, uEdge, uInternal, uFace, uRegion, uSurface, uVertex, uFineInternal, uFineFace, uFineVertex} (baseEmbedded := baseEmbedded))
  nonorientable_bundleClass_involutive :
    ¬ IsSenguptaCombinatoriallyOrientable baseTriangulation → bundleClass = bundleClass⁻¹
  factorInvariant : ∀ candidate :
      TwoDimensionalSenguptaEmbeddedSubdivisionCandidateData.{uCurve, uEdge, uInternal, uFace, uRegion, uSurface, uVertex, uFineInternal, uFineFace, uFineVertex} (baseEmbedded := baseEmbedded),
    candidate.HasFactorCertificate (coverDensity := coverDensity) (bundleClass := bundleClass)

namespace TwoDimensionalSenguptaUniversalCurveFixedEmbeddedSubdivisionData

omit [Fintype Edge] in
/-- Every supplied geometric refinement receives an exact factor certificate using its own face map. -/
theorem certificate_for
    (data : TwoDimensionalSenguptaUniversalCurveFixedEmbeddedSubdivisionData.{uCover, uCurve, uEdge, uInternal, uFace, uRegion, uSurface, uVertex, uFineInternal, uFineFace, uFineVertex}
      (baseEmbedded := baseEmbedded) (coverDensity := coverDensity)
      (bundleClass := bundleClass))
    (candidate : TwoDimensionalSenguptaEmbeddedSubdivisionCandidateData.{uCurve, uEdge, uInternal, uFace, uRegion, uSurface, uVertex, uFineInternal, uFineFace, uFineVertex}
      (baseEmbedded := baseEmbedded)) :
    candidate.HasFactorCertificate
      (coverDensity := coverDensity) (bundleClass := bundleClass) :=
  data.factorInvariant candidate

end TwoDimensionalSenguptaUniversalCurveFixedEmbeddedSubdivisionData

end

end YangMills.Dimensions
