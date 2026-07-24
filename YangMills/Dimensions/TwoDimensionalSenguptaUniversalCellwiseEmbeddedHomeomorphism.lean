/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Dimensions.TwoDimensionalSenguptaEmbeddedComparisonBridge

/-!
# Universal cellwise-compatible embedded Sengupta homeomorphism subclass

The bundled candidate type describes an arbitrary embedded target presentation and an actual
homeomorphism from one exact base presentation. It includes exact vertex, parametrized-edge,
face-disk, curve-word, complement-region, total-area, and orientation-sign transport. The universal
record requires a matching factor certificate for every candidate at the stated universe levels and
requires the candidate class to be nonempty.

This candidate class requires a direct cellwise correspondence. Sengupta's full Fact 3 permits
homeomorphisms that become simplicial only after subdividing source and target. Universal acceptance
for that broader class remains open.

This is an uninhabited acceptance interface for the cellwise-compatible subclass, not a proof or
construction.
-/

namespace YangMills.Dimensions

open YangMills.Mathematics
open scoped ENNReal Manifold ContDiff

noncomputable section

universe uCover uCurve uEdge uInternal uFace uRegion uSurface uVertex
  uTargetEdge uTargetInternal uTargetFace uTargetRegion uTargetSurface uTargetVertex

variable
    {CoverGroup : Type uCover} [Group CoverGroup]
    [TopologicalSpace CoverGroup] [IsTopologicalGroup CoverGroup]
    [CompactSpace CoverGroup] [MeasurableSpace CoverGroup] [BorelSpace CoverGroup]
    {Curve : Type uCurve} [Fintype Curve]
    {Edge : Type uEdge} [DecidableEq Edge]
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

variable
    {TargetEdge : Type uTargetEdge} [Fintype TargetEdge] [DecidableEq TargetEdge]
    {TargetInternal : Type uTargetInternal} [Fintype TargetInternal]
    [DecidableEq TargetInternal]
    {TargetFace : Type uTargetFace} [Fintype TargetFace] [DecidableEq TargetFace]
    {TargetRegion : Type uTargetRegion} [Fintype TargetRegion] [DecidableEq TargetRegion]
    {TargetSurface : Type uTargetSurface} [TopologicalSpace TargetSurface]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) TargetSurface]
    {TargetVertex : Type uTargetVertex}
    {target : TwoDimensionalSenguptaTriangulatedRegionData
      TargetEdge TargetInternal TargetFace TargetRegion}
    {targetClosed : TwoDimensionalSenguptaClosedTriangularPresentationData
      (Vertex := TargetVertex) target}
    {targetEmbedded : TwoDimensionalSenguptaEmbeddedTriangularPresentationData
      (Surface := TargetSurface) (Curve := Curve) (closed := targetClosed)}

/-- Parameterized geometric content of one directly cellwise-compatible embedded homeomorphism.
Unlike the bundled candidate below, source and target presentations are explicit parameters. This
view is reusable when preliminary-subdivision constructions choose their fine presentations first. -/
structure TwoDimensionalSenguptaCellwiseEmbeddedHomeomorphismGeometryData where
  orientationSign : SenguptaHomeomorphismOrientationSign
  faceOrientationReversed : Face → Bool
  externalEdgeEquiv : Edge ≃ TargetEdge
  internalEdgeEquiv : InternalEdge ≃ TargetInternal
  faceEquiv : Face ≃ TargetFace
  regionEquiv : Region ≃ TargetRegion
  faceRegion_coherence : ∀ face,
    target.faceRegion (faceEquiv face) = regionEquiv (baseTriangulation.faceRegion face)
  regionArea_coherence : ∀ region,
    target.regionArea (regionEquiv region) = baseTriangulation.regionArea region
  boundaryWord_coherence : ∀ face,
    target.boundaryWord (faceEquiv face) =
      senguptaTransportedBoundaryWordByReversal (faceOrientationReversed face)
        (Sum.map externalEdgeEquiv internalEdgeEquiv) (baseTriangulation.boundaryWord face)
  targetCurveWord_eq_map : ∀ curve,
    targetEmbedded.curveWord curve =
      (baseEmbedded.curveWord curve).map (senguptaMapOrientedEdge externalEdgeEquiv)
  surfaceHomeomorphism : Surface ≃ₜ TargetSurface
  targetEdgeReparam : Sum Edge InternalEdge →
    SenguptaClosedUnitInterval ≃ₜ SenguptaClosedUnitInterval
  targetEdgeReparam_initial : ∀ edge,
    targetEdgeReparam edge ⟨0, by norm_num⟩ = ⟨0, by norm_num⟩
  targetEdgeReparam_terminal : ∀ edge,
    targetEdgeReparam edge ⟨1, by norm_num⟩ = ⟨1, by norm_num⟩
  homeomorphism_edgePath : ∀ edge point,
    surfaceHomeomorphism (baseEmbedded.edgePath edge point) =
      targetEmbedded.edgePath (Sum.map externalEdgeEquiv internalEdgeEquiv edge)
        (targetEdgeReparam edge point)
  vertexEquiv : Vertex ≃ TargetVertex
  homeomorphism_vertex : ∀ vertex,
    surfaceHomeomorphism (baseEmbedded.vertexPoint vertex) =
      targetEmbedded.vertexPoint (vertexEquiv vertex)
  faceReparam : Face → SenguptaClosedUnitDisk ≃ₜ SenguptaClosedUnitDisk
  homeomorphism_facePoint : ∀ face point,
    surfaceHomeomorphism (baseEmbedded.faceDisk face point) =
      targetEmbedded.faceDisk (faceEquiv face) (faceReparam face point)
  orientationSign_positive_iff :
    orientationSign = .positive ↔
      IsSenguptaCombinatoriallyOrientable baseTriangulation ∧
      ∀ face side point,
        faceReparam face (senguptaCircleToClosedDisk
          (baseEmbedded.faceSideParam face side point)) =
        senguptaCircleToClosedDisk
          (targetEmbedded.faceSideParam (faceEquiv face) side point)
  faceOrientationReversed_false_of_positive :
    orientationSign = .positive → ∀ face, ¬ faceOrientationReversed face
  faceOrientationReversed_true_of_orientable_negative :
    IsSenguptaCombinatoriallyOrientable baseTriangulation →
      orientationSign = .negative → ∀ face, faceOrientationReversed face
  faceReparam_realizes_faceOrientation : ∀ face,
    if faceOrientationReversed face then
      ∀ side point,
        faceReparam face (senguptaCircleToClosedDisk
          (baseEmbedded.faceSideParam face side point)) =
        senguptaCircleToClosedDisk
          (targetEmbedded.faceSideParam (faceEquiv face)
            (Fin.rev side) (senguptaReverseClosedUnitInterval point))
    else
      ∀ side point,
        faceReparam face (senguptaCircleToClosedDisk
          (baseEmbedded.faceSideParam face side point)) =
        senguptaCircleToClosedDisk
          (targetEmbedded.faceSideParam (faceEquiv face) side point)
  homeomorphism_regionSet : ∀ region,
    surfaceHomeomorphism '' baseEmbedded.regionSet region =
      targetEmbedded.regionSet (regionEquiv region)

namespace TwoDimensionalSenguptaCellwiseEmbeddedHomeomorphismGeometryData

/-- Exact factor certificate for a parameterized cellwise geometry. This is the reusable analytic
surface needed when source and target fine presentations arise from preliminary subdivisions. -/
def HasFactorCertificate
    (geometry : TwoDimensionalSenguptaCellwiseEmbeddedHomeomorphismGeometryData
      (baseEmbedded := baseEmbedded) (targetEmbedded := targetEmbedded)) : Prop :=
  ∃ certificate : TwoDimensionalSenguptaHomeomorphismFactorInvarianceData
      (coverDensity := coverDensity) (source := baseTriangulation) (target := target)
      (bundleClass := bundleClass),
    certificate.orientationSign = geometry.orientationSign ∧
    certificate.faceOrientationReversed = geometry.faceOrientationReversed ∧
    certificate.externalEdgeEquiv = geometry.externalEdgeEquiv ∧
    certificate.internalEdgeEquiv = geometry.internalEdgeEquiv ∧
    certificate.faceEquiv = geometry.faceEquiv ∧
    certificate.regionEquiv = geometry.regionEquiv

end TwoDimensionalSenguptaCellwiseEmbeddedHomeomorphismGeometryData

/-- One arbitrary embedded homeomorphic target of the exact base presentation. -/
structure TwoDimensionalSenguptaEmbeddedHomeomorphismCandidateData where
  TargetEdge : Type uTargetEdge
  [targetEdgeFintype : Fintype TargetEdge]
  [targetEdgeDecidableEq : DecidableEq TargetEdge]
  TargetInternal : Type uTargetInternal
  [targetInternalFintype : Fintype TargetInternal]
  [targetInternalDecidableEq : DecidableEq TargetInternal]
  TargetFace : Type uTargetFace
  [targetFaceFintype : Fintype TargetFace]
  [targetFaceDecidableEq : DecidableEq TargetFace]
  TargetRegion : Type uTargetRegion
  [targetRegionFintype : Fintype TargetRegion]
  [targetRegionDecidableEq : DecidableEq TargetRegion]
  TargetSurface : Type uTargetSurface
  [targetSurfaceTopology : TopologicalSpace TargetSurface]
  [targetSurfaceCharted : ChartedSpace (EuclideanSpace ℝ (Fin 2)) TargetSurface]
  TargetVertex : Type uTargetVertex
  target : TwoDimensionalSenguptaTriangulatedRegionData
    TargetEdge TargetInternal TargetFace TargetRegion
  targetClosed : TwoDimensionalSenguptaClosedTriangularPresentationData
    (Vertex := TargetVertex) target
  targetEmbedded : TwoDimensionalSenguptaEmbeddedTriangularPresentationData
    (Surface := TargetSurface) (Curve := Curve) (closed := targetClosed)
  orientationSign : SenguptaHomeomorphismOrientationSign
  faceOrientationReversed : Face → Bool
  externalEdgeEquiv : Edge ≃ TargetEdge
  internalEdgeEquiv : InternalEdge ≃ TargetInternal
  faceEquiv : Face ≃ TargetFace
  regionEquiv : Region ≃ TargetRegion
  faceRegion_coherence : ∀ face,
    target.faceRegion (faceEquiv face) = regionEquiv (baseTriangulation.faceRegion face)
  regionArea_coherence : ∀ region,
    target.regionArea (regionEquiv region) = baseTriangulation.regionArea region
  boundaryWord_coherence : ∀ face,
    target.boundaryWord (faceEquiv face) =
      senguptaTransportedBoundaryWordByReversal (faceOrientationReversed face)
        (Sum.map externalEdgeEquiv internalEdgeEquiv) (baseTriangulation.boundaryWord face)
  targetCurveWord_eq_map : ∀ curve,
    targetEmbedded.curveWord curve =
      (baseEmbedded.curveWord curve).map (senguptaMapOrientedEdge externalEdgeEquiv)
  surfaceHomeomorphism : Surface ≃ₜ TargetSurface
  targetEdgeReparam : Sum Edge InternalEdge →
    SenguptaClosedUnitInterval ≃ₜ SenguptaClosedUnitInterval
  targetEdgeReparam_initial : ∀ edge, targetEdgeReparam edge ⟨0, by norm_num⟩ = ⟨0, by norm_num⟩
  targetEdgeReparam_terminal : ∀ edge, targetEdgeReparam edge ⟨1, by norm_num⟩ = ⟨1, by norm_num⟩
  homeomorphism_edgePath : ∀ edge point,
    surfaceHomeomorphism (baseEmbedded.edgePath edge point) =
      targetEmbedded.edgePath (Sum.map externalEdgeEquiv internalEdgeEquiv edge)
        (targetEdgeReparam edge point)
  vertexEquiv : Vertex ≃ TargetVertex
  homeomorphism_vertex : ∀ vertex,
    surfaceHomeomorphism (baseEmbedded.vertexPoint vertex) =
      targetEmbedded.vertexPoint (vertexEquiv vertex)
  faceReparam : Face → SenguptaClosedUnitDisk ≃ₜ SenguptaClosedUnitDisk
  homeomorphism_facePoint : ∀ face point,
    surfaceHomeomorphism (baseEmbedded.faceDisk face point) =
      targetEmbedded.faceDisk (faceEquiv face) (faceReparam face point)
  orientationSign_positive_iff :
    orientationSign = .positive ↔
      IsSenguptaCombinatoriallyOrientable baseTriangulation ∧
      ∀ face side point,
        faceReparam face (senguptaCircleToClosedDisk
          (baseEmbedded.faceSideParam face side point)) =
        senguptaCircleToClosedDisk
          (targetEmbedded.faceSideParam (faceEquiv face) side point)
  faceOrientationReversed_false_of_positive :
    orientationSign = .positive → ∀ face, ¬ faceOrientationReversed face
  faceOrientationReversed_true_of_orientable_negative :
    IsSenguptaCombinatoriallyOrientable baseTriangulation →
      orientationSign = .negative → ∀ face, faceOrientationReversed face
  faceReparam_realizes_faceOrientation : ∀ face,
    if faceOrientationReversed face then
      ∀ side point,
        faceReparam face (senguptaCircleToClosedDisk
          (baseEmbedded.faceSideParam face side point)) =
        senguptaCircleToClosedDisk
          (targetEmbedded.faceSideParam (faceEquiv face)
            (Fin.rev side) (senguptaReverseClosedUnitInterval point))
    else
      ∀ side point,
        faceReparam face (senguptaCircleToClosedDisk
          (baseEmbedded.faceSideParam face side point)) =
        senguptaCircleToClosedDisk
          (targetEmbedded.faceSideParam (faceEquiv face) side point)
  homeomorphism_regionSet : ∀ region,
    surfaceHomeomorphism '' baseEmbedded.regionSet region =
      targetEmbedded.regionSet (regionEquiv region)

namespace TwoDimensionalSenguptaEmbeddedHomeomorphismCandidateData

attribute [local instance] targetEdgeFintype targetEdgeDecidableEq
  targetInternalFintype targetInternalDecidableEq targetFaceFintype targetFaceDecidableEq
  targetRegionFintype targetRegionDecidableEq targetSurfaceTopology targetSurfaceCharted

/-- Forget bundling of the target carriers while retaining every exact cellwise geometric field. -/
noncomputable def toCellwiseGeometry
    (candidate : TwoDimensionalSenguptaEmbeddedHomeomorphismCandidateData
      (baseEmbedded := baseEmbedded)) :
    TwoDimensionalSenguptaCellwiseEmbeddedHomeomorphismGeometryData
      (baseEmbedded := baseEmbedded) (targetEmbedded := candidate.targetEmbedded) where
  orientationSign := candidate.orientationSign
  faceOrientationReversed := candidate.faceOrientationReversed
  externalEdgeEquiv := candidate.externalEdgeEquiv
  internalEdgeEquiv := candidate.internalEdgeEquiv
  faceEquiv := candidate.faceEquiv
  regionEquiv := candidate.regionEquiv
  faceRegion_coherence := candidate.faceRegion_coherence
  regionArea_coherence := candidate.regionArea_coherence
  boundaryWord_coherence := candidate.boundaryWord_coherence
  targetCurveWord_eq_map := candidate.targetCurveWord_eq_map
  surfaceHomeomorphism := candidate.surfaceHomeomorphism
  targetEdgeReparam := candidate.targetEdgeReparam
  targetEdgeReparam_initial := candidate.targetEdgeReparam_initial
  targetEdgeReparam_terminal := candidate.targetEdgeReparam_terminal
  homeomorphism_edgePath := candidate.homeomorphism_edgePath
  vertexEquiv := candidate.vertexEquiv
  homeomorphism_vertex := candidate.homeomorphism_vertex
  faceReparam := candidate.faceReparam
  homeomorphism_facePoint := candidate.homeomorphism_facePoint
  orientationSign_positive_iff := candidate.orientationSign_positive_iff
  faceOrientationReversed_false_of_positive :=
    candidate.faceOrientationReversed_false_of_positive
  faceOrientationReversed_true_of_orientable_negative :=
    candidate.faceOrientationReversed_true_of_orientable_negative
  faceReparam_realizes_faceOrientation := candidate.faceReparam_realizes_faceOrientation
  homeomorphism_regionSet := candidate.homeomorphism_regionSet

/-- Exact proposition that one geometric candidate has a factor certificate using the same sign and
all four exact equivalences. -/
def HasFactorCertificate
    (candidate : TwoDimensionalSenguptaEmbeddedHomeomorphismCandidateData
      (baseEmbedded := baseEmbedded)) : Prop :=
  candidate.toCellwiseGeometry.HasFactorCertificate
    (coverDensity := coverDensity) (bundleClass := bundleClass)

end TwoDimensionalSenguptaEmbeddedHomeomorphismCandidateData

/-- Universal acceptance over every concrete cellwise-compatible candidate at the stated universe
levels. This is not the full source class requiring preliminary subdivisions. -/
structure TwoDimensionalSenguptaUniversalCellwiseEmbeddedHomeomorphismData where
  candidate_nonempty : Nonempty
    (TwoDimensionalSenguptaEmbeddedHomeomorphismCandidateData.{uCurve, uEdge, uInternal,
      uFace, uRegion, uSurface, uVertex, uTargetEdge, uTargetInternal, uTargetFace,
      uTargetRegion, uTargetSurface, uTargetVertex} (baseEmbedded := baseEmbedded))
  nonorientable_bundleClass_involutive :
    ¬ IsSenguptaCombinatoriallyOrientable baseTriangulation → bundleClass = bundleClass⁻¹
  factorInvariant : ∀ candidate :
      TwoDimensionalSenguptaEmbeddedHomeomorphismCandidateData.{uCurve, uEdge, uInternal,
        uFace, uRegion, uSurface, uVertex, uTargetEdge, uTargetInternal, uTargetFace,
        uTargetRegion, uTargetSurface, uTargetVertex} (baseEmbedded := baseEmbedded),
    candidate.HasFactorCertificate (coverDensity := coverDensity) (bundleClass := bundleClass)

namespace TwoDimensionalSenguptaUniversalCellwiseEmbeddedHomeomorphismData

/-- Every concrete embedded homeomorphism candidate receives its matching factor certificate. -/
theorem certificate_for
    (data : TwoDimensionalSenguptaUniversalCellwiseEmbeddedHomeomorphismData.{uCover, uCurve, uEdge,
      uInternal, uFace, uRegion, uSurface, uVertex, uTargetEdge, uTargetInternal, uTargetFace,
      uTargetRegion, uTargetSurface, uTargetVertex}
      (baseEmbedded := baseEmbedded) (coverDensity := coverDensity)
      (bundleClass := bundleClass))
    (candidate : TwoDimensionalSenguptaEmbeddedHomeomorphismCandidateData.{uCurve, uEdge,
      uInternal, uFace, uRegion, uSurface, uVertex, uTargetEdge, uTargetInternal, uTargetFace,
      uTargetRegion, uTargetSurface, uTargetVertex} (baseEmbedded := baseEmbedded)) :
    candidate.HasFactorCertificate (coverDensity := coverDensity) (bundleClass := bundleClass) :=
  data.factorInvariant candidate

end TwoDimensionalSenguptaUniversalCellwiseEmbeddedHomeomorphismData

end

end YangMills.Dimensions
