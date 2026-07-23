/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Dimensions.TwoDimensionalSenguptaEmbeddedFiniteLawBridge

/-!
# Geometric realization of one Sengupta subdivision and homeomorphism comparison

This layer upgrades the selected one-pair Facts 2--3 certificates from combinatorial closed
presentations to embedded comparisons. The fine presentation subdivides the exact base on the same
surface. The transported presentation lies on a second surface related by an explicit homeomorphism.
Curve words, edge/face images, vertices, and complement regions commute with these maps.

It remains an uninhabited one-pair bridge, not universal Facts 2--3.
-/

namespace YangMills.Dimensions

open YangMills.Mathematics
open scoped ENNReal Manifold ContDiff

noncomputable section

/-- Consecutive fine embedded edges meet with their stored orientations. -/
def IsSenguptaComposableEmbeddedPath
    {Edge Surface : Type*} (edgePath : Edge → SenguptaClosedUnitInterval → Surface) :
    List (OrientedEdge Edge) → Prop
  | [] => True
  | [_] => True
  | first :: second :: rest =>
      senguptaOrientedEmbeddedEdgePath edgePath first ⟨1, by norm_num⟩ =
        senguptaOrientedEmbeddedEdgePath edgePath second ⟨0, by norm_num⟩ ∧
      IsSenguptaComposableEmbeddedPath edgePath (second :: rest)

/-- A coarse embedded edge is realized by one nonempty composable oriented fine-edge word, with exact
trace and directed endpoints. This is the geometric bond-subdivision relation used below. -/
def IsSenguptaEmbeddedPathSubdivision
    {CoarseEdge FineEdge Surface : Type*}
    (coarsePath : CoarseEdge → SenguptaClosedUnitInterval → Surface)
    (finePath : FineEdge → SenguptaClosedUnitInterval → Surface)
    (coarseEdge : CoarseEdge) (word : List (OrientedEdge FineEdge)) : Prop :=
  word ≠ [] ∧ (word.map OrientedEdge.underlying).Nodup ∧
  IsSenguptaComposableEmbeddedPath finePath word ∧
  Set.range (coarsePath coarseEdge) =
    ⋃ (oriented : OrientedEdge FineEdge) (_ : oriented ∈ word),
      Set.range (senguptaOrientedEmbeddedEdgePath finePath oriented) ∧
  ∃ first last,
    word.head? = some first ∧ word.getLast? = some last ∧
    senguptaOrientedEmbeddedEdgePath finePath first ⟨0, by norm_num⟩ =
      coarsePath coarseEdge ⟨0, by norm_num⟩ ∧
    senguptaOrientedEmbeddedEdgePath finePath last ⟨1, by norm_num⟩ =
      coarsePath coarseEdge ⟨1, by norm_num⟩

/-- Substitute one oriented coarse traversal by its directed fine-edge word. -/
def senguptaSubstituteOrientedEdge
    {CoarseEdge FineEdge : Type*}
    (edgeWord : CoarseEdge → List (OrientedEdge FineEdge)) :
    OrientedEdge CoarseEdge → List (OrientedEdge FineEdge)
  | .forward edge => edgeWord edge
  | .reverse edge => reverseFiniteOrientedWord (edgeWord edge)

/-- Substitute every traversal in a coarse word. -/
def senguptaSubstituteOrientedWord
    {CoarseEdge FineEdge : Type*}
    (edgeWord : CoarseEdge → List (OrientedEdge FineEdge))
    (word : List (OrientedEdge CoarseEdge)) : List (OrientedEdge FineEdge) :=
  word.flatMap (senguptaSubstituteOrientedEdge edgeWord)

/-- Signed incidence of one underlying edge in an oriented word. -/
def senguptaOrientedWordSignedIncidence
    {Edge : Type*} [DecidableEq Edge] (edge : Edge)
    (word : List (OrientedEdge Edge)) : ℤ :=
  (word.count (.forward edge) : ℤ) - (word.count (.reverse edge) : ℤ)

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
    {TargetSurface : Type uTargetSurface} [TopologicalSpace TargetSurface]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) TargetSurface]
    {embeddedFiniteLaw : TwoDimensionalSenguptaEmbeddedFiniteLawBridgeData
      (heatFactors := heatFactors) (Surface := Surface) (BaseVertex := BaseVertex)
      (FineVertex := FineVertex) (fine := fine)
      (TargetVertex := TargetVertex) (target := target)}

/-- Embedded geometric coherence for the selected Fact 2 refinement and Fact 3 homeomorphism. -/
structure TwoDimensionalSenguptaEmbeddedComparisonBridgeData where
  embeddedFine : TwoDimensionalSenguptaEmbeddedTriangularPresentationData
    (Surface := Surface) (Curve := Curve)
    (closed := embeddedFiniteLaw.closedInvariance.fineClosed)
  embeddedTarget : TwoDimensionalSenguptaEmbeddedTriangularPresentationData
    (Surface := TargetSurface) (Curve := Curve)
    (closed := embeddedFiniteLaw.closedInvariance.targetClosed)
  fineCurveWord_eq_base : embeddedFine.curveWord = embeddedFiniteLaw.embeddedBase.curveWord
  targetCurveWord_eq_map : ∀ curve,
    embeddedTarget.curveWord curve =
      (embeddedFiniteLaw.embeddedBase.curveWord curve).map
        (senguptaMapOrientedEdge
          embeddedFiniteLaw.closedInvariance.invariance.homeomorphism.externalEdgeEquiv)
  /-- Fine closed faces partition the exact coarse embedded face images. -/
  fineFaceImage_subset : ∀ fineFace,
    Set.range (embeddedFine.faceDisk fineFace) ⊆
      Set.range (embeddedFiniteLaw.embeddedBase.faceDisk
        (embeddedFiniteLaw.closedInvariance.invariance.subdivision.fineFaceToCoarse fineFace))
  coarseFaceImage_eq_fine_union : ∀ coarseFace,
    Set.range (embeddedFiniteLaw.embeddedBase.faceDisk coarseFace) =
      ⋃ (fineFace : FineFace)
        (_ : embeddedFiniteLaw.closedInvariance.invariance.subdivision.fineFaceToCoarse fineFace =
          coarseFace), Set.range (embeddedFine.faceDisk fineFace)
  baseVertexToFine : BaseVertex → FineVertex
  baseVertexToFine_injective : Function.Injective baseVertexToFine
  baseVertexToFine_point : ∀ vertex,
    embeddedFine.vertexPoint (baseVertexToFine vertex) =
      embeddedFiniteLaw.embeddedBase.vertexPoint vertex
  fineExternalEdgePath_eq : ∀ (edge : Edge) (point : SenguptaClosedUnitInterval),
    embeddedFine.edgePath (Sum.inl edge) point =
      embeddedFiniteLaw.embeddedBase.edgePath (Sum.inl edge) point
  coarseEdgeToFineWord : Sum Edge InternalEdge →
    List (OrientedEdge (Sum Edge FineInternal))
  coarseEdgeToFineWord_realizes : ∀ edge,
    IsSenguptaEmbeddedPathSubdivision embeddedFiniteLaw.embeddedBase.edgePath
      embeddedFine.edgePath edge (coarseEdgeToFineWord edge)
  /-- Substituting the directed coarse bond words gives exactly the oriented outer boundary of the
  assigned fine faces after cancellation of their internal edges. -/
  coarseFaceBoundary_signedChain_eq : ∀ (coarseFace : Face)
      (fineEdge : Sum Edge FineInternal),
    senguptaOrientedWordSignedIncidence fineEdge
      (senguptaSubstituteOrientedWord coarseEdgeToFineWord
        (heatFactors.triangulation.boundaryWord coarseFace)) =
    ∑ fineFace ∈ Finset.univ.filter (fun fineFace =>
        embeddedFiniteLaw.closedInvariance.invariance.subdivision.fineFaceToCoarse fineFace =
          coarseFace),
      senguptaOrientedWordSignedIncidence fineEdge (fine.boundaryWord fineFace)
  fineRegionSet_eq : ∀ region : Region,
    embeddedFine.regionSet region = embeddedFiniteLaw.embeddedBase.regionSet region
  surfaceHomeomorphism : Surface ≃ₜ TargetSurface
  targetEdgeReparam : Sum Edge InternalEdge →
    SenguptaClosedUnitInterval ≃ₜ SenguptaClosedUnitInterval
  targetEdgeReparam_initial : ∀ edge, targetEdgeReparam edge ⟨0, by norm_num⟩ = ⟨0, by norm_num⟩
  targetEdgeReparam_terminal : ∀ edge, targetEdgeReparam edge ⟨1, by norm_num⟩ = ⟨1, by norm_num⟩
  homeomorphism_edgePath : ∀ edge point,
    surfaceHomeomorphism (embeddedFiniteLaw.embeddedBase.edgePath edge point) =
      embeddedTarget.edgePath
        (Sum.map
          embeddedFiniteLaw.closedInvariance.invariance.homeomorphism.externalEdgeEquiv
          embeddedFiniteLaw.closedInvariance.invariance.homeomorphism.internalEdgeEquiv edge)
        (targetEdgeReparam edge point)
  vertexEquiv : BaseVertex ≃ TargetVertex
  homeomorphism_vertex : ∀ vertex,
    surfaceHomeomorphism (embeddedFiniteLaw.embeddedBase.vertexPoint vertex) =
      embeddedTarget.vertexPoint (vertexEquiv vertex)
  homeomorphism_edgeImage : ∀ edge : Sum Edge InternalEdge,
    surfaceHomeomorphism ''
      Set.range (embeddedFiniteLaw.embeddedBase.edgePath edge) =
      Set.range (embeddedTarget.edgePath
        (Sum.map
          embeddedFiniteLaw.closedInvariance.invariance.homeomorphism.externalEdgeEquiv
          embeddedFiniteLaw.closedInvariance.invariance.homeomorphism.internalEdgeEquiv edge))
  faceReparam : Face → SenguptaClosedUnitDisk ≃ₜ SenguptaClosedUnitDisk
  homeomorphism_facePoint : ∀ face point,
    surfaceHomeomorphism (embeddedFiniteLaw.embeddedBase.faceDisk face point) =
      embeddedTarget.faceDisk
        (embeddedFiniteLaw.closedInvariance.invariance.homeomorphism.faceEquiv face)
        (faceReparam face point)
  /-- Sengupta's exact sign rule: positive means that the source complex is orientable and the
  actual marked-boundary action preserves cyclic side order and direction. -/
  orientationSign_positive_iff :
    embeddedFiniteLaw.closedInvariance.invariance.homeomorphism.orientationSign = .positive ↔
      IsSenguptaCombinatoriallyOrientable heatFactors.triangulation ∧
      ∀ face side point,
        faceReparam face (senguptaCircleToClosedDisk
          (embeddedFiniteLaw.embeddedBase.faceSideParam face side point)) =
        senguptaCircleToClosedDisk
          (embeddedTarget.faceSideParam
            (embeddedFiniteLaw.closedInvariance.invariance.homeomorphism.faceEquiv face)
            side point)
  faceOrientationReversed_false_of_positive :
    embeddedFiniteLaw.closedInvariance.invariance.homeomorphism.orientationSign = .positive →
      ∀ face, ¬ embeddedFiniteLaw.closedInvariance.invariance.homeomorphism.faceOrientationReversed
        face
  faceOrientationReversed_true_of_orientable_negative :
    IsSenguptaCombinatoriallyOrientable heatFactors.triangulation →
    embeddedFiniteLaw.closedInvariance.invariance.homeomorphism.orientationSign = .negative →
      ∀ face, embeddedFiniteLaw.closedInvariance.invariance.homeomorphism.faceOrientationReversed
        face
  /-- Actual disk-boundary behavior follows the independently selected simplex orientation. On a
  nonorientable source this need not reverse merely because the global `h` sign is negative. -/
  faceReparam_realizes_faceOrientation : ∀ face,
    if embeddedFiniteLaw.closedInvariance.invariance.homeomorphism.faceOrientationReversed face then
      ∀ side point,
        faceReparam face (senguptaCircleToClosedDisk
          (embeddedFiniteLaw.embeddedBase.faceSideParam face side point)) =
        senguptaCircleToClosedDisk
          (embeddedTarget.faceSideParam
            (embeddedFiniteLaw.closedInvariance.invariance.homeomorphism.faceEquiv face)
            (Fin.rev side) (senguptaReverseClosedUnitInterval point))
    else
      ∀ side point,
        faceReparam face (senguptaCircleToClosedDisk
          (embeddedFiniteLaw.embeddedBase.faceSideParam face side point)) =
        senguptaCircleToClosedDisk
          (embeddedTarget.faceSideParam
            (embeddedFiniteLaw.closedInvariance.invariance.homeomorphism.faceEquiv face)
            side point)
  homeomorphism_faceImage : ∀ face : Face,
    surfaceHomeomorphism ''
      Set.range (embeddedFiniteLaw.embeddedBase.faceDisk face) =
      Set.range (embeddedTarget.faceDisk
        (embeddedFiniteLaw.closedInvariance.invariance.homeomorphism.faceEquiv face))
  homeomorphism_regionSet : ∀ region : Region,
    surfaceHomeomorphism '' embeddedFiniteLaw.embeddedBase.regionSet region =
      embeddedTarget.regionSet
        (embeddedFiniteLaw.closedInvariance.invariance.homeomorphism.regionEquiv region)

namespace TwoDimensionalSenguptaEmbeddedComparisonBridgeData

omit [T2Space CoverGroup] [Nonempty Curve] [Fintype TargetEdge] in
/-- Exact dependency projection for the embedded fine presentation. -/
noncomputable def exact_embeddedFine
    (data : TwoDimensionalSenguptaEmbeddedComparisonBridgeData
      (embeddedFiniteLaw := embeddedFiniteLaw) (TargetSurface := TargetSurface)) :
    TwoDimensionalSenguptaEmbeddedTriangularPresentationData
      (Surface := Surface) (Curve := Curve)
      (closed := embeddedFiniteLaw.closedInvariance.fineClosed) :=
  data.embeddedFine

omit [T2Space CoverGroup] [Nonempty Curve] [Fintype TargetEdge] in
/-- Exact dependency projection for the transported presentation. -/
noncomputable def exact_embeddedTarget
    (data : TwoDimensionalSenguptaEmbeddedComparisonBridgeData
      (embeddedFiniteLaw := embeddedFiniteLaw) (TargetSurface := TargetSurface)) :
    TwoDimensionalSenguptaEmbeddedTriangularPresentationData
      (Surface := TargetSurface) (Curve := Curve)
      (closed := embeddedFiniteLaw.closedInvariance.targetClosed) :=
  data.embeddedTarget

end TwoDimensionalSenguptaEmbeddedComparisonBridgeData

end

end YangMills.Dimensions
