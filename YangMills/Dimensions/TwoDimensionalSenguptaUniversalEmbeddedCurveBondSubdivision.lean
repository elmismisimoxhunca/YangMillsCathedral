/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Dimensions.TwoDimensionalSenguptaEmbeddedCurveBondGraphMeasureBridge

/-!
# Universal embedded Sengupta subdivisions with split curve bonds

A concrete candidate bundles one arbitrary embedded triangular subdivision of the exact finite-law
base, including literal curve-bond refinement and all face/path/region geometry, but no weighted
measure pushforward. Universal acceptance requires every such candidate to receive a normalized
equation-(8.3) graph-measure certificate whose fine weights are the candidate's exact
boundary-conditioned heat factors.

This remains an uninhabited acceptance surface at fixed universe levels. It does not prove the
heat-kernel integration argument, construct candidates, or claim full source-universe Fact 2.
-/

namespace YangMills.Dimensions

open MeasureTheory
open YangMills.Mathematics
open scoped ENNReal Manifold ContDiff

noncomputable section

universe uG uCover uGauge uSample uConnection uCurve uEdge uInternal uFace uRegion
  uSenguptaSample uSurface uBaseVertex
  uSelectedFineInternal uSelectedFineFace uSelectedFineVertex
  uTargetEdge uTargetInternal uTargetFace uTargetRegion uTargetVertex
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
    {CoverGroup : Type uCover} [Group CoverGroup]
    [TopologicalSpace CoverGroup] [IsTopologicalGroup CoverGroup]
    [CompactSpace CoverGroup] [T2Space CoverGroup]
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
    {SelectedFineInternal : Type uSelectedFineInternal}
      [Fintype SelectedFineInternal] [DecidableEq SelectedFineInternal]
    {SelectedFineFace : Type uSelectedFineFace}
      [Fintype SelectedFineFace] [DecidableEq SelectedFineFace]
    {SelectedFineVertex : Type uSelectedFineVertex}
    {selectedFine : TwoDimensionalSenguptaTriangulatedRegionData
      Edge SelectedFineInternal SelectedFineFace Region}
    {TargetEdge : Type uTargetEdge} [Fintype TargetEdge] [DecidableEq TargetEdge]
    {TargetInternal : Type uTargetInternal} [Fintype TargetInternal]
      [DecidableEq TargetInternal]
    {TargetFace : Type uTargetFace} [Fintype TargetFace] [DecidableEq TargetFace]
    {TargetRegion : Type uTargetRegion} [DecidableEq TargetRegion]
    {TargetVertex : Type uTargetVertex}
    {target : TwoDimensionalSenguptaTriangulatedRegionData
      TargetEdge TargetInternal TargetFace TargetRegion}
    {embeddedFiniteLaw : TwoDimensionalSenguptaEmbeddedFiniteLawBridgeData
      (heatFactors := heatFactors) (Surface := Surface) (BaseVertex := BaseVertex)
      (FineVertex := SelectedFineVertex) (fine := selectedFine)
      (TargetVertex := TargetVertex) (target := target)}

/-- One arbitrary source-geometric embedded subdivision, including split curve bonds but excluding
its analytic weighted-measure pushforward certificate. -/
structure TwoDimensionalSenguptaEmbeddedCurveBondSubdivisionCandidateData where
  FineEdge : Type uCandidateFineEdge
  [fineEdgeFintype : Fintype FineEdge]
  [fineEdgeDecidableEq : DecidableEq FineEdge]
  FineInternal : Type uCandidateFineInternal
  [fineInternalFintype : Fintype FineInternal]
  [fineInternalDecidableEq : DecidableEq FineInternal]
  FineFace : Type uCandidateFineFace
  [fineFaceFintype : Fintype FineFace]
  [fineFaceDecidableEq : DecidableEq FineFace]
  FineVertex : Type uCandidateFineVertex
  fine : TwoDimensionalSenguptaTriangulatedRegionData FineEdge FineInternal FineFace Region
  fineClosed : TwoDimensionalSenguptaClosedTriangularPresentationData
    (Vertex := FineVertex) fine
  fineEmbedded : TwoDimensionalSenguptaEmbeddedTriangularPresentationData
    (Surface := Surface) (Curve := Curve) (closed := fineClosed)
  fineCurveWord : Curve → List (OrientedEdge FineEdge)
  curveRefinement : TwoDimensionalSenguptaCurveBondRefinementData
    (coarseSource := fun edge =>
      embeddedFiniteLaw.closedInvariance.baseClosed.edgeInitial
        (Sum.inl edge : Sum Edge InternalEdge))
    (coarseTarget := fun edge =>
      embeddedFiniteLaw.closedInvariance.baseClosed.edgeTerminal
        (Sum.inl edge : Sum Edge InternalEdge))
    (fineSource := fun edge => fineClosed.edgeInitial
      (Sum.inl edge : Sum FineEdge FineInternal))
    (fineTarget := fun edge => fineClosed.edgeTerminal
      (Sum.inl edge : Sum FineEdge FineInternal))
    (coarseCurveWord := finiteLaw.curveWord) (fineCurveWord := fineCurveWord)
  geometry : TwoDimensionalSenguptaEmbeddedCurveBondSubdivisionGeometryData
    (embeddedFiniteLaw := embeddedFiniteLaw) (fine := fine) (fineClosed := fineClosed)
    (fineEmbedded := fineEmbedded) (curveRefinement := curveRefinement)

namespace TwoDimensionalSenguptaEmbeddedCurveBondSubdivisionCandidateData

/-- Exact proposition that a geometric candidate receives the missing normalized weighted
pushforward, with its fine weights fixed to the candidate's own heat factors. -/
def HasGraphMeasureCertificate
    (candidate : TwoDimensionalSenguptaEmbeddedCurveBondSubdivisionCandidateData
      (embeddedFiniteLaw := embeddedFiniteLaw)) : Prop := by
  letI : Fintype candidate.FineEdge := candidate.fineEdgeFintype
  letI : DecidableEq candidate.FineEdge := candidate.fineEdgeDecidableEq
  letI : Fintype candidate.FineInternal := candidate.fineInternalFintype
  letI : DecidableEq candidate.FineInternal := candidate.fineInternalDecidableEq
  letI : Fintype candidate.FineFace := candidate.fineFaceFintype
  letI : DecidableEq candidate.FineFace := candidate.fineFaceDecidableEq
  exact ∃ graphRefinement : TwoDimensionalSenguptaCurveBondGraphMeasureRefinementData
      (coarseLaw := finiteLaw)
      (coarseSource := fun edge =>
        embeddedFiniteLaw.closedInvariance.baseClosed.edgeInitial
          (Sum.inl edge : Sum Edge InternalEdge))
      (coarseTarget := fun edge =>
        embeddedFiniteLaw.closedInvariance.baseClosed.edgeTerminal
          (Sum.inl edge : Sum Edge InternalEdge))
      (fineSource := fun edge => candidate.fineClosed.edgeInitial
        (Sum.inl edge : Sum candidate.FineEdge candidate.FineInternal))
      (fineTarget := fun edge => candidate.fineClosed.edgeTerminal
        (Sum.inl edge : Sum candidate.FineEdge candidate.FineInternal))
      (fineCurveWord := candidate.fineCurveWord),
    graphRefinement.curveRefinement = candidate.curveRefinement ∧
    (∀ region external,
      graphRefinement.fineOrdinaryRegionWeight region external =
        senguptaTriangulatedRegionFactor candidate.fine coverDensity region external) ∧
    (∀ region external,
      graphRefinement.fineTwistedRegionWeight finiteLaw.bundleClass region external =
        senguptaTriangulatedTwistedRegionFactor candidate.fine coverDensity
          finiteLaw.bundleClass region external)

omit [T2Space CoverGroup] [MeasurableMul₂ CoverGroup] [MeasurableInv CoverGroup]
    [Nonempty Curve] [Fintype TargetEdge] in
/-- Orientability of the candidate's own fine triangulation, with its bundled finite instances. -/
def FineOrientable
    (candidate : TwoDimensionalSenguptaEmbeddedCurveBondSubdivisionCandidateData
      (embeddedFiniteLaw := embeddedFiniteLaw)) : Prop := by
  letI : Fintype candidate.FineEdge := candidate.fineEdgeFintype
  letI : DecidableEq candidate.FineEdge := candidate.fineEdgeDecidableEq
  letI : Fintype candidate.FineInternal := candidate.fineInternalFintype
  letI : DecidableEq candidate.FineInternal := candidate.fineInternalDecidableEq
  letI : Fintype candidate.FineFace := candidate.fineFaceFintype
  letI : DecidableEq candidate.FineFace := candidate.fineFaceDecidableEq
  exact IsSenguptaCombinatoriallyOrientable candidate.fine

omit [T2Space CoverGroup] [MeasurableMul₂ CoverGroup] [MeasurableInv CoverGroup]
    [Nonempty Curve] [Fintype TargetEdge] in
/-- Candidate orientability is exactly the base embedded surface's orientability class. -/
theorem fineOrientable_iff_base
    (candidate : TwoDimensionalSenguptaEmbeddedCurveBondSubdivisionCandidateData
      (embeddedFiniteLaw := embeddedFiniteLaw)) :
    candidate.FineOrientable ↔
      IsSenguptaCombinatoriallyOrientable heatFactors.triangulation := by
  letI : Fintype candidate.FineEdge := candidate.fineEdgeFintype
  letI : DecidableEq candidate.FineEdge := candidate.fineEdgeDecidableEq
  letI : Fintype candidate.FineInternal := candidate.fineInternalFintype
  letI : DecidableEq candidate.FineInternal := candidate.fineInternalDecidableEq
  letI : Fintype candidate.FineFace := candidate.fineFaceFintype
  letI : DecidableEq candidate.FineFace := candidate.fineFaceDecidableEq
  dsimp [FineOrientable]
  exact candidate.geometry.fine_orientable_iff_base

omit [T2Space CoverGroup] [MeasurableMul₂ CoverGroup] [MeasurableInv CoverGroup]
    [Nonempty Curve] [Fintype TargetEdge] in
/-- A nonorientable fine candidate forces the exact fixed bundle class to be involutive. -/
theorem bundleClass_eq_inv_of_not_fineOrientable
    (candidate : TwoDimensionalSenguptaEmbeddedCurveBondSubdivisionCandidateData
      (embeddedFiniteLaw := embeddedFiniteLaw))
    (fineNonorientable : ¬ candidate.FineOrientable) :
    finiteLaw.bundleClass = finiteLaw.bundleClass⁻¹ := by
  apply embeddedFiniteLaw.nonorientable_bundleClass_involutive
  intro baseOrientable
  exact fineNonorientable (candidate.fineOrientable_iff_base.mpr baseOrientable)

omit [T2Space CoverGroup] [MeasurableMul₂ CoverGroup] [MeasurableInv CoverGroup]
    [Nonempty Curve] [Fintype TargetEdge] in
/-- Every graph-measure certificate canonically recovers the one-pair embedded heat-factor bridge. -/
theorem exists_embeddedBridge_of_certificate
    (candidate : TwoDimensionalSenguptaEmbeddedCurveBondSubdivisionCandidateData
      (embeddedFiniteLaw := embeddedFiniteLaw))
    (certificate : candidate.HasGraphMeasureCertificate
      (finiteLaw := finiteLaw) (coverDensity := coverDensity)) : by
  letI : Fintype candidate.FineEdge := candidate.fineEdgeFintype
  letI : DecidableEq candidate.FineEdge := candidate.fineEdgeDecidableEq
  letI : Fintype candidate.FineInternal := candidate.fineInternalFintype
  letI : DecidableEq candidate.FineInternal := candidate.fineInternalDecidableEq
  letI : Fintype candidate.FineFace := candidate.fineFaceFintype
  letI : DecidableEq candidate.FineFace := candidate.fineFaceDecidableEq
  exact ∃ graphRefinement : TwoDimensionalSenguptaCurveBondGraphMeasureRefinementData
      (coarseLaw := finiteLaw)
      (coarseSource := fun edge =>
        embeddedFiniteLaw.closedInvariance.baseClosed.edgeInitial
          (Sum.inl edge : Sum Edge InternalEdge))
      (coarseTarget := fun edge =>
        embeddedFiniteLaw.closedInvariance.baseClosed.edgeTerminal
          (Sum.inl edge : Sum Edge InternalEdge))
      (fineSource := fun edge => candidate.fineClosed.edgeInitial
        (Sum.inl edge : Sum candidate.FineEdge candidate.FineInternal))
      (fineTarget := fun edge => candidate.fineClosed.edgeTerminal
        (Sum.inl edge : Sum candidate.FineEdge candidate.FineInternal))
      (fineCurveWord := candidate.fineCurveWord),
    Nonempty (TwoDimensionalSenguptaEmbeddedCurveBondGraphMeasureBridgeData
      (embeddedFiniteLaw := embeddedFiniteLaw) (fine := candidate.fine)
      (fineClosed := candidate.fineClosed) (fineEmbedded := candidate.fineEmbedded)
      (graphRefinement := graphRefinement)) := by
  letI : Fintype candidate.FineEdge := candidate.fineEdgeFintype
  letI : DecidableEq candidate.FineEdge := candidate.fineEdgeDecidableEq
  letI : Fintype candidate.FineInternal := candidate.fineInternalFintype
  letI : DecidableEq candidate.FineInternal := candidate.fineInternalDecidableEq
  letI : Fintype candidate.FineFace := candidate.fineFaceFintype
  letI : DecidableEq candidate.FineFace := candidate.fineFaceDecidableEq
  dsimp [HasGraphMeasureCertificate] at certificate
  rcases certificate with ⟨graphRefinement, curve_eq, ordinary_eq, twisted_eq⟩
  refine ⟨graphRefinement, ?_⟩
  have transportedGeometry :
      TwoDimensionalSenguptaEmbeddedCurveBondSubdivisionGeometryData
        (embeddedFiniteLaw := embeddedFiniteLaw) (fine := candidate.fine)
        (fineClosed := candidate.fineClosed) (fineEmbedded := candidate.fineEmbedded)
        (curveRefinement := graphRefinement.curveRefinement) := by
    rw [curve_eq]
    exact candidate.geometry
  exact ⟨{
    toTwoDimensionalSenguptaEmbeddedCurveBondSubdivisionGeometryData := transportedGeometry
    fineOrdinaryRegionWeight_eq := ordinary_eq
    fineTwistedRegionWeight_eq := twisted_eq
  }⟩

end TwoDimensionalSenguptaEmbeddedCurveBondSubdivisionCandidateData

/-- Universal acceptance over the concrete source-geometric split-curve-bond subdivision class.
Candidate nonemptiness prevents vacuous universal quantification. -/
structure TwoDimensionalSenguptaUniversalEmbeddedCurveBondSubdivisionData where
  candidate_nonempty : Nonempty
    (TwoDimensionalSenguptaEmbeddedCurveBondSubdivisionCandidateData.{uG, uCover, uGauge,
      uSample, uConnection, uCurve, uEdge, uInternal, uFace, uRegion, uSenguptaSample,
      uSurface, uBaseVertex, uSelectedFineInternal, uSelectedFineFace, uSelectedFineVertex,
      uTargetEdge, uTargetInternal, uTargetFace, uTargetRegion, uTargetVertex,
      uCandidateFineEdge, uCandidateFineInternal, uCandidateFineFace, uCandidateFineVertex}
      (embeddedFiniteLaw := embeddedFiniteLaw))
  weightedInvariant : ∀ candidate :
      TwoDimensionalSenguptaEmbeddedCurveBondSubdivisionCandidateData.{uG, uCover, uGauge,
        uSample, uConnection, uCurve, uEdge, uInternal, uFace, uRegion, uSenguptaSample,
        uSurface, uBaseVertex, uSelectedFineInternal, uSelectedFineFace, uSelectedFineVertex,
        uTargetEdge, uTargetInternal, uTargetFace, uTargetRegion, uTargetVertex,
        uCandidateFineEdge, uCandidateFineInternal, uCandidateFineFace, uCandidateFineVertex}
        (embeddedFiniteLaw := embeddedFiniteLaw),
    candidate.HasGraphMeasureCertificate
      (finiteLaw := finiteLaw) (coverDensity := coverDensity)

namespace TwoDimensionalSenguptaUniversalEmbeddedCurveBondSubdivisionData

omit [T2Space CoverGroup] [MeasurableMul₂ CoverGroup] [MeasurableInv CoverGroup]
    [Nonempty Curve] [Fintype TargetEdge] in
/-- Every concrete source-geometric split-bond candidate receives the exact weighted certificate. -/
theorem certificate_for
    (data : TwoDimensionalSenguptaUniversalEmbeddedCurveBondSubdivisionData.{uG, uCover,
      uGauge, uSample, uConnection, uCurve, uEdge, uInternal, uFace, uRegion,
      uSenguptaSample, uSurface, uBaseVertex, uSelectedFineInternal, uSelectedFineFace,
      uSelectedFineVertex, uTargetEdge, uTargetInternal, uTargetFace, uTargetRegion,
      uTargetVertex, uCandidateFineEdge, uCandidateFineInternal, uCandidateFineFace,
      uCandidateFineVertex}
      (embeddedFiniteLaw := embeddedFiniteLaw) (coverDensity := coverDensity))
    (candidate : TwoDimensionalSenguptaEmbeddedCurveBondSubdivisionCandidateData.{uG, uCover,
      uGauge, uSample, uConnection, uCurve, uEdge, uInternal, uFace, uRegion,
      uSenguptaSample, uSurface, uBaseVertex, uSelectedFineInternal, uSelectedFineFace,
      uSelectedFineVertex, uTargetEdge, uTargetInternal, uTargetFace, uTargetRegion,
      uTargetVertex, uCandidateFineEdge, uCandidateFineInternal, uCandidateFineFace,
      uCandidateFineVertex} (embeddedFiniteLaw := embeddedFiniteLaw)) :
    candidate.HasGraphMeasureCertificate
      (finiteLaw := finiteLaw) (coverDensity := coverDensity) :=
  data.weightedInvariant candidate

end TwoDimensionalSenguptaUniversalEmbeddedCurveBondSubdivisionData

end

end YangMills.Dimensions
