/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Dimensions.TwoDimensionalSenguptaUniversalEmbeddedCurveBondSubdivision

/-! Hostile probes for universal embedded subdivisions that split curve bonds. -/

namespace YangMills.Dimensions.TwoDimensionalSenguptaUniversalEmbeddedCurveBondSubdivision.Probes

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
    {CoverGroup : Type uCover} [Group CoverGroup] [TopologicalSpace CoverGroup]
    [IsTopologicalGroup CoverGroup] [CompactSpace CoverGroup] [T2Space CoverGroup]
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
    (data : TwoDimensionalSenguptaUniversalEmbeddedCurveBondSubdivisionData.{uG, uCover,
      uGauge, uSample, uConnection, uCurve, uEdge, uInternal, uFace, uRegion,
      uSenguptaSample, uSurface, uBaseVertex, uSelectedFineInternal, uSelectedFineFace,
      uSelectedFineVertex, uTargetEdge, uTargetInternal, uTargetFace, uTargetRegion,
      uTargetVertex, uCandidateFineEdge, uCandidateFineInternal, uCandidateFineFace,
      uCandidateFineVertex}
      (embeddedFiniteLaw := embeddedFiniteLaw) (coverDensity := coverDensity))

omit [T2Space CoverGroup] [MeasurableMul₂ CoverGroup] [MeasurableInv CoverGroup]
    [Nonempty Curve] [Fintype TargetEdge] in
include data in
/-- The concrete geometric candidate class is nonempty. -/
theorem exact_candidate_nonempty : Nonempty
    (TwoDimensionalSenguptaEmbeddedCurveBondSubdivisionCandidateData.{uG, uCover,
      uGauge, uSample, uConnection, uCurve, uEdge, uInternal, uFace, uRegion,
      uSenguptaSample, uSurface, uBaseVertex, uSelectedFineInternal, uSelectedFineFace,
      uSelectedFineVertex, uTargetEdge, uTargetInternal, uTargetFace, uTargetRegion,
      uTargetVertex, uCandidateFineEdge, uCandidateFineInternal, uCandidateFineFace,
      uCandidateFineVertex} (embeddedFiniteLaw := embeddedFiniteLaw)) :=
  data.candidate_nonempty

omit [T2Space CoverGroup] [MeasurableMul₂ CoverGroup] [MeasurableInv CoverGroup]
    [Nonempty Curve] [Fintype TargetEdge] in
include data in
/-- Every geometric split-bond candidate receives the missing weighted pushforward certificate. -/
theorem exact_universal_certificate
    (candidate : TwoDimensionalSenguptaEmbeddedCurveBondSubdivisionCandidateData.{uG,
      uCover, uGauge, uSample, uConnection, uCurve, uEdge, uInternal, uFace, uRegion,
      uSenguptaSample, uSurface, uBaseVertex, uSelectedFineInternal, uSelectedFineFace,
      uSelectedFineVertex, uTargetEdge, uTargetInternal, uTargetFace, uTargetRegion,
      uTargetVertex, uCandidateFineEdge, uCandidateFineInternal, uCandidateFineFace,
      uCandidateFineVertex} (embeddedFiniteLaw := embeddedFiniteLaw)) :
    candidate.HasGraphMeasureCertificate
      (finiteLaw := finiteLaw) (coverDensity := coverDensity) :=
  data.certificate_for candidate

omit [T2Space CoverGroup] [MeasurableMul₂ CoverGroup] [MeasurableInv CoverGroup]
    [Nonempty Curve] [Fintype TargetEdge] in
/-- Fine nonorientability is connected to the base's exact fixed involutive twist. -/
theorem exact_fine_nonorientable_twist
    (candidate : TwoDimensionalSenguptaEmbeddedCurveBondSubdivisionCandidateData.{uG,
      uCover, uGauge, uSample, uConnection, uCurve, uEdge, uInternal, uFace, uRegion,
      uSenguptaSample, uSurface, uBaseVertex, uSelectedFineInternal, uSelectedFineFace,
      uSelectedFineVertex, uTargetEdge, uTargetInternal, uTargetFace, uTargetRegion,
      uTargetVertex, uCandidateFineEdge, uCandidateFineInternal, uCandidateFineFace,
      uCandidateFineVertex} (embeddedFiniteLaw := embeddedFiniteLaw))
    (fineNonorientable : ¬ candidate.FineOrientable) :
    finiteLaw.bundleClass = finiteLaw.bundleClass⁻¹ :=
  candidate.bundleClass_eq_inv_of_not_fineOrientable fineNonorientable

omit [T2Space CoverGroup] [MeasurableMul₂ CoverGroup] [MeasurableInv CoverGroup]
    [Nonempty Curve] [Fintype TargetEdge] in
/-- Hostile orientation probe: subdivision cannot change the surface's orientability class. -/
theorem changed_orientability_blocked
    (candidate : TwoDimensionalSenguptaEmbeddedCurveBondSubdivisionCandidateData.{uG,
      uCover, uGauge, uSample, uConnection, uCurve, uEdge, uInternal, uFace, uRegion,
      uSenguptaSample, uSurface, uBaseVertex, uSelectedFineInternal, uSelectedFineFace,
      uSelectedFineVertex, uTargetEdge, uTargetInternal, uTargetFace, uTargetRegion,
      uTargetVertex, uCandidateFineEdge, uCandidateFineInternal, uCandidateFineFace,
      uCandidateFineVertex} (embeddedFiniteLaw := embeddedFiniteLaw))
    (changed : ¬ (candidate.FineOrientable ↔
      IsSenguptaCombinatoriallyOrientable heatFactors.triangulation)) : False :=
  changed candidate.fineOrientable_iff_base

omit [T2Space CoverGroup] [MeasurableMul₂ CoverGroup] [MeasurableInv CoverGroup]
    [Nonempty Curve] [Fintype TargetEdge] in
include data in
/-- The universal certificate reconstructs the complete one-pair embedded heat-factor bridge. -/
theorem exact_bridge_reconstruction
    (candidate : TwoDimensionalSenguptaEmbeddedCurveBondSubdivisionCandidateData.{uG,
      uCover, uGauge, uSample, uConnection, uCurve, uEdge, uInternal, uFace, uRegion,
      uSenguptaSample, uSurface, uBaseVertex, uSelectedFineInternal, uSelectedFineFace,
      uSelectedFineVertex, uTargetEdge, uTargetInternal, uTargetFace, uTargetRegion,
      uTargetVertex, uCandidateFineEdge, uCandidateFineInternal, uCandidateFineFace,
      uCandidateFineVertex} (embeddedFiniteLaw := embeddedFiniteLaw)) : by
  letI : Fintype candidate.FineEdge := candidate.fineEdgeFintype
  letI : DecidableEq candidate.FineEdge := candidate.fineEdgeDecidableEq
  letI : Fintype candidate.FineInternal := candidate.fineInternalFintype
  letI : DecidableEq candidate.FineInternal := candidate.fineInternalDecidableEq
  letI : Fintype candidate.FineFace := candidate.fineFaceFintype
  letI : DecidableEq candidate.FineFace := candidate.fineFaceDecidableEq
  exact ∃ graphRefinement : TwoDimensionalSenguptaCurveBondGraphMeasureRefinementData
      (coarseLaw := finiteLaw)
      (coarseSource := fun edge => embeddedFiniteLaw.closedInvariance.baseClosed.edgeInitial
        (Sum.inl edge : Sum Edge InternalEdge))
      (coarseTarget := fun edge => embeddedFiniteLaw.closedInvariance.baseClosed.edgeTerminal
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
  exact candidate.exists_embeddedBridge_of_certificate (data.certificate_for candidate)

omit [T2Space CoverGroup] [MeasurableMul₂ CoverGroup] [MeasurableInv CoverGroup]
    [Nonempty Curve] [Fintype TargetEdge] in
include data in
/-- An empty candidate class cannot make the universal statement vacuous. -/
theorem empty_candidate_class_blocked
    (empty : IsEmpty
      (TwoDimensionalSenguptaEmbeddedCurveBondSubdivisionCandidateData.{uG, uCover,
        uGauge, uSample, uConnection, uCurve, uEdge, uInternal, uFace, uRegion,
        uSenguptaSample, uSurface, uBaseVertex, uSelectedFineInternal, uSelectedFineFace,
        uSelectedFineVertex, uTargetEdge, uTargetInternal, uTargetFace, uTargetRegion,
        uTargetVertex, uCandidateFineEdge, uCandidateFineInternal, uCandidateFineFace,
        uCandidateFineVertex} (embeddedFiniteLaw := embeddedFiniteLaw))) : False :=
  empty.false data.candidate_nonempty.some

omit [T2Space CoverGroup] [MeasurableMul₂ CoverGroup] [MeasurableInv CoverGroup]
    [Nonempty Curve] [Fintype TargetEdge] in
include data in
/-- Hostile universal probe: omitting one candidate's weighted certificate is rejected. -/
theorem missing_candidate_certificate_blocked
    (candidate : TwoDimensionalSenguptaEmbeddedCurveBondSubdivisionCandidateData.{uG,
      uCover, uGauge, uSample, uConnection, uCurve, uEdge, uInternal, uFace, uRegion,
      uSenguptaSample, uSurface, uBaseVertex, uSelectedFineInternal, uSelectedFineFace,
      uSelectedFineVertex, uTargetEdge, uTargetInternal, uTargetFace, uTargetRegion,
      uTargetVertex, uCandidateFineEdge, uCandidateFineInternal, uCandidateFineFace,
      uCandidateFineVertex} (embeddedFiniteLaw := embeddedFiniteLaw))
    (missing : ¬ candidate.HasGraphMeasureCertificate
      (finiteLaw := finiteLaw) (coverDensity := coverDensity)) : False :=
  missing (data.certificate_for candidate)

end

end YangMills.Dimensions.TwoDimensionalSenguptaUniversalEmbeddedCurveBondSubdivision.Probes
