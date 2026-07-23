/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Dimensions.TwoDimensionalSenguptaUniversalCellwiseEmbeddedHomeomorphism

/-! Hostile probes for the universal cellwise-compatible embedded homeomorphism subclass. -/

namespace YangMills.Dimensions.TwoDimensionalSenguptaUniversalCellwiseEmbeddedHomeomorphism.Probes

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
    (data : TwoDimensionalSenguptaUniversalCellwiseEmbeddedHomeomorphismData.{uCover, uCurve,
      uEdge, uInternal, uFace, uRegion, uSurface, uVertex, uTargetEdge, uTargetInternal,
      uTargetFace, uTargetRegion, uTargetSurface, uTargetVertex}
      (baseEmbedded := baseEmbedded) (coverDensity := coverDensity)
      (bundleClass := bundleClass))

include data in
/-- The concrete embedded-homeomorphism candidate class is nonempty. -/
theorem exact_candidate_nonempty : Nonempty
    (TwoDimensionalSenguptaEmbeddedHomeomorphismCandidateData.{uCurve, uEdge, uInternal,
      uFace, uRegion, uSurface, uVertex, uTargetEdge, uTargetInternal, uTargetFace,
      uTargetRegion, uTargetSurface, uTargetVertex} (baseEmbedded := baseEmbedded)) :=
  data.candidate_nonempty

include data in
/-- Every arbitrary concrete target/homeomorphism candidate receives its matching factor theorem. -/
theorem exact_universal_certificate
    (candidate : TwoDimensionalSenguptaEmbeddedHomeomorphismCandidateData.{uCurve, uEdge,
      uInternal, uFace, uRegion, uSurface, uVertex, uTargetEdge, uTargetInternal,
      uTargetFace, uTargetRegion, uTargetSurface, uTargetVertex}
      (baseEmbedded := baseEmbedded)) :
    candidate.HasFactorCertificate (coverDensity := coverDensity) (bundleClass := bundleClass) :=
  data.factorInvariant candidate

include data in
/-- Failure at any one exact candidate blocks cellwise-compatible universal acceptance. -/
theorem missing_one_candidate_certificate_blocks
    (candidate : TwoDimensionalSenguptaEmbeddedHomeomorphismCandidateData.{uCurve, uEdge,
      uInternal, uFace, uRegion, uSurface, uVertex, uTargetEdge, uTargetInternal,
      uTargetFace, uTargetRegion, uTargetSurface, uTargetVertex}
      (baseEmbedded := baseEmbedded))
    (missing : ¬ candidate.HasFactorCertificate
      (coverDensity := coverDensity) (bundleClass := bundleClass)) : False :=
  missing (data.factorInvariant candidate)

include data in
/-- An empty geometric candidate class cannot make the universal statement vacuous. -/
theorem empty_candidate_class_blocks
    (empty : IsEmpty
      (TwoDimensionalSenguptaEmbeddedHomeomorphismCandidateData.{uCurve, uEdge, uInternal,
        uFace, uRegion, uSurface, uVertex, uTargetEdge, uTargetInternal, uTargetFace,
        uTargetRegion, uTargetSurface, uTargetVertex} (baseEmbedded := baseEmbedded))) : False :=
  empty.false data.candidate_nonempty.some

include data in
/-- The universal interface retains the nonorientable fixed-twist condition. -/
theorem exact_nonorientable_twist
    (nonorientable : ¬ IsSenguptaCombinatoriallyOrientable baseTriangulation) :
    bundleClass = bundleClass⁻¹ :=
  data.nonorientable_bundleClass_involutive nonorientable

end

end YangMills.Dimensions.TwoDimensionalSenguptaUniversalCellwiseEmbeddedHomeomorphism.Probes
