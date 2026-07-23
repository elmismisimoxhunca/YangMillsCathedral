/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Dimensions.TwoDimensionalSenguptaUniversalCurveFixedEmbeddedSubdivision

/-! Hostile probes for universal curve-fixed embedded Sengupta subdivision acceptance. -/

namespace YangMills.Dimensions.TwoDimensionalSenguptaUniversalCurveFixedEmbeddedSubdivision.Probes

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
    (data : TwoDimensionalSenguptaUniversalCurveFixedEmbeddedSubdivisionData.{uCover, uCurve, uEdge,
      uInternal, uFace, uRegion, uSurface, uVertex, uFineInternal, uFineFace, uFineVertex}
      (baseEmbedded := baseEmbedded) (coverDensity := coverDensity)
      (bundleClass := bundleClass))

include data in
/-- The quantified geometric candidate class is explicitly nonempty. -/
theorem exact_candidate_nonempty :
    Nonempty (TwoDimensionalSenguptaEmbeddedSubdivisionCandidateData.{uCurve, uEdge,
      uInternal, uFace, uRegion, uSurface, uVertex, uFineInternal, uFineFace, uFineVertex}
      (baseEmbedded := baseEmbedded)) :=
  data.candidate_nonempty

include data in
/-- Every arbitrary candidate in the concrete curve-fixed embedded subclass receives an exact factor certificate. -/
theorem exact_universal_certificate
    (candidate : TwoDimensionalSenguptaEmbeddedSubdivisionCandidateData.{uCurve, uEdge,
      uInternal, uFace, uRegion, uSurface, uVertex, uFineInternal, uFineFace, uFineVertex}
      (baseEmbedded := baseEmbedded)) :
    candidate.HasFactorCertificate (coverDensity := coverDensity) (bundleClass := bundleClass) :=
  data.factorInvariant candidate

include data in
/-- Hostile universal probe: failure at any one geometric candidate blocks acceptance. -/
theorem missing_one_candidate_certificate_blocks
    (candidate : TwoDimensionalSenguptaEmbeddedSubdivisionCandidateData.{uCurve, uEdge,
      uInternal, uFace, uRegion, uSurface, uVertex, uFineInternal, uFineFace, uFineVertex}
      (baseEmbedded := baseEmbedded))
    (missing : ¬ candidate.HasFactorCertificate
      (coverDensity := coverDensity) (bundleClass := bundleClass)) : False :=
  missing (data.factorInvariant candidate)

include data in
/-- The exact nonorientable base forces the same fixed twist to be involutive. -/
theorem exact_nonorientable_twist
    (nonorientable : ¬ IsSenguptaCombinatoriallyOrientable baseTriangulation) :
    bundleClass = bundleClass⁻¹ :=
  data.nonorientable_bundleClass_involutive nonorientable

include data in
/-- Hostile nonorientable twist probe. -/
theorem changed_nonorientable_twist_blocks
    (nonorientable : ¬ IsSenguptaCombinatoriallyOrientable baseTriangulation)
    (changed : bundleClass ≠ bundleClass⁻¹) : False :=
  changed (data.nonorientable_bundleClass_involutive nonorientable)

include data in
/-- Hostile vacuity probe: an empty candidate class contradicts the acceptance record. -/
theorem empty_candidate_class_blocks
    (empty : IsEmpty
      (TwoDimensionalSenguptaEmbeddedSubdivisionCandidateData.{uCurve, uEdge,
        uInternal, uFace, uRegion, uSurface, uVertex, uFineInternal, uFineFace, uFineVertex}
        (baseEmbedded := baseEmbedded))) : False :=
  empty.false data.candidate_nonempty.some

end

end YangMills.Dimensions.TwoDimensionalSenguptaUniversalCurveFixedEmbeddedSubdivision.Probes
