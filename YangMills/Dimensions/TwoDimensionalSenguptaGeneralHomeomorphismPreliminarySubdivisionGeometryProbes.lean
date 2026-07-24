/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Dimensions.TwoDimensionalSenguptaGeneralHomeomorphismPreliminarySubdivisionGeometry

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
    (data : TwoDimensionalSenguptaUniversalGeneralHomeomorphismPreliminarySubdivisionGeometryData.{uCurve,
      uEdge, uInternal, uFace, uRegion, uSurface, uVertex, uTargetEdge, uTargetInternal,
      uTargetFace, uTargetRegion, uTargetSurface, uTargetVertex, uSourceFineEdge,
      uSourceFineInternal, uSourceFineFace, uSourceFineVertex, uTargetFineEdge,
      uTargetFineInternal, uTargetFineFace, uTargetFineVertex}
      (baseEmbedded := baseEmbedded))

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
  TwoDimensionalSenguptaGeneralHomeomorphismPreliminarySubdivisionGeometryData.sourceFineEdgeFintype
  TwoDimensionalSenguptaGeneralHomeomorphismPreliminarySubdivisionGeometryData.sourceFineEdgeDecidableEq
  TwoDimensionalSenguptaGeneralHomeomorphismPreliminarySubdivisionGeometryData.sourceFineInternalFintype
  TwoDimensionalSenguptaGeneralHomeomorphismPreliminarySubdivisionGeometryData.sourceFineInternalDecidableEq
  TwoDimensionalSenguptaGeneralHomeomorphismPreliminarySubdivisionGeometryData.sourceFineFaceFintype
  TwoDimensionalSenguptaGeneralHomeomorphismPreliminarySubdivisionGeometryData.sourceFineFaceDecidableEq
  TwoDimensionalSenguptaGeneralHomeomorphismPreliminarySubdivisionGeometryData.targetFineEdgeFintype
  TwoDimensionalSenguptaGeneralHomeomorphismPreliminarySubdivisionGeometryData.targetFineEdgeDecidableEq
  TwoDimensionalSenguptaGeneralHomeomorphismPreliminarySubdivisionGeometryData.targetFineInternalFintype
  TwoDimensionalSenguptaGeneralHomeomorphismPreliminarySubdivisionGeometryData.targetFineInternalDecidableEq
  TwoDimensionalSenguptaGeneralHomeomorphismPreliminarySubdivisionGeometryData.targetFineFaceFintype
  TwoDimensionalSenguptaGeneralHomeomorphismPreliminarySubdivisionGeometryData.targetFineFaceDecidableEq

omit [Nonempty Curve] [Fintype Region] in
/-- Exact isotopy probe: the geometric certificate starts at the original outer map and ends at its
fine cellwise-compatible deformation. -/
theorem exact_generalPreliminarySubdivision_isotopy_endpoints
    {candidate : TwoDimensionalSenguptaGeneralEmbeddedHomeomorphismCandidateData.{uCurve,
      uEdge, uInternal, uFace, uRegion, uSurface, uVertex, uTargetEdge, uTargetInternal,
      uTargetFace, uTargetRegion, uTargetSurface, uTargetVertex}
      (baseEmbedded := baseEmbedded)}
    (geometry : TwoDimensionalSenguptaGeneralHomeomorphismPreliminarySubdivisionGeometryData.{uCurve,
      uEdge, uInternal, uFace, uRegion, uSurface, uVertex, uTargetEdge, uTargetInternal,
      uTargetFace, uTargetRegion, uTargetSurface, uTargetVertex, uSourceFineEdge,
      uSourceFineInternal, uSourceFineFace, uSourceFineVertex, uTargetFineEdge,
      uTargetFineInternal, uTargetFineFace, uTargetFineVertex} candidate) :
    geometry.fineCellwise_isotopy.family ⟨0, by norm_num⟩ = candidate.surfaceHomeomorphism ∧
      geometry.fineCellwise_isotopy.family ⟨1, by norm_num⟩ =
        geometry.fineCellwise.surfaceHomeomorphism :=
  ⟨geometry.exact_isotopy_initial, geometry.exact_isotopy_terminal⟩

omit [Nonempty Curve] [Fintype Region] in
/-- Hostile isotopy probe: changing the terminal fine homeomorphism contradicts the certificate. -/
theorem changed_generalPreliminarySubdivision_terminal_homeomorphism_blocked
    {candidate : TwoDimensionalSenguptaGeneralEmbeddedHomeomorphismCandidateData.{uCurve,
      uEdge, uInternal, uFace, uRegion, uSurface, uVertex, uTargetEdge, uTargetInternal,
      uTargetFace, uTargetRegion, uTargetSurface, uTargetVertex}
      (baseEmbedded := baseEmbedded)}
    (geometry : TwoDimensionalSenguptaGeneralHomeomorphismPreliminarySubdivisionGeometryData.{uCurve,
      uEdge, uInternal, uFace, uRegion, uSurface, uVertex, uTargetEdge, uTargetInternal,
      uTargetFace, uTargetRegion, uTargetSurface, uTargetVertex, uSourceFineEdge,
      uSourceFineInternal, uSourceFineFace, uSourceFineVertex, uTargetFineEdge,
      uTargetFineInternal, uTargetFineFace, uTargetFineVertex} candidate)
    (changed : Surface ≃ₜ candidate.TargetSurface)
    (changed_ne : changed ≠ geometry.fineCellwise.surfaceHomeomorphism)
    (claimed : geometry.fineCellwise_isotopy.family ⟨1, by norm_num⟩ = changed) : False :=
  changed_ne (claimed.symm.trans geometry.exact_isotopy_terminal)

omit [Nonempty Curve] [Fintype Region] in
include data in
/-- Candidate nonemptiness blocks vacuous universal preliminary-subdivision geometry. -/
theorem exact_generalPreliminarySubdivision_candidate_nonempty : Nonempty
    (TwoDimensionalSenguptaGeneralEmbeddedHomeomorphismCandidateData.{uCurve,
      uEdge, uInternal, uFace, uRegion, uSurface, uVertex, uTargetEdge, uTargetInternal,
      uTargetFace, uTargetRegion, uTargetSurface, uTargetVertex}
      (baseEmbedded := baseEmbedded)) :=
  data.candidate_nonempty

omit [Nonempty Curve] [Fintype Region] in
include data in
/-- Every general outer candidate receives source/target split-bond subdivision geometry. -/
theorem exact_generalPreliminarySubdivision_geometry_for
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

omit [Nonempty Curve] [Fintype Region] in
include data in
/-- Failure to construct preliminary subdivisions for any one general candidate blocks universal
geometric acceptance. -/
theorem missing_generalPreliminarySubdivision_geometry_blocks
    (candidate : TwoDimensionalSenguptaGeneralEmbeddedHomeomorphismCandidateData.{uCurve,
      uEdge, uInternal, uFace, uRegion, uSurface, uVertex, uTargetEdge, uTargetInternal,
      uTargetFace, uTargetRegion, uTargetSurface, uTargetVertex}
      (baseEmbedded := baseEmbedded))
    (missing : ¬ candidate.HasPreliminarySubdivisionGeometry.{uCurve, uEdge, uInternal,
      uFace, uRegion, uSurface, uVertex, uTargetEdge, uTargetInternal, uTargetFace,
      uTargetRegion, uTargetSurface, uTargetVertex, uSourceFineEdge, uSourceFineInternal,
      uSourceFineFace, uSourceFineVertex, uTargetFineEdge, uTargetFineInternal,
      uTargetFineFace, uTargetFineVertex}) : False :=
  missing (data.preliminarySubdivision candidate)

omit [Nonempty Curve] [Fintype Region] in
include data in
/-- An empty outer candidate class cannot satisfy universal preliminary-subdivision geometry. -/
theorem empty_generalPreliminarySubdivision_candidate_class_blocks
    (empty : IsEmpty
      (TwoDimensionalSenguptaGeneralEmbeddedHomeomorphismCandidateData.{uCurve,
        uEdge, uInternal, uFace, uRegion, uSurface, uVertex, uTargetEdge, uTargetInternal,
        uTargetFace, uTargetRegion, uTargetSurface, uTargetVertex}
        (baseEmbedded := baseEmbedded))) : False :=
  empty.false data.candidate_nonempty.some

end

end YangMills.Dimensions
