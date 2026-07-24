/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Dimensions.TwoDimensionalSenguptaGeneralEmbeddedHomeomorphismCandidate

namespace YangMills.Dimensions

open YangMills.Mathematics Set
open scoped Manifold ContDiff ENNReal

noncomputable section

universe uCurve uEdge uInternal uFace uRegion uSurface uVertex
  uTargetEdge uTargetInternal uTargetFace uTargetRegion uTargetSurface uTargetVertex

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
    (candidate : TwoDimensionalSenguptaGeneralEmbeddedHomeomorphismCandidateData.{uCurve,
      uEdge, uInternal, uFace, uRegion, uSurface, uVertex, uTargetEdge, uTargetInternal,
      uTargetFace, uTargetRegion, uTargetSurface, uTargetVertex}
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

omit [Nonempty Curve] [Fintype Edge] [Fintype InternalEdge] [Fintype Region] in
/-- Exact general-candidate probe: each indexed directed curve path is transported after one
endpoint-fixing whole-curve reparametrization, without requiring cellwise edge equivalences. -/
theorem exact_generalHomeomorphism_maps_curve_path
    (curve : Curve) (point : SenguptaClosedUnitInterval) :
    senguptaEmbeddedCurveWordPath candidate.targetEmbedded
        (candidate.targetEmbedded.curveWord curve)
        (candidate.targetEmbedded.curveWord_nonempty curve)
        (candidate.targetEmbedded.curveWord_composable curve)
        (candidate.curveReparam curve point) =
      candidate.surfaceHomeomorphism
        (senguptaEmbeddedCurveWordPath baseEmbedded (baseEmbedded.curveWord curve)
          (baseEmbedded.curveWord_nonempty curve) (baseEmbedded.curveWord_composable curve) point) :=
  candidate.maps_curve_path curve point

omit [Nonempty Curve] [Fintype Edge] [Fintype InternalEdge] [Fintype Region] in
/-- Exact general-candidate probe: only total simplex area equality is required. -/
theorem exact_generalHomeomorphism_total_area :
    (∑ face : candidate.TargetFace, candidate.target.faceArea face) =
      ∑ face : Face, baseTriangulation.faceArea face :=
  candidate.total_simplex_area_eq

omit [Nonempty Curve] [Fintype Edge] [Fintype InternalEdge] [Fintype Region] in
/-- Hostile orientation/order probe: a reversed target traversal cannot replace the required
endpoint-preserving directed transport when the two values differ. -/
theorem reversed_generalHomeomorphism_curve_path_blocked
    (curve : Curve) (point : SenguptaClosedUnitInterval)
    (reversed_ne :
      senguptaEmbeddedCurveWordPath candidate.targetEmbedded
          (candidate.targetEmbedded.curveWord curve)
          (candidate.targetEmbedded.curveWord_nonempty curve)
          (candidate.targetEmbedded.curveWord_composable curve)
          (senguptaReverseClosedUnitInterval point) ≠
        candidate.surfaceHomeomorphism
          (senguptaEmbeddedCurveWordPath baseEmbedded (baseEmbedded.curveWord curve)
            (baseEmbedded.curveWord_nonempty curve)
            (baseEmbedded.curveWord_composable curve) point))
    (claimed_reverse : candidate.curveReparam curve point =
      senguptaReverseClosedUnitInterval point) : False := by
  apply reversed_ne
  rw [← claimed_reverse]
  exact candidate.maps_curve_path curve point

omit [Nonempty Curve] [Fintype Edge] [Fintype InternalEdge] [Fintype Region] in
/-- Hostile endpoint probe: the required endpoint-fixing reparametrization cannot be global interval
reversal, independently of the geometric curve values. -/
theorem globally_reversed_generalHomeomorphism_reparam_blocked
    (curve : Curve)
    (claimed_reverse : ∀ point : SenguptaClosedUnitInterval,
      candidate.curveReparam curve point = senguptaReverseClosedUnitInterval point) : False := by
  have hzero := (candidate.curveReparam_initial curve).symm.trans
    (claimed_reverse ⟨0, by norm_num⟩)
  have hvalue := congrArg Subtype.val hzero
  norm_num [senguptaReverseClosedUnitInterval] at hvalue

omit [Nonempty Curve] [Fintype Edge] [Fintype InternalEdge] [Fintype Region] in
/-- Hostile area probe: replacing the target total by a genuinely changed total contradicts Fact 3's
same-total-area premise. -/
theorem changed_generalHomeomorphism_total_area_blocked
    (changed : ℝ)
    (changed_ne : changed ≠ ∑ face : Face, baseTriangulation.faceArea face)
    (claimed : (∑ face : candidate.TargetFace, candidate.target.faceArea face) = changed) : False :=
  changed_ne (claimed.symm.trans candidate.total_simplex_area_eq)

end

end YangMills.Dimensions
