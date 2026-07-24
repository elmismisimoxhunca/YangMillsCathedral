/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Dimensions.TwoDimensionalSenguptaUniversalCellwiseEmbeddedHomeomorphism
import Mathlib.Topology.Path

/-!
# General embedded homeomorphism candidates for Sengupta Fact 3

Sengupta's Fact 3 starts with two admissible triangulated surface/curve pairs and an actual
homeomorphism carrying each indexed curve to its target, possibly after reparametrization, with only
equality of total area assumed. The proof subsequently constructs preliminary subdivisions and a
simplicial isomorphism.

This file formalizes that broader outer candidate class. Unlike the existing cellwise-compatible
candidate, it deliberately stores no edge, face, vertex, or region equivalence and no facewise
reparametrization. Curve transport is stated by equality of the whole ordered directed path after an endpoint-fixing
homeomorphic reparametrization of the unit interval.
It does not construct preliminary subdivisions, a simplicial certificate, factor invariance, or a
Fact 3 universal inhabitant.
-/

namespace YangMills.Dimensions

open YangMills.Mathematics
open Set
open scoped Manifold ContDiff ENNReal

noncomputable section

universe uCurve uEdge uInternal uFace uRegion uSurface uVertex
  uTargetEdge uTargetInternal uTargetFace uTargetRegion uTargetSurface uTargetVertex

/-- One forward external bond as a bundled path with its exact embedded endpoints. -/
noncomputable def senguptaEmbeddedForwardEdgePath
    {Edge InternalEdge Face Region Vertex Surface Curve : Type*}
    [TopologicalSpace Surface]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) Surface] [Fintype Curve] [DecidableEq Edge] [DecidableEq InternalEdge]
    [Fintype Face] [DecidableEq Face] [DecidableEq Region]
    {triangulation : TwoDimensionalSenguptaTriangulatedRegionData
      Edge InternalEdge Face Region}
    {closed : TwoDimensionalSenguptaClosedTriangularPresentationData
      (Vertex := Vertex) triangulation}
    (embedded : TwoDimensionalSenguptaEmbeddedTriangularPresentationData
      (Surface := Surface) (Curve := Curve) (closed := closed)) (edge : Edge) :
    Path (embedded.vertexPoint (closed.edgeInitial (Sum.inl edge)))
      (embedded.vertexPoint (closed.edgeTerminal (Sum.inl edge))) :=
  Path.mk
    ⟨fun point => embedded.edgePath (Sum.inl edge) point,
      (embedded.edgePath_embedding (Sum.inl edge)).continuous⟩
    (embedded.edgePath_initial (Sum.inl edge))
    (embedded.edgePath_terminal (Sum.inl edge))

/-- One directed external bond as a bundled path; reverse orientation reverses its parametrization. -/
noncomputable def senguptaEmbeddedOrientedEdgePath
    {Edge InternalEdge Face Region Vertex Surface Curve : Type*}
    [TopologicalSpace Surface]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) Surface] [Fintype Curve] [DecidableEq Edge] [DecidableEq InternalEdge]
    [Fintype Face] [DecidableEq Face] [DecidableEq Region]
    {triangulation : TwoDimensionalSenguptaTriangulatedRegionData
      Edge InternalEdge Face Region}
    {closed : TwoDimensionalSenguptaClosedTriangularPresentationData
      (Vertex := Vertex) triangulation}
    (embedded : TwoDimensionalSenguptaEmbeddedTriangularPresentationData
      (Surface := Surface) (Curve := Curve) (closed := closed)) :
    (edge : OrientedEdge Edge) →
      Path (embedded.vertexPoint (senguptaOrientedEdgeInitial
        (fun value => closed.edgeInitial (Sum.inl value))
        (fun value => closed.edgeTerminal (Sum.inl value)) edge))
        (embedded.vertexPoint (senguptaOrientedEdgeTerminal
          (fun value => closed.edgeInitial (Sum.inl value))
          (fun value => closed.edgeTerminal (Sum.inl value)) edge))
  | .forward edge => senguptaEmbeddedForwardEdgePath embedded edge
  | .reverse edge => (senguptaEmbeddedForwardEdgePath embedded edge).symm

/-- Continuous whole-curve path obtained by concatenating the ordered directed bonds of one
nonempty composable curve word. Unlike a set trace, this retains traversal order and orientation. -/
noncomputable def senguptaEmbeddedCurveWordPath
    {Edge InternalEdge Face Region Vertex Surface Curve : Type*}
    [TopologicalSpace Surface]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) Surface] [Fintype Curve] [DecidableEq Edge] [DecidableEq InternalEdge]
    [Fintype Face] [DecidableEq Face] [DecidableEq Region]
    {triangulation : TwoDimensionalSenguptaTriangulatedRegionData
      Edge InternalEdge Face Region}
    {closed : TwoDimensionalSenguptaClosedTriangularPresentationData
      (Vertex := Vertex) triangulation}
    (embedded : TwoDimensionalSenguptaEmbeddedTriangularPresentationData
      (Surface := Surface) (Curve := Curve) (closed := closed)) :
    (word : List (OrientedEdge Edge)) →
    (hne : word ≠ []) →
    IsSenguptaComposableOrientedPath
      (fun edge => closed.edgeInitial (Sum.inl edge))
      (fun edge => closed.edgeTerminal (Sum.inl edge)) word →
    Path
      (embedded.vertexPoint (senguptaOrientedEdgeInitial
        (fun edge => closed.edgeInitial (Sum.inl edge))
        (fun edge => closed.edgeTerminal (Sum.inl edge)) (word.head hne)))
      (embedded.vertexPoint (senguptaOrientedEdgeTerminal
        (fun edge => closed.edgeInitial (Sum.inl edge))
        (fun edge => closed.edgeTerminal (Sum.inl edge)) (word.getLast hne)))
  | [], hne, _ => False.elim (hne rfl)
  | [edge], _, _ => senguptaEmbeddedOrientedEdgePath embedded edge
  | first :: second :: rest, _, composable => by
      have endpoint_eq :
          embedded.vertexPoint (senguptaOrientedEdgeTerminal
            (fun edge => closed.edgeInitial (Sum.inl edge))
            (fun edge => closed.edgeTerminal (Sum.inl edge)) first) =
          embedded.vertexPoint (senguptaOrientedEdgeInitial
            (fun edge => closed.edgeInitial (Sum.inl edge))
            (fun edge => closed.edgeTerminal (Sum.inl edge)) second) :=
        congrArg embedded.vertexPoint composable.1
      have tail := senguptaEmbeddedCurveWordPath embedded (second :: rest) (by simp) composable.2
      have initial := senguptaEmbeddedOrientedEdgePath embedded first
      rw [endpoint_eq] at initial
      simpa using initial.trans tail

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

/-- One source-faithful outer candidate for the general, not-necessarily-cellwise, Fact 3 class.
The same `Curve` index realizes Sengupta's prescribed indexing `c'_i = φ ∘ c_i` up to
reparametrization through exact equality of whole ordered directed paths. -/
structure TwoDimensionalSenguptaGeneralEmbeddedHomeomorphismCandidateData where
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
  surfaceHomeomorphism : Surface ≃ₜ TargetSurface
  curveReparam : Curve → SenguptaClosedUnitInterval ≃ₜ SenguptaClosedUnitInterval
  curveReparam_initial : ∀ curve,
    curveReparam curve ⟨0, by norm_num⟩ = ⟨0, by norm_num⟩
  curveReparam_terminal : ∀ curve,
    curveReparam curve ⟨1, by norm_num⟩ = ⟨1, by norm_num⟩
  curvePath_eq : ∀ (curve : Curve) (point : SenguptaClosedUnitInterval),
    senguptaEmbeddedCurveWordPath targetEmbedded (targetEmbedded.curveWord curve)
        (targetEmbedded.curveWord_nonempty curve) (targetEmbedded.curveWord_composable curve)
        (curveReparam curve point) =
      surfaceHomeomorphism
        (senguptaEmbeddedCurveWordPath baseEmbedded (baseEmbedded.curveWord curve)
          (baseEmbedded.curveWord_nonempty curve) (baseEmbedded.curveWord_composable curve) point)
  totalArea_eq :
    (∑ face : TargetFace, target.faceArea face) =
      ∑ face : Face, baseTriangulation.faceArea face

namespace TwoDimensionalSenguptaGeneralEmbeddedHomeomorphismCandidateData

attribute [local instance] targetSurfaceTopology targetSurfaceCharted
  targetEdgeFintype targetEdgeDecidableEq targetInternalFintype targetInternalDecidableEq
  targetFaceFintype targetFaceDecidableEq targetRegionFintype targetRegionDecidableEq

/-- The candidate is an actual homeomorphism of the two surface carriers. -/
noncomputable def homeomorphism
    (candidate : TwoDimensionalSenguptaGeneralEmbeddedHomeomorphismCandidateData
      (baseEmbedded := baseEmbedded)) :
    Surface ≃ₜ candidate.TargetSurface :=
  candidate.surfaceHomeomorphism

omit [Nonempty Curve] [Fintype Edge] [Fintype InternalEdge] [Fintype Region] in
/-- Exact source-level directed curve transport after one endpoint-fixing whole-curve
reparametrization. Traversal order and orientation are retained. -/
theorem maps_curve_path
    (candidate : TwoDimensionalSenguptaGeneralEmbeddedHomeomorphismCandidateData
      (baseEmbedded := baseEmbedded)) (curve : Curve)
    (point : SenguptaClosedUnitInterval) :
    senguptaEmbeddedCurveWordPath candidate.targetEmbedded
        (candidate.targetEmbedded.curveWord curve)
        (candidate.targetEmbedded.curveWord_nonempty curve)
        (candidate.targetEmbedded.curveWord_composable curve)
        (candidate.curveReparam curve point) =
      candidate.surfaceHomeomorphism
        (senguptaEmbeddedCurveWordPath baseEmbedded (baseEmbedded.curveWord curve)
          (baseEmbedded.curveWord_nonempty curve) (baseEmbedded.curveWord_composable curve) point) :=
  candidate.curvePath_eq curve point

omit [Nonempty Curve] [Fintype Edge] [Fintype InternalEdge] [Fintype Region] in
/-- Fact 3 assumes equality only of total simplex area, not a facewise or regionwise allocation. -/
theorem total_simplex_area_eq
    (candidate : TwoDimensionalSenguptaGeneralEmbeddedHomeomorphismCandidateData
      (baseEmbedded := baseEmbedded)) :
    (∑ face : candidate.TargetFace, candidate.target.faceArea face) =
      ∑ face : Face, baseTriangulation.faceArea face :=
  candidate.totalArea_eq

end TwoDimensionalSenguptaGeneralEmbeddedHomeomorphismCandidateData

end

end YangMills.Dimensions
