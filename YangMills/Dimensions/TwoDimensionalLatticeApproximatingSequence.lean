/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Dimensions.TwoDimensionalGeneralBoundaryChoice
import YangMills.Dimensions.TwoDimensionalSquareLatticePath

/-!
# Driver lattice-approximating graph sequences

This module formalizes Driver Definition 8.1 on the project's conservative embedded-arc subclass;
Driver-permitted one-edge loop incidence must first be subdivided. At every positive spacing `ε`, the approximating
embedded graph has exact paths in the directed nearest-neighbor graph on `εℤ²`. Coarse edges and
bounded regions map surjectively to the approximating graph. Region symmetric-difference area is
uniformly `O(ε)`, stated by an explicit constant and positive cutoff. Every valid coarse boundary
presentation is transported to a valid fine presentation with the exact mapped ordered words.

The interface is uninhabited and constructs no graph sequence. It states no Villain/Wilson action,
lattice measure, limit, or Yang--Mills theory.
-/

namespace YangMills.Dimensions

open MeasureTheory Set
open YangMills.Mathematics

noncomputable section

universe uVertex uEdge uFace uXAxisCell
  uFineVertex uFineEdge uFineFace uFineXAxisCell

/-- Strictly positive lattice spacing. -/
abbrev PositiveLatticeSpacing := { ε : ℝ // 0 < ε }

/-- Map one oriented edge without changing its selected orientation. -/
def mapOrientedEdge {Edge FineEdge : Type*} (edgeMap : Edge → FineEdge) :
    OrientedEdge Edge → OrientedEdge FineEdge
  | .forward edge => .forward (edgeMap edge)
  | .reverse edge => .reverse (edgeMap edge)

/-- Map an exact oriented word edge-by-edge, retaining traversal order. -/
def mapOrientedWord {Edge FineEdge : Type*} (edgeMap : Edge → FineEdge)
    (word : List (OrientedEdge Edge)) : List (OrientedEdge FineEdge) :=
  word.map (mapOrientedEdge edgeMap)

/-- Literal symmetric difference of two planar regions. -/
def twoDimensionalRegionSymmetricDifference
    (first second : Set EuclideanDimension.two.Spacetime) :
    Set EuclideanDimension.two.Spacetime :=
  (first \ second) ∪ (second \ first)

variable
    {G Gauge Sample Connection : Type*}
    [Group G] [MeasurableSpace G] [Group Gauge] [MeasurableSpace Sample]
    {base : TwoDimensionalGaugeFixedHolonomyMeasureData G Gauge Sample Connection}
    {coarse : TwoDimensionalEmbeddedPlanarGraphData.{uVertex, uEdge, uFace, uXAxisCell} base}
    [DecidableEq coarse.Edge]

/-- Driver Definition 8.1 lattice-approximating sequence on the strengthened embedded-arc graph
subclass. -/
structure TwoDimensionalLatticeApproximatingSequenceData where
  fine : PositiveLatticeSpacing →
    TwoDimensionalEmbeddedPlanarGraphData.{uFineVertex, uFineEdge, uFineFace, uFineXAxisCell} base
  fineEdgeDecidableEq : ∀ spacing, DecidableEq (fine spacing).Edge
  /-- Existing exact coarse boundary choices prevent the facewise boundary clause from being empty. -/
  coarseBoundaryChoices : TwoDimensionalGeneralBoundaryChoiceData base coarse
  edgeMap : ∀ spacing, coarse.Edge → (fine spacing).Edge
  faceMap : ∀ spacing, coarse.Face → (fine spacing).Face
  edgeMap_surjective : ∀ spacing, Function.Surjective (edgeMap spacing)
  faceMap_surjective : ∀ spacing, Function.Surjective (faceMap spacing)
  /-- Every approximating edge is literally a finite path in Driver's `ε`-square lattice. -/
  fineEdge_latticePath : ∀ spacing edge,
    EpsilonSquareLatticePathCertificate
      ((fine spacing).pathCurve ((fine spacing).edgePath edge)) spacing.1
  /-- Uniform explicit interpretation of “area ... is of order `ε`” for all bounded faces. -/
  areaOrderConstant : ℝ
  areaOrderConstant_nonnegative : 0 ≤ areaOrderConstant
  areaOrderCutoff : ℝ
  areaOrderCutoff_pos : 0 < areaOrderCutoff
  face_symmetricDifference_area_le : ∀ spacing,
    spacing.1 < areaOrderCutoff → ∀ face,
      twoDimensionalCoordinateLebesgueVolume
        (twoDimensionalRegionSymmetricDifference
          (coarse.faceRegion face)
          ((fine spacing).faceRegion (faceMap spacing face))) ≤
        ENNReal.ofReal (areaOrderConstant * spacing.1)
  /-- Driver's condition is facewise: every valid coarse boundary presentation maps to its own valid
  presentation, without forcing unrelated coarse faces sharing one image label to use equal words. -/
  boundaryPresentationMap : ∀ spacing,
    GeneralBoundaryPresentation coarse → GeneralBoundaryPresentation (fine spacing)
  boundaryPresentation_face : ∀ spacing presentation,
    (boundaryPresentationMap spacing presentation).face =
      faceMap spacing presentation.face
  boundary_words_map : ∀ spacing presentation,
    (boundaryPresentationMap spacing presentation).components.map
        GeneralBoundaryComponentPresentation.word =
      presentation.components.map
        (fun component => mapOrientedWord (edgeMap spacing) component.word)

end

end YangMills.Dimensions
