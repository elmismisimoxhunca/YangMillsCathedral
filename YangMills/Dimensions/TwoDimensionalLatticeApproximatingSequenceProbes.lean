/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Dimensions.TwoDimensionalLatticeApproximatingSequence
import YangMills.Foundation.DimensionsProbes

/-!
# Probes for Driver lattice-approximating sequences
-/

namespace YangMills.Dimensions.TwoDimensionalLatticeApproximatingSequence.Probes

open MeasureTheory Set
open YangMills.Mathematics

noncomputable section

universe uVertex uEdge uFace uXAxisCell
  uFineVertex uFineEdge uFineFace uFineXAxisCell

variable
    {G Gauge Sample Connection : Type*}
    [Group G] [MeasurableSpace G] [Group Gauge] [MeasurableSpace Sample]
    {base : TwoDimensionalGaugeFixedHolonomyMeasureData G Gauge Sample Connection}
    {coarse : TwoDimensionalEmbeddedPlanarGraphData.{uVertex, uEdge, uFace, uXAxisCell} base}
    [DecidableEq coarse.Edge]
    (sequence : TwoDimensionalLatticeApproximatingSequenceData.{uVertex, uEdge, uFace,
      uXAxisCell, uFineVertex, uFineEdge, uFineFace, uFineXAxisCell}
      (base := base) (coarse := coarse))

/-- Every spacing in the family is strictly positive. -/
theorem exact_positive_spacing (spacing : PositiveLatticeSpacing) : 0 < spacing.1 :=
  spacing.2

/-- Every fine edge is an exact path in the directed nearest-neighbor `εℤ²` graph. -/
theorem exact_fine_edge_lattice_path
    (spacing : PositiveLatticeSpacing) (edge : (sequence.fine spacing).Edge) :
    Nonempty (EpsilonSquareLatticePathCertificate
      ((sequence.fine spacing).pathCurve ((sequence.fine spacing).edgePath edge)) spacing.1) :=
  ⟨sequence.fineEdge_latticePath spacing edge⟩

/-- Driver's maps on coarse bonds and bounded regions are genuinely surjective. -/
theorem exact_edge_face_surjections (spacing : PositiveLatticeSpacing) :
    Function.Surjective (sequence.edgeMap spacing) ∧
      Function.Surjective (sequence.faceMap spacing) :=
  ⟨sequence.edgeMap_surjective spacing, sequence.faceMap_surjective spacing⟩

/-- The source phrase “of order ε” is retained as one explicit uniform bound and cutoff. -/
theorem exact_symmetric_difference_area_order
    (spacing : PositiveLatticeSpacing) (small : spacing.1 < sequence.areaOrderCutoff)
    (face : coarse.Face) :
    twoDimensionalCoordinateLebesgueVolume
        (twoDimensionalRegionSymmetricDifference
          (coarse.faceRegion face)
          ((sequence.fine spacing).faceRegion (sequence.faceMap spacing face))) ≤
      ENNReal.ofReal (sequence.areaOrderConstant * spacing.1) :=
  sequence.face_symmetricDifference_area_le spacing small face

/-- Every coarse face has at least one actual valid boundary presentation, so transport is not
vacuous. -/
theorem exact_coarse_boundary_nonempty
    (sequence : TwoDimensionalLatticeApproximatingSequenceData
      (base := base) (coarse := coarse))
    (face : coarse.Face) :
    ∃ presentation : GeneralBoundaryPresentation coarse, presentation.face = face :=
  TwoDimensionalGeneralBoundaryChoiceData.choiceNonempty
    sequence.coarseBoundaryChoices face

/-- Every valid facewise boundary presentation maps with exact orientation and component order. -/
theorem exact_boundary_word_transport
    (spacing : PositiveLatticeSpacing)
    (presentation : GeneralBoundaryPresentation coarse) :
    letI := sequence.fineEdgeDecidableEq spacing
    (sequence.boundaryPresentationMap spacing presentation).face =
        sequence.faceMap spacing presentation.face ∧
      (sequence.boundaryPresentationMap spacing presentation).components.map
          GeneralBoundaryComponentPresentation.word =
        presentation.components.map
          (fun component => mapOrientedWord (sequence.edgeMap spacing) component.word) := by
  letI := sequence.fineEdgeDecidableEq spacing
  exact ⟨sequence.boundaryPresentation_face spacing presentation,
    sequence.boundary_words_map spacing presentation⟩

/-- Edge mapping preserves forward and reverse orientation literally. -/
theorem exact_oriented_edge_map
    (spacing : PositiveLatticeSpacing) (edge : coarse.Edge) :
    mapOrientedEdge (sequence.edgeMap spacing) (.forward edge) =
        .forward (sequence.edgeMap spacing edge) ∧
      mapOrientedEdge (sequence.edgeMap spacing) (.reverse edge) =
        .reverse (sequence.edgeMap spacing edge) :=
  ⟨rfl, rfl⟩

/-- A nonsurjective substitute for either source map is rejected. -/
theorem nonsurjective_edge_map_blocked
    (spacing : PositiveLatticeSpacing)
    (claimed : ¬ Function.Surjective (sequence.edgeMap spacing)) : False :=
  claimed (sequence.edgeMap_surjective spacing)

/-- A wrong area estimate is rejected whenever it exceeds the exact source-facing bound. -/
theorem wrong_area_bound_blocked
    (spacing : PositiveLatticeSpacing) (small : spacing.1 < sequence.areaOrderCutoff)
    (face : coarse.Face) (wrong : ENNReal)
    (too_small : wrong < twoDimensionalCoordinateLebesgueVolume
      (twoDimensionalRegionSymmetricDifference
        (coarse.faceRegion face)
        ((sequence.fine spacing).faceRegion (sequence.faceMap spacing face))))
    (claimed : ENNReal.ofReal (sequence.areaOrderConstant * spacing.1) ≤ wrong) : False := by
  have exactBound := sequence.face_symmetricDifference_area_le spacing small face
  exact (not_le_of_gt too_small) (exactBound.trans claimed)

/-- Approximating sequences remain two-dimensional and cannot inhabit the Clay endpoint. -/
theorem lattice_approximation_not_four_dimensional :
    EuclideanDimension.two ≠ EuclideanDimension.four :=
  EuclideanDimension.two_ne_four

end

end YangMills.Dimensions.TwoDimensionalLatticeApproximatingSequence.Probes
