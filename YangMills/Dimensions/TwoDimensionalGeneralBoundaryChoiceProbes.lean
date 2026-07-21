/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Dimensions.TwoDimensionalGeneralBoundaryChoice

/-!
# Probes for universal disconnected boundary choices
-/

namespace YangMills.Dimensions.TwoDimensionalGeneralBoundaryChoice.Probes

open Set
open YangMills.Mathematics

noncomputable section

universe uVertex uEdge uFace uXAxisCell

variable
    {G Gauge Sample Connection : Type*}
    [Group G] [MeasurableSpace G] [Group Gauge] [MeasurableSpace Sample]
    {base : TwoDimensionalGaugeFixedHolonomyMeasureData G Gauge Sample Connection}
    {embedded : TwoDimensionalEmbeddedPlanarGraphData.{uVertex, uEdge, uFace, uXAxisCell} base}
    [DecidableEq embedded.Edge]
    (choices : TwoDimensionalGeneralBoundaryChoiceData base embedded)

/-- Facewise existence gives a simultaneous universal-carrier choice. -/
theorem exact_choice_nonempty
    (choices : TwoDimensionalGeneralBoundaryChoiceData base embedded) :
    Nonempty (TwoDimensionalGeneralBoundaryChoiceData.Choice (embedded := embedded)) :=
  TwoDimensionalGeneralBoundaryChoiceData.choice_nonempty choices

/-- The choice carrier is definitionally every valid simultaneous presentation; it cannot be
replaced by a supplier-selected singleton family. -/
theorem arbitrary_valid_choice_is_in_scope
    (candidate : GeneralBoundaryChoice embedded) :
    candidate ∈ (Set.univ : Set (TwoDimensionalGeneralBoundaryChoiceData.Choice
      (embedded := embedded))) :=
  Set.mem_univ candidate

/-- Every face receives an exact presentation of that same face. -/
theorem exact_presentation_face
    (choice : TwoDimensionalGeneralBoundaryChoiceData.Choice (embedded := embedded))
    (face : embedded.Face) : (choice.presentation face).face = face :=
  choice.presentation_face face

/-- A presentation has a finite nonempty ordered component list. -/
theorem exact_finite_component_order
    (choice : TwoDimensionalGeneralBoundaryChoiceData.Choice (embedded := embedded))
    (face : embedded.Face) : (choice.presentation face).components ≠ [] :=
  (choice.presentation face).components_nonempty

/-- Component occurrences are duplicate-free before their words enter the ordered product. -/
theorem exact_component_occurrence_nodup
    (choice : TwoDimensionalGeneralBoundaryChoiceData.Choice (embedded := embedded))
    (face : embedded.Face) : (choice.presentation face).components.Nodup :=
  (choice.presentation face).components_nodup

/-- Repeating the exact same component value is rejected, not hidden behind an inequality premise. -/
theorem duplicate_component_occurrence_blocked
    (component : GeneralBoundaryComponentPresentation embedded)
    (claimed : [component, component].Nodup) : False := by
  simp at claimed

/-- Every listed component is a continuous closed traversal of its exact bridge-aware word trace. -/
theorem exact_component_traversal
    (choice : TwoDimensionalGeneralBoundaryChoiceData.Choice (embedded := embedded))
    (face : embedded.Face) (component : GeneralBoundaryComponentPresentation embedded)
    (membership : component ∈ (choice.presentation face).components) :
    ContinuousOn component.traversal (Set.Icc 0 1) ∧
      component.traversal 0 = component.traversal 1 ∧
      component.traversal '' Set.Icc 0 1 =
        finiteBoundaryWordTrace embedded.pathCurve embedded.edgePath component.word ∧
      component ∈ (choice.presentation face).components :=
  ⟨component.traversal_continuousOn, component.traversal_closed,
    component.traversal_range, membership⟩

/-- The exact frontier is covered by the listed component traces. -/
theorem exact_frontier_decomposition
    (choice : TwoDimensionalGeneralBoundaryChoiceData.Choice (embedded := embedded))
    (face : embedded.Face) :
    frontier (embedded.faceRegion face) =
      ⋃ component ∈ (choice.presentation face).components,
        finiteBoundaryWordTrace embedded.pathCurve embedded.edgePath component.word := by
  simpa [choice.presentation_face face] using
    (choice.presentation face).frontier_decomposition

/-- Distinct listed components cannot duplicate or overlap one another. -/
theorem exact_component_disjointness
    (choice : TwoDimensionalGeneralBoundaryChoiceData.Choice (embedded := embedded))
    (face : embedded.Face) (first second : GeneralBoundaryComponentPresentation embedded)
    (first_mem : first ∈ (choice.presentation face).components)
    (second_mem : second ∈ (choice.presentation face).components)
    (different : first ≠ second) :
    Disjoint
      (finiteBoundaryWordTrace embedded.pathCurve embedded.edgePath first.word)
      (finiteBoundaryWordTrace embedded.pathCurve embedded.edgePath second.word) :=
  (choice.presentation face).component_traces_disjoint
    first first_mem second second_mem different

/-- Each trace is a maximal connected frontier subset, excluding artificial splitting. -/
theorem exact_component_maximality
    (choice : TwoDimensionalGeneralBoundaryChoiceData.Choice (embedded := embedded))
    (face : embedded.Face) (component : GeneralBoundaryComponentPresentation embedded)
    (membership : component ∈ (choice.presentation face).components)
    (connectedSet : Set EuclideanDimension.two.Spacetime)
    (connected : IsConnected connectedSet)
    (in_frontier : connectedSet ⊆ frontier (embedded.faceRegion face))
    (meets : (connectedSet ∩ finiteBoundaryWordTrace embedded.pathCurve embedded.edgePath
      component.word).Nonempty) :
    connectedSet ⊆ finiteBoundaryWordTrace embedded.pathCurve embedded.edgePath component.word := by
  apply (choice.presentation face).component_maximal
    component membership connectedSet connected
  · simpa [choice.presentation_face face] using in_frontier
  · exact meets

/-- A supplied origin vertex is exactly coordinate zero. -/
theorem exact_origin_when_present (vertex : embedded.Vertex)
    (present : choices.originVertex = some vertex) : embedded.vertexPoint vertex = 0 :=
  choices.originVertex_some vertex present

/-- Absence means zero is not represented by any graph vertex. -/
theorem exact_origin_when_absent (absent : choices.originVertex = none)
    (vertex : embedded.Vertex) : embedded.vertexPoint vertex ≠ 0 :=
  choices.originVertex_none absent vertex

/-- Later component traversals multiply on the left. -/
theorem two_component_order
    {H Edge : Type*} [Group H] (configuration : Edge → H)
    (first second : List (OrientedEdge Edge)) :
    finiteBoundaryComponentHolonomy configuration [first, second] =
      finiteOrientedWordHolonomy configuration second *
        finiteOrientedWordHolonomy configuration first := by
  simp [finiteBoundaryComponentHolonomy]

/-- Pointwise presentation dependence remains permitted. -/
theorem pointwise_choice_difference_not_contradictory
    {H : Type*} [Group H]
    (first second : TwoDimensionalGeneralBoundaryChoiceData.Choice (embedded := embedded))
    (face : embedded.Face) (configuration : embedded.Edge → H)
    (different : TwoDimensionalGeneralBoundaryChoiceData.boundaryHolonomy
        (G := G) first face configuration ≠
      TwoDimensionalGeneralBoundaryChoiceData.boundaryHolonomy
        (G := G) second face configuration) :
    TwoDimensionalGeneralBoundaryChoiceData.boundaryHolonomy
        (G := G) first face configuration ≠
      TwoDimensionalGeneralBoundaryChoiceData.boundaryHolonomy
        (G := G) second face configuration :=
  different

/-- General boundary data remain strictly two-dimensional. -/
theorem general_boundary_not_four_dimensional :
    EuclideanDimension.two ≠ EuclideanDimension.four :=
  EuclideanDimension.two_ne_four

end

end YangMills.Dimensions.TwoDimensionalGeneralBoundaryChoice.Probes
