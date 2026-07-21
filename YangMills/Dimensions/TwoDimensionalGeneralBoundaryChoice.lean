/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Dimensions.TwoDimensionalEmbeddedPlanarGraph
import YangMills.Mathematics.FiniteBoundaryConnectedWord
import YangMills.Mathematics.FiniteOrientedEdgeFaceWeight

/-!
# Universal disconnected planar face-boundary choices

Driver Theorem 6.4 permits bounded faces with disconnected boundary. Paths around the actual
connected boundary components require starts, orientations, an order, and cut/conjugating bridge
excursions. Here a `Choice` is not a supplier-selected subtype: it is the full structure of every
presentation satisfying the exact geometric component conditions. Thus quantification over choices
cannot collapse to a designated singleton while other valid presentations exist.

Each listed trace is nonempty, connected, pairwise disjoint, covers the exact frontier, and is
maximal among connected frontier subsets that meet it. This prevents duplicate labels and artificial
splitting. Pointwise boundary holonomies may depend on the presentation; only the later expectation
law derives integral-level independence.

Driver Definition 6.3 fixes the origin only when `0` is a graph vertex. The optional origin below is
tied exactly to coordinate zero and is proved absent from all vertices when `none`. The project
retains its conservative embedded-arc strengthening. No graph, cut system, measure, or Yang--Mills
theory is constructed.
-/

namespace YangMills.Dimensions

open Set
open YangMills.Mathematics

noncomputable section

universe uVertex uEdge uFace uXAxisCell

/-- Multiply ordered closed component words with later traversals on the left. -/
def finiteBoundaryComponentHolonomy
    {Edge G : Type*} [Group G] (configuration : Edge → G) :
    List (List (OrientedEdge Edge)) → G
  | [] => 1
  | word :: tail => finiteBoundaryComponentHolonomy configuration tail *
      finiteOrientedWordHolonomy configuration word

/-- Ordered component holonomy is measurable under the exact finite-word hypotheses. -/
theorem finiteBoundaryComponentHolonomy_measurable
    {Edge G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
    (words : List (List (OrientedEdge Edge))) :
    Measurable (fun configuration : Edge → G =>
      finiteBoundaryComponentHolonomy configuration words) := by
  induction words with
  | nil => simp [finiteBoundaryComponentHolonomy]
  | cons word tail ih =>
      simpa [finiteBoundaryComponentHolonomy] using
        ih.mul (finiteOrientedWordHolonomy_measurable word)

/-- One exact connected boundary-component presentation. -/
structure GeneralBoundaryComponentPresentation
    {G Gauge Sample Connection : Type*}
    [Group G] [MeasurableSpace G] [Group Gauge] [MeasurableSpace Sample]
    {base : TwoDimensionalGaugeFixedHolonomyMeasureData G Gauge Sample Connection}
    (embedded : TwoDimensionalEmbeddedPlanarGraphData base)
    [DecidableEq embedded.Edge] where
  word : List (OrientedEdge embedded.Edge)
  word_certificate : BoundaryConnectedWordCertificate embedded.edgeSource embedded.edgeTarget word
  traversal : ℝ → EuclideanDimension.two.Spacetime
  traversal_continuousOn : ContinuousOn traversal (Set.Icc 0 1)
  traversal_closed : traversal 0 = traversal 1
  word_realizes_traversal : ∀ (index : Fin word.length) (t : ℝ), t ∈ Set.Icc (0 : ℝ) 1 →
    traversal (((index.1 : ℝ) + t) / (word.length : ℝ)) =
      finiteOrientedEdgeCurve embedded.pathCurve embedded.edgePath (word.get index) t
  traversal_range : traversal '' Set.Icc 0 1 =
    finiteBoundaryWordTrace embedded.pathCurve embedded.edgePath word
  trace_nonempty :
    (finiteBoundaryWordTrace embedded.pathCurve embedded.edgePath word).Nonempty
  trace_connected :
    IsConnected (finiteBoundaryWordTrace embedded.pathCurve embedded.edgePath word)

/-- Every valid ordered presentation of the actual connected components of one face frontier. -/
structure GeneralBoundaryPresentation
    {G Gauge Sample Connection : Type*}
    [Group G] [MeasurableSpace G] [Group Gauge] [MeasurableSpace Sample]
    {base : TwoDimensionalGaugeFixedHolonomyMeasureData G Gauge Sample Connection}
    (embedded : TwoDimensionalEmbeddedPlanarGraphData base)
    [DecidableEq embedded.Edge] where
  face : embedded.Face
  components : List (GeneralBoundaryComponentPresentation embedded)
  components_nonempty : components ≠ []
  components_nodup : components.Nodup
  component_traces_disjoint : ∀ first ∈ components, ∀ second ∈ components, first ≠ second →
    Disjoint
      (finiteBoundaryWordTrace embedded.pathCurve embedded.edgePath first.word)
      (finiteBoundaryWordTrace embedded.pathCurve embedded.edgePath second.word)
  frontier_decomposition : frontier (embedded.faceRegion face) =
    ⋃ component ∈ components,
      finiteBoundaryWordTrace embedded.pathCurve embedded.edgePath component.word
  /-- Maximal connectedness identifies each listed trace as an actual connected component. -/
  component_maximal : ∀ component ∈ components,
      ∀ connectedSet : Set EuclideanDimension.two.Spacetime,
    IsConnected connectedSet → connectedSet ⊆ frontier (embedded.faceRegion face) →
      (connectedSet ∩
        finiteBoundaryWordTrace embedded.pathCurve embedded.edgePath component.word).Nonempty →
      connectedSet ⊆
        finiteBoundaryWordTrace embedded.pathCurve embedded.edgePath component.word

/-- One simultaneous choice of a valid presentation for every bounded face. This is the full
structure of all such assignments, not a supplier-selected family. -/
structure GeneralBoundaryChoice
    {G Gauge Sample Connection : Type*}
    [Group G] [MeasurableSpace G] [Group Gauge] [MeasurableSpace Sample]
    {base : TwoDimensionalGaugeFixedHolonomyMeasureData G Gauge Sample Connection}
    (embedded : TwoDimensionalEmbeddedPlanarGraphData base)
    [DecidableEq embedded.Edge] where
  presentation : ∀ _face : embedded.Face, GeneralBoundaryPresentation embedded
  presentation_face : ∀ target, (presentation target).face = target

/-- Boundary-neutral origin semantics and existence of at least one valid presentation for every
face. The choice type itself is the full `GeneralBoundaryChoice` structure. -/
structure TwoDimensionalGeneralBoundaryChoiceData
    {G Gauge Sample Connection : Type*}
    [Group G] [MeasurableSpace G] [Group Gauge] [MeasurableSpace Sample]
    (base : TwoDimensionalGaugeFixedHolonomyMeasureData G Gauge Sample Connection)
    (embedded : TwoDimensionalEmbeddedPlanarGraphData.{uVertex, uEdge, uFace, uXAxisCell} base)
    [DecidableEq embedded.Edge] where
  originVertex : Option embedded.Vertex
  originVertex_some : ∀ vertex, originVertex = some vertex →
    embedded.vertexPoint vertex = 0
  originVertex_none : originVertex = none → ∀ vertex,
    embedded.vertexPoint vertex ≠ 0
  choiceNonempty : ∀ face : embedded.Face,
    ∃ choice : GeneralBoundaryPresentation embedded, choice.face = face

namespace TwoDimensionalGeneralBoundaryChoiceData

variable
    {G Gauge Sample Connection : Type*}
    [Group G] [MeasurableSpace G] [Group Gauge] [MeasurableSpace Sample]
    {base : TwoDimensionalGaugeFixedHolonomyMeasureData G Gauge Sample Connection}
    {embedded : TwoDimensionalEmbeddedPlanarGraphData.{uVertex, uEdge, uFace, uXAxisCell} base}
    [DecidableEq embedded.Edge]
    (choices : TwoDimensionalGeneralBoundaryChoiceData base embedded)

/-- The universal carrier of simultaneous valid presentations, not a supplier-selected subfamily. -/
abbrev Choice := GeneralBoundaryChoice embedded

/-- Facewise existence derives existence of a simultaneous universal-carrier choice. -/
theorem choice_nonempty
    (choices : TwoDimensionalGeneralBoundaryChoiceData base embedded) :
    Nonempty (Choice (embedded := embedded)) := by
  classical
  refine ⟨{ presentation := fun face => Classical.choose
              (TwoDimensionalGeneralBoundaryChoiceData.choiceNonempty choices face),
             presentation_face := ?_ }⟩
  intro face
  exact Classical.choose_spec
    (TwoDimensionalGeneralBoundaryChoiceData.choiceNonempty choices face)

/-- Driver Definition 6.3's conditional root-fixing predicate. -/
def FixesDriverOrigin {H : Type*} [One H] (gauge : embedded.Vertex → H) : Prop :=
  ∀ vertex, choices.originVertex = some vertex → gauge vertex = 1

/-- Ordered words selected by one valid presentation. -/
def orderedComponentWords (choice : Choice (embedded := embedded)) (face : embedded.Face) :
    List (List (OrientedEdge embedded.Edge)) :=
  (choice.presentation face).components.map GeneralBoundaryComponentPresentation.word

/-- Exact presentation-dependent boundary holonomy. -/
def boundaryHolonomy
    {H : Type*} [Group H] (choice : Choice (embedded := embedded))
    (face : embedded.Face) (configuration : embedded.Edge → H) : H :=
  finiteBoundaryComponentHolonomy configuration (orderedComponentWords choice face)

/-- Presentation-dependent boundary holonomy is measurable. -/
theorem boundaryHolonomy_measurable
    [MeasurableMul₂ G] [MeasurableInv G] (choice : Choice (embedded := embedded))
    (face : embedded.Face) :
    Measurable (boundaryHolonomy (G := G) (H := G) choice face) :=
  finiteBoundaryComponentHolonomy_measurable (orderedComponentWords choice face)

/-- Every chosen component word is nonempty. -/
theorem componentWord_nonempty
    (choice : Choice (embedded := embedded)) (face : embedded.Face)
    (component : GeneralBoundaryComponentPresentation embedded)
    (membership : component ∈ (choice.presentation face).components) :
    component ∈ (choice.presentation face).components ∧ component.word ≠ [] :=
  ⟨membership, component.word_certificate.nonempty⟩

end TwoDimensionalGeneralBoundaryChoiceData

end

end YangMills.Dimensions
