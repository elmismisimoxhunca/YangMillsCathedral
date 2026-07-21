/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Dimensions.TwoDimensionalGeneralBoundaryTreeFreezingLaw
import YangMills.Mathematics.FiniteGraphRefinement

/-!
# General planar graph refinement consistency

Lévy Definition 1.2.6 says a fine graph refines a coarse graph when every coarse edge is a fine-
graph path. The induced map sends a fine configuration to the holonomies of those paths. Theorem
1.6.1 states that this map is surjective and pushes the fine discrete Yang--Mills measure to the
coarse one; Lemma 1.6.3 gives exact composition.

This module ties that finite map to two embedded graph interfaces over the same ambient continuum
holonomy data and requires exact ambient-edge holonomy compatibility. The uninhabited law then
requires pushforward equality for selected valid boundary presentations of two existing general-
boundary expectation laws indexed by the unchanged density semigroup. Pullback equality of all
eligible coarse observables is derived. No graph, refinement, measure law, or Yang--Mills theory is
constructed.
-/

namespace YangMills.Dimensions

open MeasureTheory
open YangMills.Mathematics

noncomputable section

universe uCoarseVertex uCoarseEdge uCoarseFace uCoarseXAxisCell
  uMiddleVertex uMiddleEdge uMiddleFace uMiddleXAxisCell
  uFineVertex uFineEdge uFineFace uFineXAxisCell

variable
    {G Gauge Sample Connection : Type*}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    [MeasurableMul₂ G] [MeasurableInv G]
    [Group Gauge] [MeasurableSpace Sample]
    {base : TwoDimensionalGaugeFixedHolonomyMeasureData G Gauge Sample Connection}
    {law : TwoDimensionalSelectedLoopHaarDensityLawData base}
    {coarse : TwoDimensionalEmbeddedPlanarGraphData.{uCoarseVertex, uCoarseEdge,
      uCoarseFace, uCoarseXAxisCell} base}
    {fine : TwoDimensionalEmbeddedPlanarGraphData.{uFineVertex, uFineEdge,
      uFineFace, uFineXAxisCell} base}
    [DecidableEq coarse.Edge] [DecidableEq fine.Edge]

/-- Ambient path represented by one oriented embedded edge. -/
def orientedEmbeddedEdgePath
    (graph : TwoDimensionalEmbeddedPlanarGraphData base) :
    OrientedEdge graph.Edge → base.Path
  | .forward edge => graph.edgePath edge
  | .reverse edge => base.reverse (graph.edgePath edge)

/-- Literal concatenated ambient path of one nonempty oriented word. -/
def finiteOrientedAmbientPathFrom
    (graph : TwoDimensionalEmbeddedPlanarGraphData base)
    (first : OrientedEdge graph.Edge) : List (OrientedEdge graph.Edge) → base.Path
  | [] => orientedEmbeddedEdgePath graph first
  | next :: tail => base.concat (orientedEmbeddedEdgePath graph first)
      (finiteOrientedAmbientPathFrom graph next tail)

omit [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [BorelSpace G]
  [MeasurableMul₂ G] [MeasurableInv G]
  [DecidableEq coarse.Edge] [DecidableEq fine.Edge] in
/-- Source, target, and holonomy of the literal concatenated ambient word path. -/
theorem finiteOrientedAmbientPathFrom_spec
    (graph : TwoDimensionalEmbeddedPlanarGraphData base)
    (configurationConnection : Connection)
    (first : OrientedEdge graph.Edge) (tail : List (OrientedEdge graph.Edge))
    (chain : List.IsChain (OrientedEdgeComposable graph.edgeSource graph.edgeTarget)
      (first :: tail)) :
    base.pathSource (finiteOrientedAmbientPathFrom graph first tail) =
        graph.vertexPoint (OrientedEdge.source graph.edgeSource graph.edgeTarget first) ∧
      base.pathTarget (finiteOrientedAmbientPathFrom graph first tail) =
        graph.vertexPoint (OrientedEdge.target graph.edgeSource graph.edgeTarget
          ((first :: tail).getLast (by simp))) ∧
      base.holonomy (finiteOrientedAmbientPathFrom graph first tail) configurationConnection =
        finiteOrientedWordHolonomy
          (fun edge => base.holonomy (graph.edgePath edge) configurationConnection)
          (first :: tail) := by
  induction tail generalizing first with
  | nil =>
      cases first with
      | forward edge =>
          simp [finiteOrientedAmbientPathFrom, orientedEmbeddedEdgePath,
            OrientedEdge.source, OrientedEdge.target, graph.edgePath_source,
            graph.edgePath_target]
      | reverse edge =>
          simp [finiteOrientedAmbientPathFrom, orientedEmbeddedEdgePath,
            OrientedEdge.source, OrientedEdge.target, base.reverse_source,
            base.reverse_target, graph.edgePath_source, graph.edgePath_target,
            base.holonomy_reverse]
  | cons next rest ih =>
      have adjacent : OrientedEdgeComposable graph.edgeSource graph.edgeTarget first next :=
        (List.isChain_cons_cons.mp chain).1
      have restChain : List.IsChain
          (OrientedEdgeComposable graph.edgeSource graph.edgeTarget) (next :: rest) :=
        (List.isChain_cons_cons.mp chain).2
      obtain ⟨restSource, restTarget, restHolonomy⟩ := ih next restChain
      have firstTarget :
          base.pathTarget (orientedEmbeddedEdgePath graph first) =
            graph.vertexPoint (OrientedEdge.target
              graph.edgeSource graph.edgeTarget first) := by
        cases first <;>
          simp [orientedEmbeddedEdgePath, OrientedEdge.target,
            base.reverse_target, graph.edgePath_source, graph.edgePath_target]
      have composable : base.composable (orientedEmbeddedEdgePath graph first)
          (finiteOrientedAmbientPathFrom graph next rest) := by
        rw [base.composable_iff, firstTarget, restSource]
        exact congrArg graph.vertexPoint adjacent
      have firstSource :
          base.pathSource (orientedEmbeddedEdgePath graph first) =
            graph.vertexPoint (OrientedEdge.source
              graph.edgeSource graph.edgeTarget first) := by
        cases first <;>
          simp [orientedEmbeddedEdgePath, OrientedEdge.source,
            base.reverse_source, graph.edgePath_source, graph.edgePath_target]
      refine ⟨?_, ?_, ?_⟩
      · exact (base.concat_source _ _ composable).trans firstSource
      · simpa [finiteOrientedAmbientPathFrom] using
          (base.concat_target _ _ composable).trans restTarget
      · have firstHolonomy :
            base.holonomy (orientedEmbeddedEdgePath graph first) configurationConnection =
              OrientedEdge.eval
                (fun edge => base.holonomy (graph.edgePath edge) configurationConnection) first := by
          cases first <;>
            simp [orientedEmbeddedEdgePath, OrientedEdge.eval, base.holonomy_reverse]
        rw [finiteOrientedAmbientPathFrom, base.holonomy_concat _ _ _ composable,
          restHolonomy, firstHolonomy]
        rfl

/-- Exact geometric/combinatorial refinement between two embedded graph interfaces over the same
ambient holonomy carrier. -/
structure TwoDimensionalEmbeddedGraphRefinementData where
  coarseEdgeNonempty : Nonempty coarse.Edge
  fineEdgeNonempty : Nonempty fine.Edge
  combinatorial : FiniteGraphRefinementData
    coarse.Vertex fine.Vertex coarse.Edge fine.Edge
    coarse.edgeSource coarse.edgeTarget fine.edgeSource fine.edgeTarget
  vertexPoint_coherence : ∀ vertex,
    fine.vertexPoint (combinatorial.vertexMap vertex) = coarse.vertexPoint vertex
  /-- Lévy Definition 1.2.6 literally: each coarse ambient edge path is the concatenated path of
  its selected nonempty fine word, not merely holonomy-equivalent to it. -/
  coarsePath_eq_fineWordPath : ∀ edge,
    coarse.edgePath edge = finiteOrientedAmbientPathFrom fine
      ((combinatorial.edgeWord edge).head (combinatorial.edgeWord_nonempty edge))
      ((combinatorial.edgeWord edge).tail)
  /-- Lévy Theorem 1.6.1's surjectivity at the unchanged selected gauge group. -/
  configurationMap_surjective :
    Function.Surjective (combinatorial.configurationMap (G := G))

namespace TwoDimensionalEmbeddedGraphRefinementData

variable (refinement : TwoDimensionalEmbeddedGraphRefinementData
  (G := G) (coarse := coarse) (fine := fine))

omit [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [BorelSpace G]
  [DecidableEq coarse.Edge] [DecidableEq fine.Edge] in
/-- The exact refinement configuration map is measurable. -/
theorem configurationMap_measurable :
    Measurable (refinement.combinatorial.configurationMap (G := G)) :=
  refinement.combinatorial.configurationMap_measurable

omit [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [BorelSpace G]
  [MeasurableMul₂ G] [MeasurableInv G]
  [DecidableEq coarse.Edge] [DecidableEq fine.Edge] in
/-- Literal fine-path equality derives ambient connection-configuration compatibility. -/
theorem ambientConfiguration_compatibility (connection : Connection) :
    refinement.combinatorial.configurationMap
        (fun fineEdge => base.holonomy (fine.edgePath fineEdge) connection) =
      fun edge => base.holonomy (coarse.edgePath edge) connection := by
  funext edge
  obtain ⟨first, tail, word_eq⟩ := List.exists_cons_of_ne_nil
    (refinement.combinatorial.edgeWord_nonempty edge)
  have chain : List.IsChain
      (OrientedEdgeComposable fine.edgeSource fine.edgeTarget) (first :: tail) := by
    simpa [word_eq] using refinement.combinatorial.edgeWord_chain edge
  have specification := finiteOrientedAmbientPathFrom_spec fine connection first tail chain
  have path_eq := refinement.coarsePath_eq_fineWordPath edge
  simp [word_eq] at path_eq
  rw [FiniteGraphRefinementData.configurationMap,
    finiteEdgeRefinementConfigurationMap, word_eq, ← specification.2.2, ← path_eq]

omit [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [BorelSpace G]
  [MeasurableMul₂ G] [MeasurableInv G]
  [DecidableEq coarse.Edge] [DecidableEq fine.Edge] in
/-- Pointwise form of exact ambient configuration compatibility. -/
theorem ambientConfiguration_compatibility_apply
    (connection : Connection) (edge : coarse.Edge) :
    refinement.combinatorial.configurationMap
        (fun fineEdge => base.holonomy (fine.edgePath fineEdge) connection) edge =
      base.holonomy (coarse.edgePath edge) connection := by
  rw [refinement.ambientConfiguration_compatibility connection]

end TwoDimensionalEmbeddedGraphRefinementData

/-- Source-facing coherence of a coarse-to-middle, middle-to-fine, and direct coarse-to-fine embedded
refinement triple. -/
structure TwoDimensionalEmbeddedGraphRefinementCompositionData
    {middle : TwoDimensionalEmbeddedPlanarGraphData.{uMiddleVertex, uMiddleEdge,
      uMiddleFace, uMiddleXAxisCell} base}
    [DecidableEq middle.Edge]
    (coarseToMiddle : TwoDimensionalEmbeddedGraphRefinementData
      (G := G) (coarse := coarse) (fine := middle))
    (middleToFine : TwoDimensionalEmbeddedGraphRefinementData
      (G := G) (coarse := middle) (fine := fine))
    (coarseToFine : TwoDimensionalEmbeddedGraphRefinementData
      (G := G) (coarse := coarse) (fine := fine)) where
  combinatorial_coherence : FiniteGraphRefinementCompositionData
    coarseToMiddle.combinatorial middleToFine.combinatorial coarseToFine.combinatorial

namespace TwoDimensionalEmbeddedGraphRefinementCompositionData

variable
    {middle : TwoDimensionalEmbeddedPlanarGraphData.{uMiddleVertex, uMiddleEdge,
      uMiddleFace, uMiddleXAxisCell} base}
    [DecidableEq middle.Edge]
    {coarseToMiddle : TwoDimensionalEmbeddedGraphRefinementData
      (G := G) (coarse := coarse) (fine := middle)}
    {middleToFine : TwoDimensionalEmbeddedGraphRefinementData
      (G := G) (coarse := middle) (fine := fine)}
    {coarseToFine : TwoDimensionalEmbeddedGraphRefinementData
      (G := G) (coarse := coarse) (fine := fine)}

omit [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [BorelSpace G]
  [MeasurableMul₂ G] [MeasurableInv G]
  [DecidableEq coarse.Edge] [DecidableEq fine.Edge] in
/-- The direct embedded refinement map is exactly the source-ordered composite. -/
theorem configurationMap_eq_comp
    (data : TwoDimensionalEmbeddedGraphRefinementCompositionData
      coarseToMiddle middleToFine coarseToFine) :
    coarseToFine.combinatorial.configurationMap (G := G) =
      coarseToMiddle.combinatorial.configurationMap ∘
        middleToFine.combinatorial.configurationMap :=
  data.combinatorial_coherence.configurationMap_eq_comp

end TwoDimensionalEmbeddedGraphRefinementCompositionData

variable
    {coarseChoices : TwoDimensionalGeneralBoundaryChoiceData base coarse}
    {fineChoices : TwoDimensionalGeneralBoundaryChoiceData base fine}
    {semigroup : TwoDimensionalSelectedLoopConvolutionSemigroupData law}
    {coarseGeneralLaw : TwoDimensionalGeneralBoundaryExpectationLawData
      (G := G) (choices := coarseChoices) semigroup}
    {fineGeneralLaw : TwoDimensionalGeneralBoundaryExpectationLawData
      (G := G) (choices := fineChoices) semigroup}

/-- Lévy Theorem 1.6.1's exact pushforward law for two selected valid boundary presentations on the
same density-semigroup and ambient-holonomy chain. -/
structure TwoDimensionalGeneralBoundaryRefinementLawData
    (coarseGeneralLaw : TwoDimensionalGeneralBoundaryExpectationLawData
      (G := G) (choices := coarseChoices) semigroup)
    (fineGeneralLaw : TwoDimensionalGeneralBoundaryExpectationLawData
      (G := G) (choices := fineChoices) semigroup)
    (refinement : TwoDimensionalEmbeddedGraphRefinementData
      (G := G) (coarse := coarse) (fine := fine))
    (coarseChoice : TwoDimensionalGeneralBoundaryChoiceData.Choice (embedded := coarse))
    (fineChoice : TwoDimensionalGeneralBoundaryChoiceData.Choice (embedded := fine)) where
  observablePullback : GeneralBoundaryGaugeInvariantGraphObservable
      (G := G) (law := law) (choices := coarseChoices) →
    GeneralBoundaryGaugeInvariantGraphObservable
      (G := G) (law := law) (choices := fineChoices)
  observablePullback_toFun : ∀ observable configuration,
    observablePullback observable configuration =
      observable (refinement.combinatorial.configurationMap configuration)
  physicalObservable_coherence : ∀ observable,
    fineGeneralLaw.physicalObservable (observablePullback observable) =
      coarseGeneralLaw.physicalObservable observable
  pushforward_faceWeightMeasure :
    Measure.map refinement.combinatorial.configurationMap
        (generalBoundarySelectedFaceWeightMeasure (law := law) fineChoice) =
      generalBoundarySelectedFaceWeightMeasure (law := law) coarseChoice

namespace TwoDimensionalGeneralBoundaryRefinementLawData

variable
    {refinement : TwoDimensionalEmbeddedGraphRefinementData
      (G := G) (coarse := coarse) (fine := fine)}
    {coarseChoice : TwoDimensionalGeneralBoundaryChoiceData.Choice (embedded := coarse)}
    {fineChoice : TwoDimensionalGeneralBoundaryChoiceData.Choice (embedded := fine)}

/-- Every eligible coarse observable has the same coarse integral as its exact fine pullback. -/
theorem coarseIntegral_eq_finePullback
    (data : TwoDimensionalGeneralBoundaryRefinementLawData
      (coarseGeneralLaw := coarseGeneralLaw) (fineGeneralLaw := fineGeneralLaw)
      refinement coarseChoice fineChoice)
    (observable : GeneralBoundaryGaugeInvariantGraphObservable
      (G := G) (law := law) (choices := coarseChoices)) :
    (∫ configuration, observable configuration
        ∂(generalBoundarySelectedFaceWeightMeasure (law := law) coarseChoice)) =
      ∫ configuration, observable
          (refinement.combinatorial.configurationMap configuration)
        ∂(generalBoundarySelectedFaceWeightMeasure (law := law) fineChoice) := by
  rw [← data.pushforward_faceWeightMeasure]
  exact integral_map
    refinement.configurationMap_measurable.aemeasurable
    observable.measurable_toFun.aestronglyMeasurable

omit [MeasurableMul₂ G] [MeasurableInv G] in
/-- The designated fine observable is the exact pullback and has the same ambient physical
interpretation under the two existing general-boundary laws. -/
theorem observablePullback_coherence
    (data : TwoDimensionalGeneralBoundaryRefinementLawData
      coarseGeneralLaw fineGeneralLaw refinement coarseChoice fineChoice)
    (observable : GeneralBoundaryGaugeInvariantGraphObservable
      (G := G) (law := law) (choices := coarseChoices)) :
    (∀ configuration, data.observablePullback observable configuration =
      observable (refinement.combinatorial.configurationMap configuration)) ∧
      fineGeneralLaw.physicalObservable (data.observablePullback observable) =
        coarseGeneralLaw.physicalObservable observable :=
  ⟨data.observablePullback_toFun observable,
    data.physicalObservable_coherence observable⟩

/-- Lévy Corollary 1.6.4: every finite tuple of coarse word holonomies has the same law as the
corresponding substituted fine-word tuple. -/
theorem wordHolonomyFamily_law
    (data : TwoDimensionalGeneralBoundaryRefinementLawData
      coarseGeneralLaw fineGeneralLaw refinement coarseChoice fineChoice)
    {Index : Type*} [Fintype Index]
    (words : Index → List (OrientedEdge coarse.Edge)) :
    Measure.map (finiteOrientedWordHolonomyFamily (G := G) words)
        (generalBoundarySelectedFaceWeightMeasure (law := law) coarseChoice) =
      Measure.map (finiteOrientedWordHolonomyFamily (G := G)
        (fun index => refineOrientedWord refinement.combinatorial.edgeWord (words index)))
        (generalBoundarySelectedFaceWeightMeasure (law := law) fineChoice) := by
  rw [← data.pushforward_faceWeightMeasure]
  rw [Measure.map_map
    (finiteOrientedWordHolonomyFamily_measurable words)
    refinement.configurationMap_measurable]
  apply Measure.map_congr
  filter_upwards with configuration
  funext index
  exact (finiteOrientedWordHolonomy_refineOrientedWord
    refinement.combinatorial.edgeWord configuration (words index)).symm

/-- Pairwise source-facing pushforward laws compose along a coherent embedded refinement triple. -/
theorem pushforward_comp
    {middle : TwoDimensionalEmbeddedPlanarGraphData.{uMiddleVertex, uMiddleEdge,
      uMiddleFace, uMiddleXAxisCell} base}
    [DecidableEq middle.Edge]
    {middleChoices : TwoDimensionalGeneralBoundaryChoiceData base middle}
    {middleGeneralLaw : TwoDimensionalGeneralBoundaryExpectationLawData
      (G := G) (choices := middleChoices) semigroup}
    {middleChoice : TwoDimensionalGeneralBoundaryChoiceData.Choice (embedded := middle)}
    {coarseToMiddle : TwoDimensionalEmbeddedGraphRefinementData
      (G := G) (coarse := coarse) (fine := middle)}
    {middleToFine : TwoDimensionalEmbeddedGraphRefinementData
      (G := G) (coarse := middle) (fine := fine)}
    {coarseToFine : TwoDimensionalEmbeddedGraphRefinementData
      (G := G) (coarse := coarse) (fine := fine)}
    (first : TwoDimensionalGeneralBoundaryRefinementLawData
      coarseGeneralLaw middleGeneralLaw coarseToMiddle coarseChoice middleChoice)
    (second : TwoDimensionalGeneralBoundaryRefinementLawData
      middleGeneralLaw fineGeneralLaw middleToFine middleChoice fineChoice)
    (composition : TwoDimensionalEmbeddedGraphRefinementCompositionData
      coarseToMiddle middleToFine coarseToFine) :
    Measure.map coarseToFine.combinatorial.configurationMap
        (generalBoundarySelectedFaceWeightMeasure (law := law) fineChoice) =
      generalBoundarySelectedFaceWeightMeasure (law := law) coarseChoice := by
  rw [composition.configurationMap_eq_comp]
  exact finiteRefinementMeasurePushforward_comp
    (generalBoundarySelectedFaceWeightMeasure (law := law) fineChoice)
    (generalBoundarySelectedFaceWeightMeasure (law := law) middleChoice)
    (generalBoundarySelectedFaceWeightMeasure (law := law) coarseChoice)
    middleToFine.combinatorial.configurationMap
    coarseToMiddle.combinatorial.configurationMap
    middleToFine.configurationMap_measurable
    coarseToMiddle.configurationMap_measurable
    second.pushforward_faceWeightMeasure first.pushforward_faceWeightMeasure

end TwoDimensionalGeneralBoundaryRefinementLawData

end

end YangMills.Dimensions
