/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Dimensions.TwoDimensionalGeneralBoundaryRefinementLaw

/-!
# Probes for general planar graph refinement consistency
-/

namespace YangMills.Dimensions.TwoDimensionalGeneralBoundaryRefinementLaw.Probes

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
    {coarseChoices : TwoDimensionalGeneralBoundaryChoiceData base coarse}
    {fineChoices : TwoDimensionalGeneralBoundaryChoiceData base fine}
    {semigroup : TwoDimensionalSelectedLoopConvolutionSemigroupData law}
    {coarseGeneralLaw : TwoDimensionalGeneralBoundaryExpectationLawData
      (G := G) (choices := coarseChoices) semigroup}
    {fineGeneralLaw : TwoDimensionalGeneralBoundaryExpectationLawData
      (G := G) (choices := fineChoices) semigroup}
    {refinement : TwoDimensionalEmbeddedGraphRefinementData
      (G := G) (coarse := coarse) (fine := fine)}
    {coarseChoice : TwoDimensionalGeneralBoundaryChoiceData.Choice (embedded := coarse)}
    {fineChoice : TwoDimensionalGeneralBoundaryChoiceData.Choice (embedded := fine)}
    (data : TwoDimensionalGeneralBoundaryRefinementLawData
      coarseGeneralLaw fineGeneralLaw refinement coarseChoice fineChoice)

omit [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [BorelSpace G]
  [MeasurableMul₂ G] [MeasurableInv G]
  [DecidableEq coarse.Edge] [DecidableEq fine.Edge] in
/-- Coarse vertices retain their exact ambient points. -/
theorem exact_vertex_point_coherence (vertex : coarse.Vertex) :
    fine.vertexPoint (refinement.combinatorial.vertexMap vertex) = coarse.vertexPoint vertex :=
  refinement.vertexPoint_coherence vertex

omit [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [BorelSpace G]
  [MeasurableMul₂ G] [MeasurableInv G]
  [DecidableEq coarse.Edge] [DecidableEq fine.Edge] in
/-- Source-facing refinements have actual coarse and fine edges, blocking empty-coordinate vacuity. -/
theorem exact_nonempty_edge_carriers
    (refinement : TwoDimensionalEmbeddedGraphRefinementData
      (G := G) (coarse := coarse) (fine := fine)) :
    Nonempty coarse.Edge ∧ Nonempty fine.Edge :=
  ⟨refinement.coarseEdgeNonempty, refinement.fineEdgeNonempty⟩

omit [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [BorelSpace G]
  [MeasurableMul₂ G] [MeasurableInv G]
  [DecidableEq coarse.Edge] [DecidableEq fine.Edge] in
/-- Lévy fineness is literal ambient-path equality, not merely equality of holonomies. -/
theorem exact_coarse_path_is_fine_word_path (edge : coarse.Edge) :
    coarse.edgePath edge = finiteOrientedAmbientPathFrom fine
      ((refinement.combinatorial.edgeWord edge).head
        (refinement.combinatorial.edgeWord_nonempty edge))
      ((refinement.combinatorial.edgeWord edge).tail) :=
  refinement.coarsePath_eq_fineWordPath edge

omit [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [BorelSpace G]
  [MeasurableMul₂ G] [MeasurableInv G]
  [DecidableEq coarse.Edge] [DecidableEq fine.Edge] in
/-- Every coarse ambient edge holonomy is exactly its fine-word holonomy. -/
theorem exact_ambient_holonomy_coherence
    (connection : Connection) (edge : coarse.Edge) :
    refinement.combinatorial.configurationMap
        (fun fineEdge => base.holonomy (fine.edgePath fineEdge) connection) edge =
      base.holonomy (coarse.edgePath edge) connection :=
  refinement.ambientConfiguration_compatibility_apply connection edge

omit [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [BorelSpace G]
  [MeasurableMul₂ G] [MeasurableInv G]
  [DecidableEq coarse.Edge] [DecidableEq fine.Edge] in
/-- Lévy Theorem 1.6.1 surjectivity is retained at the exact gauge group. -/
theorem exact_refinement_surjectivity :
    Function.Surjective (refinement.combinatorial.configurationMap (G := G)) :=
  refinement.configurationMap_surjective

omit [MeasurableMul₂ G] [MeasurableInv G] in
/-- The law is exact pushforward equality, not merely equality of selected expectations. -/
theorem exact_measure_pushforward
    (data : TwoDimensionalGeneralBoundaryRefinementLawData
      coarseGeneralLaw fineGeneralLaw refinement coarseChoice fineChoice) :
    Measure.map refinement.combinatorial.configurationMap
        (generalBoundarySelectedFaceWeightMeasure (law := law) fineChoice) =
      generalBoundarySelectedFaceWeightMeasure (law := law) coarseChoice :=
  data.pushforward_faceWeightMeasure

omit [MeasurableMul₂ G] [MeasurableInv G] in
/-- The two pre-existing general laws are joined by an exact eligible-observable pullback and the
same ambient physical observable. -/
theorem exact_general_law_observable_coherence
    (data : TwoDimensionalGeneralBoundaryRefinementLawData
      coarseGeneralLaw fineGeneralLaw refinement coarseChoice fineChoice)
    (observable : GeneralBoundaryGaugeInvariantGraphObservable
      (G := G) (law := law) (choices := coarseChoices)) :
    (∀ configuration, data.observablePullback observable configuration =
      observable (refinement.combinatorial.configurationMap configuration)) ∧
      fineGeneralLaw.physicalObservable (data.observablePullback observable) =
        coarseGeneralLaw.physicalObservable observable :=
  data.observablePullback_coherence observable

/-- Every eligible coarse observable has the exact fine pullback integral. -/
theorem exact_observable_projective_consistency
    (data : TwoDimensionalGeneralBoundaryRefinementLawData
      coarseGeneralLaw fineGeneralLaw refinement coarseChoice fineChoice)
    (observable : GeneralBoundaryGaugeInvariantGraphObservable
      (G := G) (law := law) (choices := coarseChoices)) :
    (∫ configuration, observable configuration
        ∂(generalBoundarySelectedFaceWeightMeasure (law := law) coarseChoice)) =
      ∫ configuration, observable
          (refinement.combinatorial.configurationMap configuration)
        ∂(generalBoundarySelectedFaceWeightMeasure (law := law) fineChoice) :=
  data.coarseIntegral_eq_finePullback observable

/-- Every finite tuple of coarse word holonomies has the same law as its substituted fine tuple. -/
theorem exact_word_holonomy_family_law
    (data : TwoDimensionalGeneralBoundaryRefinementLawData
      coarseGeneralLaw fineGeneralLaw refinement coarseChoice fineChoice)
    {Index : Type*} [Fintype Index]
    (words : Index → List (OrientedEdge coarse.Edge)) :
    Measure.map (finiteOrientedWordHolonomyFamily (G := G) words)
        (generalBoundarySelectedFaceWeightMeasure (law := law) coarseChoice) =
      Measure.map (finiteOrientedWordHolonomyFamily (G := G)
        (fun index => refineOrientedWord refinement.combinatorial.edgeWord (words index)))
        (generalBoundarySelectedFaceWeightMeasure (law := law) fineChoice) :=
  data.wordHolonomyFamily_law words

/-- Pairwise exact pushforwards derive the direct source-facing projective law. -/
theorem exact_source_facing_pushforward_composition
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
      generalBoundarySelectedFaceWeightMeasure (law := law) coarseChoice :=
  TwoDimensionalGeneralBoundaryRefinementLawData.pushforward_comp
    first second composition

omit [MeasurableMul₂ G] [MeasurableInv G] in
/-- A substituted unrelated coarse measure is rejected whenever it differs from the exact one. -/
theorem unrelated_coarse_measure_blocked
    (data : TwoDimensionalGeneralBoundaryRefinementLawData
      coarseGeneralLaw fineGeneralLaw refinement coarseChoice fineChoice)
    (wrong : Measure (coarse.Edge → G))
    (different : wrong ≠ generalBoundarySelectedFaceWeightMeasure (law := law) coarseChoice)
    (claimed : Measure.map refinement.combinatorial.configurationMap
      (generalBoundarySelectedFaceWeightMeasure (law := law) fineChoice) = wrong) : False := by
  apply different
  rw [← claimed]
  exact data.pushforward_faceWeightMeasure

omit [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [BorelSpace G]
  [MeasurableMul₂ G] [MeasurableInv G]
  [DecidableEq coarse.Edge] [DecidableEq fine.Edge] in
/-- Substituting a holonomy-equivalent but literally different path is rejected. -/
theorem nonliteral_coarse_path_blocked
    (edge : coarse.Edge) (wrongPath : base.Path)
    (different : wrongPath ≠ finiteOrientedAmbientPathFrom fine
      ((refinement.combinatorial.edgeWord edge).head
        (refinement.combinatorial.edgeWord_nonempty edge))
      ((refinement.combinatorial.edgeWord edge).tail))
    (claimed : coarse.edgePath edge = wrongPath) : False := by
  apply different
  rw [← claimed]
  exact refinement.coarsePath_eq_fineWordPath edge

omit [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [BorelSpace G]
  [MeasurableMul₂ G] [MeasurableInv G]
  [DecidableEq coarse.Edge] [DecidableEq fine.Edge] in
/-- A wrong ambient refinement map is blocked at any detected connection/edge mismatch. -/
theorem wrong_ambient_holonomy_blocked
    (wrongMap : (fine.Edge → G) → coarse.Edge → G)
    (connection : Connection) (edge : coarse.Edge)
    (different : wrongMap (fun fineEdge => base.holonomy (fine.edgePath fineEdge) connection) edge ≠
      base.holonomy (coarse.edgePath edge) connection)
    (claimed : wrongMap = refinement.combinatorial.configurationMap) : False := by
  apply different
  rw [claimed]
  exact refinement.ambientConfiguration_compatibility_apply connection edge

/-- Refinement consistency remains strictly two-dimensional. -/
theorem refinement_not_four_dimensional :
    EuclideanDimension.two ≠ EuclideanDimension.four :=
  EuclideanDimension.two_ne_four

end

end YangMills.Dimensions.TwoDimensionalGeneralBoundaryRefinementLaw.Probes
