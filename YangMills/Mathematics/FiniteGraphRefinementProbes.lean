/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Mathematics.FiniteGraphRefinement

/-!
# Probes for finite graph refinement maps
-/

namespace YangMills.Mathematics.FiniteGraphRefinement.Probes

noncomputable section

universe uCoarseVertex uFineVertex uCoarseEdge uFineEdge uG

/-- Reverse coarse traversal substitutes the exact reverse/flipped fine word. -/
theorem exact_reverse_substitution
    {CoarseEdge : Type uCoarseEdge} {FineEdge : Type uFineEdge}
    (edgeWord : CoarseEdge → List (OrientedEdge FineEdge)) (edge : CoarseEdge) :
    refineOrientedEdge edgeWord (.reverse edge) =
      reverseFiniteOrientedWord (edgeWord edge) :=
  rfl

/-- Holonomy of every substituted word is computed by the induced coarse configuration. -/
theorem exact_substitution_holonomy
    {CoarseEdge : Type uCoarseEdge} {FineEdge : Type uFineEdge}
    {G : Type uG} [Group G]
    (edgeWord : CoarseEdge → List (OrientedEdge FineEdge))
    (configuration : FineEdge → G) (word : List (OrientedEdge CoarseEdge)) :
    finiteOrientedWordHolonomy configuration (refineOrientedWord edgeWord word) =
      finiteOrientedWordHolonomy
        (finiteEdgeRefinementConfigurationMap edgeWord configuration) word :=
  finiteOrientedWordHolonomy_refineOrientedWord edgeWord configuration word

/-- Three-stage refinement composes exactly by word substitution. -/
theorem exact_projective_composition
    {CoarseEdge : Type uCoarseEdge} {MiddleEdge : Type uFineEdge} {FineEdge : Type*}
    {G : Type uG} [Group G]
    (coarseToMiddle : CoarseEdge → List (OrientedEdge MiddleEdge))
    (middleToFine : MiddleEdge → List (OrientedEdge FineEdge))
    (configuration : FineEdge → G) :
    finiteEdgeRefinementConfigurationMap coarseToMiddle
        (finiteEdgeRefinementConfigurationMap middleToFine configuration) =
      finiteEdgeRefinementConfigurationMap
        (fun edge => refineOrientedWord middleToFine (coarseToMiddle edge)) configuration :=
  finiteEdgeRefinementConfigurationMap_comp coarseToMiddle middleToFine configuration

/-- Identity refinement is an actual inhabitant and its map is definitionally pointwise identity. -/
theorem identity_refinement_configuration
    {Vertex : Type uCoarseVertex} {Edge : Type uCoarseEdge} [Fintype Edge]
    (edgeSource edgeTarget : Edge → Vertex) {G : Type uG} [Group G]
    (configuration : Edge → G) :
    (finiteGraphIdentityRefinementData Vertex Edge edgeSource edgeTarget).configurationMap
      configuration = configuration := by
  funext edge
  simp [FiniteGraphRefinementData.configurationMap,
    finiteGraphIdentityRefinementData, finiteEdgeRefinementConfigurationMap]

/-- Endpoint gauge transport is not discarded by refinement. -/
theorem exact_refinement_gauge_transport
    {CoarseVertex : Type uCoarseVertex} {FineVertex : Type uFineVertex}
    {CoarseEdge : Type uCoarseEdge} {FineEdge : Type uFineEdge}
    [Fintype CoarseEdge] [Fintype FineEdge]
    {coarseSource coarseTarget : CoarseEdge → CoarseVertex}
    {fineSource fineTarget : FineEdge → FineVertex}
    (refinement : FiniteGraphRefinementData CoarseVertex FineVertex CoarseEdge FineEdge
      coarseSource coarseTarget fineSource fineTarget)
    {G : Type uG} [Group G] (fineGauge : FineVertex → G)
    (configuration : FineEdge → G) :
    refinement.configurationMap
        (finiteEdgeGaugeAction fineSource fineTarget fineGauge configuration) =
      finiteEdgeGaugeAction coarseSource coarseTarget
        (fun vertex => fineGauge (refinement.vertexMap vertex))
        (refinement.configurationMap configuration) :=
  refinement.configurationMap_gauge fineGauge configuration

/-- Exact measure pushforwards compose, rather than requiring an unrelated third law. -/
theorem exact_pushforward_composition
    {FineConfiguration MiddleConfiguration CoarseConfiguration : Type*}
    [MeasurableSpace FineConfiguration] [MeasurableSpace MiddleConfiguration]
    [MeasurableSpace CoarseConfiguration]
    (fineMeasure : MeasureTheory.Measure FineConfiguration)
    (middleMeasure : MeasureTheory.Measure MiddleConfiguration)
    (coarseMeasure : MeasureTheory.Measure CoarseConfiguration)
    (fineToMiddle : FineConfiguration → MiddleConfiguration)
    (middleToCoarse : MiddleConfiguration → CoarseConfiguration)
    (fineToMiddle_measurable : Measurable fineToMiddle)
    (middleToCoarse_measurable : Measurable middleToCoarse)
    (fine_pushforward : MeasureTheory.Measure.map fineToMiddle fineMeasure = middleMeasure)
    (middle_pushforward : MeasureTheory.Measure.map middleToCoarse middleMeasure = coarseMeasure) :
    MeasureTheory.Measure.map (middleToCoarse ∘ fineToMiddle) fineMeasure = coarseMeasure :=
  finiteRefinementMeasurePushforward_comp fineMeasure middleMeasure coarseMeasure
    fineToMiddle middleToCoarse fineToMiddle_measurable middleToCoarse_measurable
    fine_pushforward middle_pushforward

/-- A certified direct refinement is exactly the composite map, not merely pointwise related on a
selected configuration. -/
theorem exact_certified_refinement_composition
    {CoarseVertex : Type uCoarseVertex} {MiddleVertex : Type uFineVertex}
    {FineVertex : Type*} {CoarseEdge : Type uCoarseEdge}
    {MiddleEdge : Type uFineEdge} {FineEdge : Type*}
    [Fintype CoarseEdge] [Fintype MiddleEdge] [Fintype FineEdge]
    {coarseSource coarseTarget : CoarseEdge → CoarseVertex}
    {middleSource middleTarget : MiddleEdge → MiddleVertex}
    {fineSource fineTarget : FineEdge → FineVertex}
    {coarseToMiddle : FiniteGraphRefinementData
      CoarseVertex MiddleVertex CoarseEdge MiddleEdge
      coarseSource coarseTarget middleSource middleTarget}
    {middleToFine : FiniteGraphRefinementData
      MiddleVertex FineVertex MiddleEdge FineEdge
      middleSource middleTarget fineSource fineTarget}
    {coarseToFine : FiniteGraphRefinementData
      CoarseVertex FineVertex CoarseEdge FineEdge
      coarseSource coarseTarget fineSource fineTarget}
    (composition : FiniteGraphRefinementCompositionData
      coarseToMiddle middleToFine coarseToFine)
    {G : Type uG} [Group G] :
    coarseToFine.configurationMap (G := G) =
      coarseToMiddle.configurationMap ∘ middleToFine.configurationMap :=
  composition.configurationMap_eq_comp

/-- Identity refinement composition is inhabited rather than a consistency-only empty interface. -/
theorem identity_refinement_composition_nonempty
    (Vertex : Type uCoarseVertex) (Edge : Type uCoarseEdge) [Fintype Edge]
    (edgeSource edgeTarget : Edge → Vertex) :
    Nonempty (FiniteGraphRefinementCompositionData
      (finiteGraphIdentityRefinementData Vertex Edge edgeSource edgeTarget)
      (finiteGraphIdentityRefinementData Vertex Edge edgeSource edgeTarget)
      (finiteGraphIdentityRefinementData Vertex Edge edgeSource edgeTarget)) :=
  ⟨finiteGraphIdentityRefinementCompositionData Vertex Edge edgeSource edgeTarget⟩

/-- Empty edge words are rejected before they can collapse every coarse coordinate to the identity. -/
theorem empty_refinement_word_blocked
    {CoarseVertex : Type uCoarseVertex} {FineVertex : Type uFineVertex}
    {CoarseEdge : Type uCoarseEdge} {FineEdge : Type uFineEdge}
    [Fintype CoarseEdge] [Fintype FineEdge]
    {coarseSource coarseTarget : CoarseEdge → CoarseVertex}
    {fineSource fineTarget : FineEdge → FineVertex}
    (refinement : FiniteGraphRefinementData CoarseVertex FineVertex CoarseEdge FineEdge
      coarseSource coarseTarget fineSource fineTarget)
    (edge : CoarseEdge) (claimed : refinement.edgeWord edge = []) : False :=
  refinement.edgeWord_nonempty edge claimed

end

end YangMills.Mathematics.FiniteGraphRefinement.Probes
