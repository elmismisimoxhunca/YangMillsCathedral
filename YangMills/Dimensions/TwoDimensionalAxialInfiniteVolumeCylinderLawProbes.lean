/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Dimensions.TwoDimensionalAxialInfiniteVolumeCylinderLaw
import YangMills.Foundation.DimensionsProbes

/-!
# Probes for Driver's axial infinite-volume cylinder contract
-/

namespace YangMills.Dimensions.TwoDimensionalAxialInfiniteVolumeCylinderLaw.Probes

open MeasureTheory Set

noncomputable section

universe uG uCoordinate uPlaquette

variable
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [MeasurableSpace G] [BorelSpace G] [MeasurableMul₂ G]
    {spacing : PositiveLatticeSpacing}
    {action : TwoDimensionalLatticeActionData G}
    (sequence : TwoDimensionalFiniteAxialProjectiveSequenceData.{uG, uCoordinate, uPlaquette}
      (spacing := spacing) action)

omit [MeasurableMul₂ G] in
/-- Coordinate inclusions are injective and retain the identical infinite directed bond. -/
theorem exact_coordinate_nesting (stage : ℕ) :
    Function.Injective (sequence.coordinateInclusion stage) ∧
      (∀ coordinate,
        (sequence.presentation (stage + 1)).coordinateBond
            (sequence.coordinateInclusion stage coordinate) =
          (sequence.presentation stage).coordinateBond coordinate) :=
  ⟨sequence.coordinateInclusion_injective stage,
    sequence.coordinateBond_inclusion stage⟩

omit [MeasurableMul₂ G] in
/-- Plaquette inclusions are injective and retain the identical elementary plaquette. -/
theorem exact_plaquette_nesting (stage : ℕ) :
    Function.Injective (sequence.plaquetteInclusion stage) ∧
      (∀ label,
        (sequence.presentation (stage + 1)).plaquette
            (sequence.plaquetteInclusion stage label) =
          (sequence.presentation stage).plaquette label) :=
  ⟨sequence.plaquetteInclusion_injective stage,
    sequence.plaquette_inclusion stage⟩

omit [MeasurableMul₂ G] in
/-- Consecutive finite laws are related by the exact stored coordinate restriction. -/
theorem exact_projective_consistency (stage : ℕ) :
    Measure.map
        (fun configuration coordinate =>
          configuration (sequence.coordinateInclusion stage coordinate))
        (twoDimensionalFiniteAxialMeasure action (sequence.presentation (stage + 1))) =
      twoDimensionalFiniteAxialMeasure action (sequence.presentation stage) :=
  sequence.finiteMeasure_projective stage

omit [MeasurableMul₂ G] in
/-- Every off-tree bond eventually appears in one represented orientation. -/
theorem exact_bond_exhaustion
    (bond : EpsilonSquareLatticeDirectedBond spacing)
    (notTree : ¬ epsilonSquareLatticeIsAxialTreeBond bond) :
    ∃ stage coordinate,
      bond = (sequence.presentation stage).coordinateBond coordinate ∨
        bond = ((sequence.presentation stage).coordinateBond coordinate).reverse :=
  sequence.bond_eventually_represented bond notTree

omit [MeasurableMul₂ G] in
/-- Every elementary plaquette eventually appears. -/
theorem exact_plaquette_exhaustion
    (plaquette : EpsilonSquareLatticePlaquette spacing) :
    ∃ stage label, (sequence.presentation stage).plaquette label = plaquette :=
  sequence.plaquette_eventually_selected plaquette

omit [MeasurableMul₂ G] in
/-- A permanently missing elementary plaquette is hostilely rejected. -/
theorem missing_plaquette_blocked
    (plaquette : EpsilonSquareLatticePlaquette spacing)
    (absent : ∀ stage label,
      (sequence.presentation stage).plaquette label ≠ plaquette) : False := by
  obtain ⟨stage, label, equality⟩ := sequence.plaquette_eventually_selected plaquette
  exact absent stage label equality

omit [MeasurableMul₂ G] in
/-- A permanently missing off-tree bond is hostilely rejected. -/
theorem missing_bond_blocked
    (bond : EpsilonSquareLatticeDirectedBond spacing)
    (notTree : ¬ epsilonSquareLatticeIsAxialTreeBond bond)
    (absent : ∀ stage coordinate,
      bond ≠ (sequence.presentation stage).coordinateBond coordinate ∧
        bond ≠ ((sequence.presentation stage).coordinateBond coordinate).reverse) : False :=
  sequence.no_permanently_unrepresented_bond bond notTree absent

omit [MeasurableMul₂ G] in
/-- Every finite stage is itself normalized by its exact partition-function certificate. -/
theorem exact_finite_stage_normalized (stage : ℕ) :
    twoDimensionalFiniteAxialMeasure action (sequence.presentation stage) univ = 1 :=
  twoDimensionalFiniteAxialMeasure.apply_univ action (sequence.presentation stage)
    (sequence.normalizer stage)

omit [MeasurableMul₂ G] in
/-- The fragment postulates exact equality on every finite-coordinate cylinder; no uniqueness is
inferred here. -/
theorem exact_infinite_cylinder_law
    (law : TwoDimensionalAxialInfiniteVolumeCylinderLawData
      (spacing := spacing) action sequence)
    (stage : ℕ) :
    Measure.map
        (fun configuration coordinate =>
          configuration ((sequence.presentation stage).coordinateBond coordinate))
        law.probabilityMeasure =
      twoDimensionalFiniteAxialMeasure action (sequence.presentation stage) :=
  law.finiteCylinderLaw stage

omit [MeasurableMul₂ G] in
/-- Represented one-bond marginals are derived from the same finite cylinder law. -/
theorem exact_represented_marginal
    (law : TwoDimensionalAxialInfiniteVolumeCylinderLawData
      (spacing := spacing) action sequence)
    (stage : ℕ) (coordinate : (sequence.presentation stage).Coordinate) :
    Measure.map
        (fun configuration : EpsilonSquareLatticeAxialConfiguration G spacing =>
          configuration ((sequence.presentation stage).coordinateBond coordinate))
        law.probabilityMeasure =
      Measure.map
        (fun configuration : (sequence.presentation stage).Coordinate → G =>
          configuration coordinate)
        (twoDimensionalFiniteAxialMeasure action (sequence.presentation stage)) :=
  law.represented_coordinate_marginal stage coordinate

omit [MeasurableMul₂ G] in
/-- A zero infinite-volume law is rejected by probability normalization. -/
theorem zero_infinite_measure_blocked
    (law : TwoDimensionalAxialInfiniteVolumeCylinderLawData
      (spacing := spacing) action sequence)
    (claimed : law.probabilityMeasure = 0) : False :=
  law.probabilityMeasure_ne_zero claimed

/-- The two-dimensional infinite cylinder contract cannot inhabit the four-dimensional endpoint. -/
theorem infinite_cylinder_not_four_dimensional :
    EuclideanDimension.two ≠ EuclideanDimension.four :=
  EuclideanDimension.two_ne_four

end

end YangMills.Dimensions.TwoDimensionalAxialInfiniteVolumeCylinderLaw.Probes
