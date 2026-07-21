/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Dimensions.TwoDimensionalFiniteAxialPushforwardMeasure

/-!
# Projective finite axial laws and an infinite-volume cylinder contract

Motivated by the cylinder conclusion inside Driver Theorem 7.2, this module records an exhaustive nested family of the existing finite presentations, exact
pushforward consistency under coordinate restriction, and a probability measure on the exact
infinite axial carrier whose every finite-coordinate law is the corresponding normalized finite
measure.

This is uninhabited acceptance data. It constructs no box sequence, infinite-volume measure, weak
limit, lattice-continuum limit, Yang--Mills theory, or mass gap.
-/

namespace YangMills.Dimensions

open MeasureTheory Set

noncomputable section

universe uG uCoordinate uPlaquette

variable
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [MeasurableSpace G] [BorelSpace G] [MeasurableMul₂ G]
    {spacing : PositiveLatticeSpacing}

/-- Exhaustive nested finite presentations with exact projective finite-volume laws. -/
structure TwoDimensionalFiniteAxialProjectiveSequenceData
    (action : TwoDimensionalLatticeActionData G) where
  presentation : ℕ →
    TwoDimensionalFiniteAxialPlaquettePresentationData.{uG, uCoordinate, uPlaquette} G spacing
  normalizer : ∀ stage,
    TwoDimensionalFiniteAxialNormalizerData action (presentation stage)
  coordinateInclusion : ∀ stage,
    (presentation stage).Coordinate → (presentation (stage + 1)).Coordinate
  coordinateInclusion_injective : ∀ stage,
    Function.Injective (coordinateInclusion stage)
  coordinateBond_inclusion : ∀ stage coordinate,
    (presentation (stage + 1)).coordinateBond (coordinateInclusion stage coordinate) =
      (presentation stage).coordinateBond coordinate
  plaquetteInclusion : ∀ stage,
    (presentation stage).Plaquette → (presentation (stage + 1)).Plaquette
  plaquetteInclusion_injective : ∀ stage,
    Function.Injective (plaquetteInclusion stage)
  plaquette_inclusion : ∀ stage label,
    (presentation (stage + 1)).plaquette (plaquetteInclusion stage label) =
      (presentation stage).plaquette label
  /-- Every off-tree directed bond eventually occurs, in one of its two orientations. -/
  bond_eventually_represented : ∀ bond,
    ¬ epsilonSquareLatticeIsAxialTreeBond bond →
      ∃ stage coordinate,
        bond = (presentation stage).coordinateBond coordinate ∨
          bond = ((presentation stage).coordinateBond coordinate).reverse
  /-- Every elementary plaquette eventually occurs. -/
  plaquette_eventually_selected : ∀ plaquette,
    ∃ stage label, (presentation stage).plaquette label = plaquette
  /-- Exact finite-law pushforward under coordinate restriction. -/
  finiteMeasure_projective : ∀ stage,
    Measure.map
        (fun configuration coordinate => configuration (coordinateInclusion stage coordinate))
        (twoDimensionalFiniteAxialMeasure action (presentation (stage + 1))) =
      twoDimensionalFiniteAxialMeasure action (presentation stage)

namespace TwoDimensionalFiniteAxialProjectiveSequenceData

variable {action : TwoDimensionalLatticeActionData G}

omit [MeasurableMul₂ G] in
/-- Coordinate restriction between consecutive finite stages is measurable. -/
theorem coordinateRestriction_measurable
    (sequence : TwoDimensionalFiniteAxialProjectiveSequenceData (spacing := spacing) action)
    (stage : ℕ) :
    Measurable (fun (configuration : (sequence.presentation (stage + 1)).Coordinate → G)
      (coordinate : (sequence.presentation stage).Coordinate) =>
        configuration (sequence.coordinateInclusion stage coordinate)) := by
  letI := (sequence.presentation stage).coordinateFintype
  letI := (sequence.presentation (stage + 1)).coordinateFintype
  apply measurable_pi_iff.mpr
  intro coordinate
  exact measurable_pi_apply (sequence.coordinateInclusion stage coordinate)

omit [MeasurableMul₂ G] in
/-- Cofinality rejects an off-tree bond that is absent from every stage. -/
theorem no_permanently_unrepresented_bond
    (sequence : TwoDimensionalFiniteAxialProjectiveSequenceData (spacing := spacing) action)
    (bond : EpsilonSquareLatticeDirectedBond spacing)
    (notTree : ¬ epsilonSquareLatticeIsAxialTreeBond bond)
    (absent : ∀ stage coordinate,
      bond ≠ (sequence.presentation stage).coordinateBond coordinate ∧
        bond ≠ ((sequence.presentation stage).coordinateBond coordinate).reverse) : False := by
  obtain ⟨stage, coordinate, forward | reverse⟩ :=
    sequence.bond_eventually_represented bond notTree
  · exact (absent stage coordinate).1 forward
  · exact (absent stage coordinate).2 reverse

end TwoDimensionalFiniteAxialProjectiveSequenceData

/-- Projective infinite axial cylinder-law fragment. It postulates every finite restriction but does
not assert measure uniqueness, square-box origin, weak convergence, or boundary independence. -/
structure TwoDimensionalAxialInfiniteVolumeCylinderLawData
    (action : TwoDimensionalLatticeActionData G)
    (sequence : TwoDimensionalFiniteAxialProjectiveSequenceData (spacing := spacing) action) where
  probabilityMeasure : Measure (EpsilonSquareLatticeAxialConfiguration G spacing)
  probability_normalized : probabilityMeasure univ = 1
  /-- Exact restriction to every finite represented coordinate family. -/
  finiteCylinderLaw : ∀ stage,
    Measure.map
        (fun configuration coordinate =>
          configuration ((sequence.presentation stage).coordinateBond coordinate))
        probabilityMeasure =
      twoDimensionalFiniteAxialMeasure action (sequence.presentation stage)

namespace TwoDimensionalAxialInfiniteVolumeCylinderLawData

variable
    {action : TwoDimensionalLatticeActionData G}
    {sequence : TwoDimensionalFiniteAxialProjectiveSequenceData (spacing := spacing) action}

omit [MeasurableMul₂ G] in
/-- The accepted infinite-volume probability measure cannot be zero. -/
theorem probabilityMeasure_ne_zero
    (law : TwoDimensionalAxialInfiniteVolumeCylinderLawData (spacing := spacing) action sequence) :
    law.probabilityMeasure ≠ 0 := by
  intro zeroMeasure
  have normalized := law.probability_normalized
  rw [zeroMeasure] at normalized
  simp at normalized

omit [MeasurableMul₂ G] in
/-- Every represented bond has exactly its corresponding finite-stage one-coordinate marginal. -/
theorem represented_coordinate_marginal
    (law : TwoDimensionalAxialInfiniteVolumeCylinderLawData (spacing := spacing) action sequence)
    (stage : ℕ) (coordinate : (sequence.presentation stage).Coordinate) :
    Measure.map
        (fun configuration : EpsilonSquareLatticeAxialConfiguration G spacing =>
          configuration ((sequence.presentation stage).coordinateBond coordinate))
        law.probabilityMeasure =
      Measure.map
        (fun configuration : (sequence.presentation stage).Coordinate → G =>
          configuration coordinate)
        (twoDimensionalFiniteAxialMeasure action (sequence.presentation stage)) := by
  letI := (sequence.presentation stage).coordinateFintype
  rw [← law.finiteCylinderLaw stage]
  rw [Measure.map_map
    (measurable_pi_apply coordinate)
    (by
      apply measurable_pi_iff.mpr
      intro index
      exact EpsilonSquareLatticeAxialConfiguration.measurable_apply
        ((sequence.presentation stage).coordinateBond index))]
  apply Measure.map_congr
  filter_upwards [] with configuration
  rfl

end TwoDimensionalAxialInfiniteVolumeCylinderLawData

end

end YangMills.Dimensions
