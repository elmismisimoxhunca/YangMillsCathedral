/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Dimensions.TwoDimensionalSquareLatticeBoxProjectiveSequence

/-!
# Hostile probes for the exhaustive square-box projective sequence
-/

namespace YangMills.Dimensions.TwoDimensionalSquareLatticeBoxProjectiveSequence.Probes

open MeasureTheory

noncomputable section

universe uG

/-- Projective radii are exactly the positive sequence `stage + 1`. -/
theorem exact_projective_radius (stage : ℕ) :
    (squareLatticeBoxProjectiveRadius stage).1 = stage + 1 ∧
      squareLatticeBoxProjectiveRadius (stage + 1) =
        squareLatticeBoxSuccessorRadius (squareLatticeBoxProjectiveRadius stage) :=
  ⟨squareLatticeBoxProjectiveRadius_value stage,
    squareLatticeBoxProjectiveRadius_succ stage⟩

/-- Every off-tree bond is retained eventually in one of the exact two orientations. -/
theorem exact_bond_exhaustion
    {spacing : PositiveLatticeSpacing}
    (bond : EpsilonSquareLatticeDirectedBond spacing)
    (notTree : ¬ epsilonSquareLatticeIsAxialTreeBond bond) :
    ∃ stage, ∃ coordinate : EpsilonSquareLatticeBoxCoordinate spacing
        (squareLatticeBoxProjectiveRadius stage),
      bond = coordinate.1 ∨ bond = coordinate.1.reverse :=
  squareLatticeBoxProjectiveRadius_bond_eventually_represented bond notTree

/-- Every elementary plaquette is retained eventually with literal plaquette equality. -/
theorem exact_plaquette_exhaustion
    {spacing : PositiveLatticeSpacing}
    (plaquette : EpsilonSquareLatticePlaquette spacing) :
    ∃ stage, ∃ label : EpsilonSquareLatticeBoxPlaquette spacing
        (squareLatticeBoxProjectiveRadius stage),
      label.1 = plaquette :=
  squareLatticeBoxProjectiveRadius_plaquette_eventually_selected plaquette

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    [MeasurableMul₂ G] [MeasurableInv G]
    (spacing : PositiveLatticeSpacing) (action : TwoDimensionalLatticeActionData G)

/-- The exhaustive projective-sequence interface is now concretely inhabited by exact boxes. -/
@[reducible] def exact_constructed_sequence :
    TwoDimensionalFiniteAxialProjectiveSequenceData (spacing := spacing) action :=
  twoDimensionalSquareLatticeBoxProjectiveSequenceData spacing action

/-- The constructed sequence retains exact consecutive finite-law projectivity. -/
theorem exact_sequence_pushforward (stage : ℕ) :
    Measure.map
      (fun configuration coordinate => configuration
        ((twoDimensionalSquareLatticeBoxProjectiveSequenceData spacing action).coordinateInclusion
          stage coordinate))
      (twoDimensionalFiniteAxialMeasure action
        ((twoDimensionalSquareLatticeBoxProjectiveSequenceData spacing action).presentation
          (stage + 1))) =
      twoDimensionalFiniteAxialMeasure action
        ((twoDimensionalSquareLatticeBoxProjectiveSequenceData spacing action).presentation stage) :=
  (twoDimensionalSquareLatticeBoxProjectiveSequenceData spacing action).finiteMeasure_projective
    stage

/-- Omitting one off-tree bond from every stage contradicts the constructed exhaustion theorem. -/
theorem permanently_missing_bond_blocked
    (bond : EpsilonSquareLatticeDirectedBond spacing)
    (notTree : ¬ epsilonSquareLatticeIsAxialTreeBond bond)
    (absent : ∀ stage, ∀ coordinate : EpsilonSquareLatticeBoxCoordinate spacing
      (squareLatticeBoxProjectiveRadius stage),
      bond ≠ coordinate.1 ∧ bond ≠ coordinate.1.reverse) : False := by
  obtain ⟨stage, coordinate, forward | reverse⟩ :=
    squareLatticeBoxProjectiveRadius_bond_eventually_represented bond notTree
  · exact (absent stage coordinate).1 forward
  · exact (absent stage coordinate).2 reverse

/-- Omitting one plaquette from every stage contradicts literal plaquette exhaustion. -/
theorem permanently_missing_plaquette_blocked
    (plaquette : EpsilonSquareLatticePlaquette spacing)
    (absent : ∀ stage, ∀ label : EpsilonSquareLatticeBoxPlaquette spacing
      (squareLatticeBoxProjectiveRadius stage), label.1 ≠ plaquette) : False := by
  obtain ⟨stage, label, equality⟩ :=
    squareLatticeBoxProjectiveRadius_plaquette_eventually_selected plaquette
  exact absent stage label equality

/-- The finite sequence still does not identify its two-dimensional evidence with the 4D endpoint. -/
theorem projective_sequence_not_four_dimensional :
    EuclideanDimension.two ≠ EuclideanDimension.four :=
  EuclideanDimension.two_ne_four

end

end YangMills.Dimensions.TwoDimensionalSquareLatticeBoxProjectiveSequence.Probes
