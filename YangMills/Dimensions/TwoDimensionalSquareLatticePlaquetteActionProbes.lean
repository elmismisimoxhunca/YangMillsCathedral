/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Dimensions.TwoDimensionalSquareLatticePlaquetteAction

/-!
# Probes for elementary square-lattice plaquette actions
-/

namespace YangMills.Dimensions.TwoDimensionalSquareLatticePlaquetteAction.Probes

noncomputable section

variable {spacing : PositiveLatticeSpacing}

/-- The elementary plaquette at the integer origin. -/
def originPlaquette : EpsilonSquareLatticePlaquette spacing :=
  ⟨(0, 0)⟩

/-- The four bonds form one literally closed counterclockwise path. -/
theorem exact_closed_boundary :
    (originPlaquette (spacing := spacing)).bottomBond.target =
        (originPlaquette (spacing := spacing)).rightBond.source ∧
      (originPlaquette (spacing := spacing)).rightBond.target =
        (originPlaquette (spacing := spacing)).topBond.source ∧
      (originPlaquette (spacing := spacing)).topBond.target =
        (originPlaquette (spacing := spacing)).leftBond.source ∧
      (originPlaquette (spacing := spacing)).leftBond.target =
        (originPlaquette (spacing := spacing)).bottomBond.source :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- The plaquette's physical lower and upper x-coordinates differ by exactly `ε`. -/
theorem exact_physical_width :
    twoDimensionalFirstCoordinate
        (epsilonSquareLatticePoint spacing
          (originPlaquette (spacing := spacing)).bottomBond.target) =
      twoDimensionalFirstCoordinate
        (epsilonSquareLatticePoint spacing
          (originPlaquette (spacing := spacing)).bottomBond.source) + spacing.1 := by
  norm_num [originPlaquette, EpsilonSquareLatticePlaquette.bottomBond]

/-- The source-critical noncommutative order is locked to the reusable finite-word evaluator for
the literal bottom/right/top/left traversal. -/
theorem exact_finite_word_order
    {G : Type*} [Group G]
    (configuration : EpsilonSquareLatticeConfiguration G spacing) :
    epsilonSquareLatticePlaquetteHolonomy
        (originPlaquette (spacing := spacing)) configuration =
      YangMills.Mathematics.finiteOrientedWordHolonomy configuration.value
        (originPlaquette (spacing := spacing)).boundaryWord :=
  epsilonSquareLatticePlaquetteHolonomy_eq_finiteOrientedWordHolonomy _ _

/-- Identity configurations have identity plaquette holonomy. -/
theorem identity_holonomy {G : Type*} [Group G] :
    epsilonSquareLatticePlaquetteHolonomy
      (originPlaquette (spacing := spacing))
      (EpsilonSquareLatticeConfiguration.identity :
        EpsilonSquareLatticeConfiguration G spacing) = 1 := by
  simp [epsilonSquareLatticePlaquetteHolonomy]

/-- The nonconstant axial witness has a nonidentity plaquette holonomy, so the plaquette observable
does not collapse on the axial carrier. -/
theorem rowOneInteger_holonomy_nonidentity :
    epsilonSquareLatticeAxialPlaquetteHolonomy
      (originPlaquette (spacing := spacing))
      EpsilonSquareLatticeAxialConfiguration.rowOneInteger ≠ 1 := by
  norm_num [epsilonSquareLatticeAxialPlaquetteHolonomy,
    epsilonSquareLatticePlaquetteHolonomy, originPlaquette,
    EpsilonSquareLatticePlaquette.leftBond,
    EpsilonSquareLatticePlaquette.topBond,
    EpsilonSquareLatticePlaquette.rightBond,
    EpsilonSquareLatticePlaquette.bottomBond,
    EpsilonSquareLatticeAxialConfiguration.rowOneInteger]

/-- The empty plaquette family has neutral action weight. -/
theorem empty_weight
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (action : TwoDimensionalLatticeActionData G)
    (configuration : EpsilonSquareLatticeAxialConfiguration G spacing) :
    epsilonSquareLatticeFinitePlaquetteActionWeight action ∅ configuration = 1 := by
  simp [epsilonSquareLatticeFinitePlaquetteActionWeight]

/-- A singleton family uses exactly the supplied common action on the exact plaquette holonomy. -/
theorem singleton_weight
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (action : TwoDimensionalLatticeActionData G)
    (configuration : EpsilonSquareLatticeAxialConfiguration G spacing) :
    epsilonSquareLatticeFinitePlaquetteActionWeight action
        {originPlaquette (spacing := spacing)} configuration =
      ENNReal.ofReal (action.action
        (epsilonSquareLatticeAxialPlaquetteHolonomy
          (originPlaquette (spacing := spacing)) configuration)) := by
  simp [epsilonSquareLatticeFinitePlaquetteActionWeight]

/-- With measurable multiplication, every exact finite plaquette product is measurable. -/
theorem exact_weight_measurable
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [MeasurableSpace G] [BorelSpace G] [MeasurableMul₂ G]
    (action : TwoDimensionalLatticeActionData G)
    (plaquettes : Finset (EpsilonSquareLatticePlaquette spacing)) :
    Measurable (epsilonSquareLatticeFinitePlaquetteActionWeight action plaquettes) :=
  epsilonSquareLatticeFinitePlaquetteActionWeight.measurable action plaquettes

/-- Strict action positivity rejects a zero finite plaquette weight. -/
theorem zero_weight_blocked
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (action : TwoDimensionalLatticeActionData G)
    (plaquettes : Finset (EpsilonSquareLatticePlaquette spacing))
    (configuration : EpsilonSquareLatticeAxialConfiguration G spacing)
    (claimed : epsilonSquareLatticeFinitePlaquetteActionWeight
      action plaquettes configuration = 0) : False :=
  (epsilonSquareLatticeFinitePlaquetteActionWeight.ne_zero
    action plaquettes configuration) claimed

end

end YangMills.Dimensions.TwoDimensionalSquareLatticePlaquetteAction.Probes
