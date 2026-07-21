/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Dimensions.TwoDimensionalInfiniteSquareLatticeConfiguration
import YangMills.Dimensions.TwoDimensionalLatticeAction
import YangMills.Mathematics.FiniteOrientedEdgeWord

/-!
# Elementary square plaquettes and finite action products

This module defines the exact counterclockwise elementary plaquette in Driver's scaled square
lattice, its holonomy with the project's later-traversal-on-the-left convention, and finite products
of a single Definition 7.1 action over plaquettes. It is measure-free groundwork: no finite-volume
normalizer, Gibbs measure, infinite-volume limit, or continuum convergence is supplied.
-/

namespace YangMills.Dimensions

open MeasureTheory

noncomputable section

/-- An elementary `ε × ε` plaquette, indexed by its integer lower-left site. -/
structure EpsilonSquareLatticePlaquette (spacing : PositiveLatticeSpacing) where
  lowerLeft : ℤ × ℤ
  deriving DecidableEq

namespace EpsilonSquareLatticePlaquette

variable {spacing : PositiveLatticeSpacing}

/-- Bottom edge, traversed to the right. -/
def bottomBond (plaquette : EpsilonSquareLatticePlaquette spacing) :
    EpsilonSquareLatticeDirectedBond spacing where
  source := plaquette.lowerLeft
  target := (plaquette.lowerLeft.1 + 1, plaquette.lowerLeft.2)
  nearestNeighbor := Or.inl ⟨Or.inl rfl, rfl⟩

/-- Right edge, traversed upward. -/
def rightBond (plaquette : EpsilonSquareLatticePlaquette spacing) :
    EpsilonSquareLatticeDirectedBond spacing where
  source := (plaquette.lowerLeft.1 + 1, plaquette.lowerLeft.2)
  target := (plaquette.lowerLeft.1 + 1, plaquette.lowerLeft.2 + 1)
  nearestNeighbor := Or.inr ⟨Or.inl rfl, rfl⟩

/-- Top edge, traversed to the left. -/
def topBond (plaquette : EpsilonSquareLatticePlaquette spacing) :
    EpsilonSquareLatticeDirectedBond spacing where
  source := (plaquette.lowerLeft.1 + 1, plaquette.lowerLeft.2 + 1)
  target := (plaquette.lowerLeft.1, plaquette.lowerLeft.2 + 1)
  nearestNeighbor := Or.inl ⟨Or.inr (by omega), rfl⟩

/-- Left edge, traversed downward. -/
def leftBond (plaquette : EpsilonSquareLatticePlaquette spacing) :
    EpsilonSquareLatticeDirectedBond spacing where
  source := (plaquette.lowerLeft.1, plaquette.lowerLeft.2 + 1)
  target := plaquette.lowerLeft
  nearestNeighbor := Or.inr ⟨Or.inr (by omega), rfl⟩

@[simp] theorem bottom_target_eq_right_source
    (plaquette : EpsilonSquareLatticePlaquette spacing) :
    plaquette.bottomBond.target = plaquette.rightBond.source :=
  rfl

@[simp] theorem right_target_eq_top_source
    (plaquette : EpsilonSquareLatticePlaquette spacing) :
    plaquette.rightBond.target = plaquette.topBond.source :=
  rfl

@[simp] theorem top_target_eq_left_source
    (plaquette : EpsilonSquareLatticePlaquette spacing) :
    plaquette.topBond.target = plaquette.leftBond.source :=
  rfl

@[simp] theorem left_target_eq_bottom_source
    (plaquette : EpsilonSquareLatticePlaquette spacing) :
    plaquette.leftBond.target = plaquette.bottomBond.source :=
  rfl

/-- Exact counterclockwise boundary word, traversed bottom, right, top, then left. -/
def boundaryWord (plaquette : EpsilonSquareLatticePlaquette spacing) :
    List (YangMills.Mathematics.OrientedEdge
      (EpsilonSquareLatticeDirectedBond spacing)) :=
  [.forward plaquette.bottomBond, .forward plaquette.rightBond,
    .forward plaquette.topBond, .forward plaquette.leftBond]

end EpsilonSquareLatticePlaquette

/-- Counterclockwise elementary plaquette holonomy. Traversing bottom, right, top, then left gives
`left * top * right * bottom` under Driver's fixed path-order convention. -/
def epsilonSquareLatticePlaquetteHolonomy
    {G : Type*} [Group G] {spacing : PositiveLatticeSpacing}
    (plaquette : EpsilonSquareLatticePlaquette spacing)
    (configuration : EpsilonSquareLatticeConfiguration G spacing) : G :=
  configuration plaquette.leftBond *
    (configuration plaquette.topBond *
      (configuration plaquette.rightBond * configuration plaquette.bottomBond))

/-- Exact bridge to the reusable finite-word convention. This declaration locks the
source-critical bottom/right/top/left traversal and later-on-the-left multiplication order. -/
theorem epsilonSquareLatticePlaquetteHolonomy_eq_finiteOrientedWordHolonomy
    {G : Type*} [Group G] {spacing : PositiveLatticeSpacing}
    (plaquette : EpsilonSquareLatticePlaquette spacing)
    (configuration : EpsilonSquareLatticeConfiguration G spacing) :
    epsilonSquareLatticePlaquetteHolonomy plaquette configuration =
      YangMills.Mathematics.finiteOrientedWordHolonomy configuration.value
        plaquette.boundaryWord := by
  simp [epsilonSquareLatticePlaquetteHolonomy,
    EpsilonSquareLatticePlaquette.boundaryWord, mul_assoc]

/-- The same plaquette holonomy restricted to the exact axial carrier. -/
def epsilonSquareLatticeAxialPlaquetteHolonomy
    {G : Type*} [Group G] {spacing : PositiveLatticeSpacing}
    (plaquette : EpsilonSquareLatticePlaquette spacing)
    (configuration : EpsilonSquareLatticeAxialConfiguration G spacing) : G :=
  epsilonSquareLatticePlaquetteHolonomy plaquette configuration.configuration

/-- Finite product of one exact Definition 7.1 action over elementary plaquette holonomies. -/
def epsilonSquareLatticeFinitePlaquetteActionWeight
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    {spacing : PositiveLatticeSpacing}
    (action : TwoDimensionalLatticeActionData G)
    (plaquettes : Finset (EpsilonSquareLatticePlaquette spacing))
    (configuration : EpsilonSquareLatticeAxialConfiguration G spacing) : ENNReal :=
  ∏ plaquette ∈ plaquettes,
    ENNReal.ofReal
      (action.action (epsilonSquareLatticeAxialPlaquetteHolonomy plaquette configuration))

namespace epsilonSquareLatticePlaquetteHolonomy

variable
    {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul₂ G]
    {spacing : PositiveLatticeSpacing}

/-- Elementary plaquette holonomy is measurable on the induced infinite configuration carrier. -/
theorem measurable (plaquette : EpsilonSquareLatticePlaquette spacing) :
    Measurable (epsilonSquareLatticePlaquetteHolonomy (G := G) plaquette) :=
  (EpsilonSquareLatticeConfiguration.measurable_apply plaquette.leftBond).mul
    ((EpsilonSquareLatticeConfiguration.measurable_apply plaquette.topBond).mul
      ((EpsilonSquareLatticeConfiguration.measurable_apply plaquette.rightBond).mul
        (EpsilonSquareLatticeConfiguration.measurable_apply plaquette.bottomBond)))

end epsilonSquareLatticePlaquetteHolonomy

namespace epsilonSquareLatticeAxialPlaquetteHolonomy

variable
    {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul₂ G]
    {spacing : PositiveLatticeSpacing}

/-- Elementary plaquette holonomy is measurable on the exact axial carrier. -/
theorem measurable (plaquette : EpsilonSquareLatticePlaquette spacing) :
    Measurable (epsilonSquareLatticeAxialPlaquetteHolonomy (G := G) plaquette) :=
  (EpsilonSquareLatticeAxialConfiguration.measurable_apply plaquette.leftBond).mul
    ((EpsilonSquareLatticeAxialConfiguration.measurable_apply plaquette.topBond).mul
      ((EpsilonSquareLatticeAxialConfiguration.measurable_apply plaquette.rightBond).mul
        (EpsilonSquareLatticeAxialConfiguration.measurable_apply plaquette.bottomBond)))

end epsilonSquareLatticeAxialPlaquetteHolonomy

namespace epsilonSquareLatticeFinitePlaquetteActionWeight

variable
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [MeasurableSpace G] [BorelSpace G] [MeasurableMul₂ G]
    {spacing : PositiveLatticeSpacing}

/-- Every finite plaquette action weight is measurable. -/
theorem measurable
    (action : TwoDimensionalLatticeActionData G)
    (plaquettes : Finset (EpsilonSquareLatticePlaquette spacing)) :
    Measurable (epsilonSquareLatticeFinitePlaquetteActionWeight action plaquettes) := by
  apply Finset.measurable_prod
  intro plaquette _
  exact ENNReal.measurable_ofReal.comp
    (action.action_continuous.measurable.comp
      (epsilonSquareLatticeAxialPlaquetteHolonomy.measurable plaquette))

omit [MeasurableMul₂ G] in
/-- Strict action positivity makes every finite plaquette weight nonzero. -/
theorem ne_zero
    (action : TwoDimensionalLatticeActionData G)
    (plaquettes : Finset (EpsilonSquareLatticePlaquette spacing))
    (configuration : EpsilonSquareLatticeAxialConfiguration G spacing) :
    epsilonSquareLatticeFinitePlaquetteActionWeight action plaquettes configuration ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro plaquette membership
  exact ne_of_gt (ENNReal.ofReal_pos.mpr (action.action_pos _))

end epsilonSquareLatticeFinitePlaquetteActionWeight

end

end YangMills.Dimensions
