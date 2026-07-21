/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Dimensions.TwoDimensionalLatticeApproximatingSequence

/-!
# Infinite directed `εℤ²` configurations and Driver's axial tree

Driver §7 uses the infinite directed nearest-neighbor graph, configurations satisfying reverse-bond
inversion, and the axial tree consisting of every vertical bond together with every horizontal bond
on the x-axis. This module defines those exact carriers. It supplies only combinatorial
configurations; no action, measure, finite/infinite-volume limit, or convergence is constructed.
-/

namespace YangMills.Dimensions

noncomputable section

/-- Physical embedding of an integer site into the exact scaled lattice `εℤ²`. -/
def epsilonSquareLatticePoint (spacing : PositiveLatticeSpacing) (site : ℤ × ℤ) :
    EuclideanDimension.two.Spacetime :=
  (EuclideanSpace.equiv EuclideanDimension.two.CoordinateIndex ℝ).symm
    (fun index => if index = ⟨0, by decide⟩
      then spacing.1 * (site.1 : ℝ) else spacing.1 * (site.2 : ℝ))

/-- Directed nearest-neighbor bonds of Driver's infinite `εℤ²` graph. -/
structure EpsilonSquareLatticeDirectedBond (spacing : PositiveLatticeSpacing) where
  source : ℤ × ℤ
  target : ℤ × ℤ
  nearestNeighbor : SquareLatticeNearestNeighbor source target
  deriving DecidableEq

namespace EpsilonSquareLatticeDirectedBond

variable {spacing : PositiveLatticeSpacing}

@[simp]
theorem point_firstCoordinate (site : ℤ × ℤ) :
    twoDimensionalFirstCoordinate (epsilonSquareLatticePoint spacing site) =
      spacing.1 * (site.1 : ℝ) := by
  simp [epsilonSquareLatticePoint, twoDimensionalFirstCoordinate]

@[simp]
theorem point_secondCoordinate (site : ℤ × ℤ) :
    twoDimensionalSecondCoordinate (epsilonSquareLatticePoint spacing site) =
      spacing.1 * (site.2 : ℝ) := by
  simp [epsilonSquareLatticePoint, twoDimensionalSecondCoordinate]

private theorem scaledNearestNeighbor
    (spacing : PositiveLatticeSpacing) (first second : ℤ × ℤ)
    (nearest : SquareLatticeNearestNeighbor first second) :
    (((spacing.1 * (second.1 : ℝ) = spacing.1 * (first.1 : ℝ) + spacing.1 ∨
        spacing.1 * (second.1 : ℝ) = spacing.1 * (first.1 : ℝ) - spacing.1) ∧
      spacing.1 * (second.2 : ℝ) = spacing.1 * (first.2 : ℝ)) ∨
    ((spacing.1 * (second.2 : ℝ) = spacing.1 * (first.2 : ℝ) + spacing.1 ∨
        spacing.1 * (second.2 : ℝ) = spacing.1 * (first.2 : ℝ) - spacing.1) ∧
      spacing.1 * (second.1 : ℝ) = spacing.1 * (first.1 : ℝ))) := by
  unfold SquareLatticeNearestNeighbor at nearest
  rcases nearest with horizontal | vertical
  · left
    constructor
    · rcases horizontal.1 with rightStep | leftStep
      · left
        rw [rightStep]
        push_cast
        ring
      · right
        rw [leftStep]
        push_cast
        ring
    · rw [horizontal.2]
  · right
    constructor
    · rcases vertical.1 with upStep | downStep
      · left
        rw [upStep]
        push_cast
        ring
      · right
        rw [downStep]
        push_cast
        ring
    · rw [vertical.2]

/-- The physically embedded endpoints differ by exactly one signed `ε` step in one coordinate. -/
theorem physical_nearestNeighbor (bond : EpsilonSquareLatticeDirectedBond spacing) :
    ((twoDimensionalFirstCoordinate (epsilonSquareLatticePoint spacing bond.target) =
          twoDimensionalFirstCoordinate (epsilonSquareLatticePoint spacing bond.source) + spacing.1 ∨
        twoDimensionalFirstCoordinate (epsilonSquareLatticePoint spacing bond.target) =
          twoDimensionalFirstCoordinate (epsilonSquareLatticePoint spacing bond.source) - spacing.1) ∧
      twoDimensionalSecondCoordinate (epsilonSquareLatticePoint spacing bond.target) =
        twoDimensionalSecondCoordinate (epsilonSquareLatticePoint spacing bond.source)) ∨
    ((twoDimensionalSecondCoordinate (epsilonSquareLatticePoint spacing bond.target) =
          twoDimensionalSecondCoordinate (epsilonSquareLatticePoint spacing bond.source) + spacing.1 ∨
        twoDimensionalSecondCoordinate (epsilonSquareLatticePoint spacing bond.target) =
          twoDimensionalSecondCoordinate (epsilonSquareLatticePoint spacing bond.source) - spacing.1) ∧
      twoDimensionalFirstCoordinate (epsilonSquareLatticePoint spacing bond.target) =
        twoDimensionalFirstCoordinate (epsilonSquareLatticePoint spacing bond.source)) := by
  simpa only [point_firstCoordinate, point_secondCoordinate] using
    scaledNearestNeighbor spacing bond.source bond.target bond.nearestNeighbor

@[ext]
theorem ext {first second : EpsilonSquareLatticeDirectedBond spacing}
    (source : first.source = second.source) (target : first.target = second.target) :
    first = second := by
  cases first
  cases second
  simp_all

/-- Nearest-neighbor incidence is symmetric. -/
theorem nearestNeighbor_symm {first second : ℤ × ℤ}
    (h : SquareLatticeNearestNeighbor first second) :
    SquareLatticeNearestNeighbor second first := by
  unfold SquareLatticeNearestNeighbor at h ⊢
  omega

/-- Reverse the directed orientation of the same lattice bond. -/
def reverse (bond : EpsilonSquareLatticeDirectedBond spacing) :
    EpsilonSquareLatticeDirectedBond spacing where
  source := bond.target
  target := bond.source
  nearestNeighbor := nearestNeighbor_symm bond.nearestNeighbor

@[simp]
theorem reverse_source (bond : EpsilonSquareLatticeDirectedBond spacing) :
    bond.reverse.source = bond.target :=
  rfl

@[simp]
theorem reverse_target (bond : EpsilonSquareLatticeDirectedBond spacing) :
    bond.reverse.target = bond.source :=
  rfl

@[simp]
theorem reverse_reverse (bond : EpsilonSquareLatticeDirectedBond spacing) :
    bond.reverse.reverse = bond := by
  cases bond
  rfl

/-- A nearest-neighbor bond never has equal endpoints. -/
theorem source_ne_target (bond : EpsilonSquareLatticeDirectedBond spacing) :
    bond.source ≠ bond.target := by
  intro equality
  have firstCoordinate := congrArg Prod.fst equality
  have secondCoordinate := congrArg Prod.snd equality
  have nearest := bond.nearestNeighbor
  unfold SquareLatticeNearestNeighbor at nearest
  omega

end EpsilonSquareLatticeDirectedBond

/-- Driver's axial tree: all vertical bonds and exactly the horizontal bonds on the x-axis. -/
def epsilonSquareLatticeIsAxialTreeBond
    {spacing : PositiveLatticeSpacing}
    (bond : EpsilonSquareLatticeDirectedBond spacing) : Prop :=
  bond.source.1 = bond.target.1 ∨
    (bond.source.2 = 0 ∧ bond.target.2 = 0)

namespace epsilonSquareLatticeIsAxialTreeBond

variable {spacing : PositiveLatticeSpacing}

/-- Axial-tree membership is orientation independent. -/
theorem reverse_iff (bond : EpsilonSquareLatticeDirectedBond spacing) :
    epsilonSquareLatticeIsAxialTreeBond bond.reverse ↔
      epsilonSquareLatticeIsAxialTreeBond bond := by
  simp only [epsilonSquareLatticeIsAxialTreeBond,
    EpsilonSquareLatticeDirectedBond.reverse_source,
    EpsilonSquareLatticeDirectedBond.reverse_target]
  constructor <;> intro h
  · rcases h with h | ⟨hs, ht⟩
    · exact Or.inl h.symm
    · exact Or.inr ⟨ht, hs⟩
  · rcases h with h | ⟨hs, ht⟩
    · exact Or.inl h.symm
    · exact Or.inr ⟨ht, hs⟩

end epsilonSquareLatticeIsAxialTreeBond

/-- Driver's infinite directed configuration carrier `Ω∞(ε)`, with reverse orientation interpreted
by group inversion rather than an independent coordinate. -/
structure EpsilonSquareLatticeConfiguration
    (G : Type*) [Group G] (spacing : PositiveLatticeSpacing) where
  value : EpsilonSquareLatticeDirectedBond spacing → G
  reverse_value : ∀ bond, value bond.reverse = (value bond)⁻¹

namespace EpsilonSquareLatticeConfiguration

variable {G : Type*} [Group G] {spacing : PositiveLatticeSpacing}

instance [MeasurableSpace G] : MeasurableSpace
    (EpsilonSquareLatticeConfiguration G spacing) :=
  MeasurableSpace.comap EpsilonSquareLatticeConfiguration.value inferInstance

instance : CoeFun (EpsilonSquareLatticeConfiguration G spacing)
    (fun _ => EpsilonSquareLatticeDirectedBond spacing → G) :=
  ⟨value⟩

/-- Every directed-bond coordinate is measurable on the induced configuration carrier. -/
theorem measurable_apply [MeasurableSpace G]
    (bond : EpsilonSquareLatticeDirectedBond spacing) :
    Measurable (fun configuration : EpsilonSquareLatticeConfiguration G spacing =>
      configuration bond) :=
  (measurable_pi_apply bond).comp
    (comap_measurable EpsilonSquareLatticeConfiguration.value)

/-- The identity configuration inhabits the exact reverse-compatible carrier. -/
def identity : EpsilonSquareLatticeConfiguration G spacing where
  value := fun _ => 1
  reverse_value := fun _ => by simp

@[simp]
theorem identity_apply (bond : EpsilonSquareLatticeDirectedBond spacing) :
    (identity : EpsilonSquareLatticeConfiguration G spacing) bond = 1 :=
  rfl

end EpsilonSquareLatticeConfiguration

/-- Driver's axial-gauge-fixed carrier: every coordinate on the exact axial tree is the identity. -/
structure EpsilonSquareLatticeAxialConfiguration
    (G : Type*) [Group G] (spacing : PositiveLatticeSpacing) where
  configuration : EpsilonSquareLatticeConfiguration G spacing
  axialTree_fixed : ∀ bond, epsilonSquareLatticeIsAxialTreeBond bond →
    configuration bond = 1

namespace EpsilonSquareLatticeAxialConfiguration

variable {G : Type*} [Group G] {spacing : PositiveLatticeSpacing}

instance [MeasurableSpace G] : MeasurableSpace
    (EpsilonSquareLatticeAxialConfiguration G spacing) :=
  MeasurableSpace.comap EpsilonSquareLatticeAxialConfiguration.configuration inferInstance

instance : CoeFun (EpsilonSquareLatticeAxialConfiguration G spacing)
    (fun _ => EpsilonSquareLatticeDirectedBond spacing → G) :=
  ⟨fun configuration => configuration.configuration⟩

/-- Every directed-bond coordinate is measurable on the induced axial carrier. -/
theorem measurable_apply [MeasurableSpace G]
    (bond : EpsilonSquareLatticeDirectedBond spacing) :
    Measurable (fun configuration : EpsilonSquareLatticeAxialConfiguration G spacing =>
      configuration bond) :=
  (EpsilonSquareLatticeConfiguration.measurable_apply bond).comp
    (comap_measurable EpsilonSquareLatticeAxialConfiguration.configuration)

/-- A concrete nonconstant axial configuration over the multiplicative integers: horizontal bonds
on row one record their signed horizontal displacement, while every other bond is the identity. -/
def rowOneInteger :
    EpsilonSquareLatticeAxialConfiguration (Multiplicative ℤ) spacing where
  configuration :=
    { value := fun bond =>
        if bond.source.2 = 1 ∧ bond.target.2 = 1
        then Multiplicative.ofAdd (bond.target.1 - bond.source.1)
        else 1
      reverse_value := by
        intro bond
        by_cases row : bond.source.2 = 1 ∧ bond.target.2 = 1
        · simp [row]
        · have reverseNotRow : ¬ (bond.target.2 = 1 ∧ bond.source.2 = 1) := by
            intro reverseRow
            exact row ⟨reverseRow.2, reverseRow.1⟩
          simp [row, reverseNotRow] }
  axialTree_fixed := by
    intro bond tree
    rcases tree with vertical | horizontalAxis
    · by_cases row : bond.source.2 = 1 ∧ bond.target.2 = 1
      · simp [row, vertical]
      · simp [row]
    · have notRow : ¬ (bond.source.2 = 1 ∧ bond.target.2 = 1) := by
        omega
      simp [notRow]

/-- The identity configuration also inhabits the exact axial-gauge-fixed carrier. -/
def identity : EpsilonSquareLatticeAxialConfiguration G spacing where
  configuration := EpsilonSquareLatticeConfiguration.identity
  axialTree_fixed := fun _ _ => rfl

@[simp]
theorem identity_apply (bond : EpsilonSquareLatticeDirectedBond spacing) :
    (identity : EpsilonSquareLatticeAxialConfiguration G spacing) bond = 1 :=
  rfl

end EpsilonSquareLatticeAxialConfiguration

end

end YangMills.Dimensions
