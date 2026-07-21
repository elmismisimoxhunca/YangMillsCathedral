/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Dimensions.TwoDimensionalSquareLatticeBoxMeasure

/-!
# Consecutive exact-box projective consistency

Exact positive-radius boxes are nested geometrically. This module constructs the literal coordinate
and plaquette inclusions into the successor radius and records the remaining measure-level
projective consistency obligation: restricting the successor box law to the smaller coordinates must
give the smaller box law.

The consistency datum is uninhabited. It does not construct a compatible family, infinite-volume
measure, weak boundary limit, or lattice-continuum convergence.
-/

namespace YangMills.Dimensions

open MeasureTheory

noncomputable section

universe uG

/-- Increase a positive box radius by one. -/
def squareLatticeBoxSuccessorRadius
    (radius : PositiveSquareLatticeBoxRadius) : PositiveSquareLatticeBoxRadius :=
  ⟨radius.1 + 1, Nat.zero_lt_succ _⟩

@[simp]
theorem squareLatticeBoxSuccessorRadius_value
    (radius : PositiveSquareLatticeBoxRadius) :
    (squareLatticeBoxSuccessorRadius radius).1 = radius.1 + 1 :=
  rfl

/-- Literal inclusion of smaller-box independent coordinates into the successor box. -/
def epsilonSquareLatticeBoxCoordinateInclusion
    (spacing : PositiveLatticeSpacing) (radius : PositiveSquareLatticeBoxRadius) :
    EpsilonSquareLatticeBoxCoordinate spacing radius →
      EpsilonSquareLatticeBoxCoordinate spacing (squareLatticeBoxSuccessorRadius radius) :=
  fun coordinate =>
    ⟨coordinate.1,
      epsilonSquareLatticeBoxAxialCoordinates.mono spacing
        (show radius.1 ≤ (squareLatticeBoxSuccessorRadius radius).1 by
          rw [squareLatticeBoxSuccessorRadius_value]
          omega)
        coordinate.2⟩

/-- Literal inclusion of smaller-box plaquettes into the successor box. -/
def epsilonSquareLatticeBoxPlaquetteInclusion
    (spacing : PositiveLatticeSpacing) (radius : PositiveSquareLatticeBoxRadius) :
    EpsilonSquareLatticeBoxPlaquette spacing radius →
      EpsilonSquareLatticeBoxPlaquette spacing (squareLatticeBoxSuccessorRadius radius) :=
  fun plaquette =>
    ⟨plaquette.1,
      epsilonSquareLatticeBoxPlaquettes.mono spacing
        (show radius.1 ≤ (squareLatticeBoxSuccessorRadius radius).1 by
          rw [squareLatticeBoxSuccessorRadius_value]
          omega)
        plaquette.2⟩

namespace epsilonSquareLatticeBoxCoordinateInclusion

/-- Coordinate inclusion is injective. -/
theorem injective
    (spacing : PositiveLatticeSpacing) (radius : PositiveSquareLatticeBoxRadius) :
    Function.Injective (epsilonSquareLatticeBoxCoordinateInclusion spacing radius) := by
  intro first second equality
  apply Subtype.ext
  simpa [epsilonSquareLatticeBoxCoordinateInclusion] using
    congrArg Subtype.val equality

/-- Coordinate inclusion retains the identical infinite directed bond. -/
@[simp] theorem val
    (spacing : PositiveLatticeSpacing) (radius : PositiveSquareLatticeBoxRadius)
    (coordinate : EpsilonSquareLatticeBoxCoordinate spacing radius) :
    (epsilonSquareLatticeBoxCoordinateInclusion spacing radius coordinate).1 = coordinate.1 :=
  rfl

end epsilonSquareLatticeBoxCoordinateInclusion

namespace epsilonSquareLatticeBoxPlaquetteInclusion

/-- Plaquette inclusion is injective. -/
theorem injective
    (spacing : PositiveLatticeSpacing) (radius : PositiveSquareLatticeBoxRadius) :
    Function.Injective (epsilonSquareLatticeBoxPlaquetteInclusion spacing radius) := by
  intro first second equality
  apply Subtype.ext
  simpa [epsilonSquareLatticeBoxPlaquetteInclusion] using
    congrArg Subtype.val equality

/-- Plaquette inclusion retains the identical elementary plaquette. -/
@[simp] theorem val
    (spacing : PositiveLatticeSpacing) (radius : PositiveSquareLatticeBoxRadius)
    (plaquette : EpsilonSquareLatticeBoxPlaquette spacing radius) :
    (epsilonSquareLatticeBoxPlaquetteInclusion spacing radius plaquette).1 = plaquette.1 :=
  rfl

end epsilonSquareLatticeBoxPlaquetteInclusion

/-- Restr a successor-box coordinate configuration to the smaller exact box. -/
def epsilonSquareLatticeBoxCoordinateRestriction
    {G : Type uG}
    (spacing : PositiveLatticeSpacing) (radius : PositiveSquareLatticeBoxRadius) :
    (EpsilonSquareLatticeBoxCoordinate spacing (squareLatticeBoxSuccessorRadius radius) → G) →
      (EpsilonSquareLatticeBoxCoordinate spacing radius → G) :=
  fun configuration coordinate =>
    configuration (epsilonSquareLatticeBoxCoordinateInclusion spacing radius coordinate)

namespace epsilonSquareLatticeBoxCoordinateRestriction

/-- Coordinate restriction is measurable for every measurable target. -/
theorem measurable
    {G : Type uG} [MeasurableSpace G]
    (spacing : PositiveLatticeSpacing) (radius : PositiveSquareLatticeBoxRadius) :
    Measurable (epsilonSquareLatticeBoxCoordinateRestriction (G := G) spacing radius) := by
  apply measurable_pi_iff.mpr
  intro coordinate
  exact measurable_pi_apply (epsilonSquareLatticeBoxCoordinateInclusion spacing radius coordinate)

end epsilonSquareLatticeBoxCoordinateRestriction

/-- Exact consecutive-box projective consistency required by the finite-cylinder conclusion behind
Driver Theorem 7.2. -/
structure TwoDimensionalSquareLatticeBoxProjectiveConsistencyData
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    [MeasurableMul₂ G] [MeasurableInv G]
    (spacing : PositiveLatticeSpacing)
    (action : TwoDimensionalLatticeActionData G) : Prop where
  consecutive_pushforward : ∀ radius : PositiveSquareLatticeBoxRadius,
    Measure.map (epsilonSquareLatticeBoxCoordinateRestriction (G := G) spacing radius)
        (twoDimensionalSquareLatticeBoxMeasure spacing
          (squareLatticeBoxSuccessorRadius radius) action) =
      twoDimensionalSquareLatticeBoxMeasure spacing radius action

end

end YangMills.Dimensions
