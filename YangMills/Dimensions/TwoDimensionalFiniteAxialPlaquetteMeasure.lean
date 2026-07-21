/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Dimensions.TwoDimensionalSquareLatticePlaquetteAction
import YangMills.Mathematics.NormalizedCompactHaarFiniteProduct

/-!
# Finite axial plaquette presentations and normalized measures

This module packages a finite set of independent off-tree bond coordinates, its exact measurable
extension into the infinite axial carrier, and a finite family of actual elementary plaquettes.
The finite-volume action weight, its partition function, and normalized Haar-density measure are
then definitions. Finiteness and nonvanishing of that exact partition function are required before
normalization; no unrelated probability measure is supplied.

This is finite-presentation groundwork for Driver equations (7.2)/(7.4), not yet an exact square-box
sequence, boundary-condition limit, infinite-volume measure, or continuum convergence theorem.
-/

namespace YangMills.Dimensions

open MeasureTheory Set
open YangMills.Mathematics

noncomputable section

universe uG uCoordinate uPlaquette

/-- One finite axial plaquette presentation inside the exact infinite scaled lattice. -/
structure TwoDimensionalFiniteAxialPlaquettePresentationData
    (G : Type uG) [Group G] [MeasurableSpace G]
    (spacing : PositiveLatticeSpacing) where
  Coordinate : Type uCoordinate
  coordinateFintype : Fintype Coordinate
  coordinateDecidableEq : DecidableEq Coordinate
  coordinateNonempty : Nonempty Coordinate
  Plaquette : Type uPlaquette
  plaquetteFintype : Fintype Plaquette
  plaquetteDecidableEq : DecidableEq Plaquette
  plaquetteNonempty : Nonempty Plaquette
  /-- Each independent coordinate is one exact off-tree directed bond. -/
  coordinateBond : Coordinate → EpsilonSquareLatticeDirectedBond spacing
  coordinateBond_injective : Function.Injective coordinateBond
  /-- Opposite orientations of one underlying bond are never treated as independent coordinates. -/
  coordinateBond_reverse_disjoint : ∀ first second,
    coordinateBond first ≠ (coordinateBond second).reverse
  coordinateBond_not_axial : ∀ coordinate,
    ¬ epsilonSquareLatticeIsAxialTreeBond (coordinateBond coordinate)
  /-- Exact extension of finite independent coordinates to a reverse-compatible axial configuration. -/
  extension : (Coordinate → G) → EpsilonSquareLatticeAxialConfiguration G spacing
  extension_measurable : Measurable extension
  extension_coordinate : ∀ configuration coordinate,
    extension configuration (coordinateBond coordinate) = configuration coordinate
  /-- Every unrepresented off-tree directed bond is set to the identity. Reverse representatives
  are explicitly admitted because their values are forced by inversion. -/
  extension_unrepresented : ∀ configuration bond,
    ¬ epsilonSquareLatticeIsAxialTreeBond bond →
    (∀ coordinate, bond ≠ coordinateBond coordinate ∧
      bond ≠ (coordinateBond coordinate).reverse) →
    extension configuration bond = 1
  /-- The finite region consists of actual elementary plaquettes in the same scaled lattice. -/
  plaquette : Plaquette → EpsilonSquareLatticePlaquette spacing
  plaquette_injective : Function.Injective plaquette
  /-- Every non-tree boundary bond of every selected plaquette is one of the represented
  coordinates, in one of its two orientations. This blocks disconnected constant-action factors. -/
  plaquette_boundary_covered : ∀ label bond,
    bond ∈ (plaquette label).boundaryBonds →
      epsilonSquareLatticeIsAxialTreeBond bond ∨
        ∃ coordinate, bond = coordinateBond coordinate ∨
          bond = (coordinateBond coordinate).reverse

namespace TwoDimensionalFiniteAxialPlaquettePresentationData

variable
    {G : Type uG} [Group G] [MeasurableSpace G]
    {spacing : PositiveLatticeSpacing}

/-- The finite-coordinate extension is injective because every coordinate is recovered on its exact
represented bond. -/
theorem extension_injective
    (presentation : TwoDimensionalFiniteAxialPlaquettePresentationData G spacing) :
    Function.Injective presentation.extension := by
  intro first second equality
  funext coordinate
  have pointwise := congrArg
    (fun configuration : EpsilonSquareLatticeAxialConfiguration G spacing =>
      configuration (presentation.coordinateBond coordinate)) equality
  simpa [presentation.extension_coordinate] using pointwise

end TwoDimensionalFiniteAxialPlaquettePresentationData

variable
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [MeasurableSpace G] [BorelSpace G] [MeasurableMul₂ G]
    {spacing : PositiveLatticeSpacing}

/-- Exact finite product of one common action over the presented elementary plaquettes. -/
def twoDimensionalFiniteAxialPlaquetteWeight
    (action : TwoDimensionalLatticeActionData G)
    (presentation : TwoDimensionalFiniteAxialPlaquettePresentationData G spacing)
    (configuration : presentation.Coordinate → G) : ENNReal := by
  letI := presentation.plaquetteFintype
  letI := presentation.plaquetteDecidableEq
  exact ∏ label : presentation.Plaquette,
    ENNReal.ofReal (action.action
      (epsilonSquareLatticeAxialPlaquetteHolonomy
        (presentation.plaquette label) (presentation.extension configuration)))

/-- Exact partition function against canonical finite product Haar probability. -/
def twoDimensionalFiniteAxialNormalizer
    (action : TwoDimensionalLatticeActionData G)
    (presentation : TwoDimensionalFiniteAxialPlaquettePresentationData G spacing) : ENNReal := by
  letI := presentation.coordinateFintype
  exact ∫⁻ configuration,
    twoDimensionalFiniteAxialPlaquetteWeight action presentation configuration
      ∂normalizedCompactHaarFiniteProductMeasure presentation.Coordinate G

/-- Source-facing finiteness/nonvanishing certificate for the exact partition function. -/
structure TwoDimensionalFiniteAxialNormalizerData
    (action : TwoDimensionalLatticeActionData G)
    (presentation : TwoDimensionalFiniteAxialPlaquettePresentationData G spacing) : Prop where
  normalizer_ne_zero : twoDimensionalFiniteAxialNormalizer action presentation ≠ 0
  normalizer_ne_top : twoDimensionalFiniteAxialNormalizer action presentation ≠ ⊤

/-- Normalized finite axial Haar-density measure. -/
def twoDimensionalFiniteAxialMeasure
    (action : TwoDimensionalLatticeActionData G)
    (presentation : TwoDimensionalFiniteAxialPlaquettePresentationData G spacing) :
    Measure (presentation.Coordinate → G) := by
  letI := presentation.coordinateFintype
  exact (twoDimensionalFiniteAxialNormalizer action presentation)⁻¹ •
    (normalizedCompactHaarFiniteProductMeasure presentation.Coordinate G).withDensity
      (twoDimensionalFiniteAxialPlaquetteWeight action presentation)

namespace twoDimensionalFiniteAxialPlaquetteWeight

/-- The exact finite action weight is measurable on finite product coordinates. -/
theorem measurable
    (action : TwoDimensionalLatticeActionData G)
    (presentation : TwoDimensionalFiniteAxialPlaquettePresentationData G spacing) :
    Measurable (twoDimensionalFiniteAxialPlaquetteWeight action presentation) := by
  letI := presentation.coordinateFintype
  letI := presentation.plaquetteFintype
  letI := presentation.plaquetteDecidableEq
  apply Finset.measurable_prod
  intro label _
  exact ENNReal.measurable_ofReal.comp
    (action.action_continuous.measurable.comp
      ((epsilonSquareLatticeAxialPlaquetteHolonomy.measurable
        (presentation.plaquette label)).comp presentation.extension_measurable))

omit [MeasurableMul₂ G] in
/-- Strict positivity of the same action makes every presented finite weight nonzero. -/
theorem ne_zero
    (action : TwoDimensionalLatticeActionData G)
    (presentation : TwoDimensionalFiniteAxialPlaquettePresentationData G spacing)
    (configuration : presentation.Coordinate → G) :
    twoDimensionalFiniteAxialPlaquetteWeight action presentation configuration ≠ 0 := by
  letI := presentation.plaquetteFintype
  letI := presentation.plaquetteDecidableEq
  apply Finset.prod_ne_zero_iff.mpr
  intro label _
  exact ne_of_gt (ENNReal.ofReal_pos.mpr (action.action_pos _))

end twoDimensionalFiniteAxialPlaquetteWeight

namespace twoDimensionalFiniteAxialMeasure

omit [MeasurableMul₂ G] in
/-- Exact partition-function normalization derives total mass one. -/
theorem apply_univ
    (action : TwoDimensionalLatticeActionData G)
    (presentation : TwoDimensionalFiniteAxialPlaquettePresentationData G spacing)
    (normalizer : TwoDimensionalFiniteAxialNormalizerData action presentation) :
    twoDimensionalFiniteAxialMeasure action presentation univ = 1 := by
  letI := presentation.coordinateFintype
  rw [twoDimensionalFiniteAxialMeasure, Measure.smul_apply, withDensity_apply _ MeasurableSet.univ]
  rw [Measure.restrict_univ]
  simp only [smul_eq_mul]
  change (twoDimensionalFiniteAxialNormalizer action presentation)⁻¹ *
    twoDimensionalFiniteAxialNormalizer action presentation = 1
  exact ENNReal.inv_mul_cancel normalizer.normalizer_ne_zero normalizer.normalizer_ne_top

omit [MeasurableMul₂ G] in
/-- The normalized finite axial measure is nonzero. -/
theorem ne_zero
    (action : TwoDimensionalLatticeActionData G)
    (presentation : TwoDimensionalFiniteAxialPlaquettePresentationData G spacing)
    (normalizer : TwoDimensionalFiniteAxialNormalizerData action presentation) :
    twoDimensionalFiniteAxialMeasure action presentation ≠ 0 := by
  intro zeroMeasure
  have normalized := apply_univ action presentation normalizer
  rw [zeroMeasure] at normalized
  simp at normalized

end twoDimensionalFiniteAxialMeasure

end

end YangMills.Dimensions
