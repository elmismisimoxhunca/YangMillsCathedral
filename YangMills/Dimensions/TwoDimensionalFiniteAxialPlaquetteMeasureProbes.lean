/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Dimensions.TwoDimensionalFiniteAxialPlaquetteMeasure

/-!
# Probes for finite axial plaquette measures
-/

namespace YangMills.Dimensions.TwoDimensionalFiniteAxialPlaquetteMeasure.Probes

open MeasureTheory Set
open YangMills.Mathematics

noncomputable section

variable {spacing : PositiveLatticeSpacing}

/-- One off-tree coordinate for an inhabited finite presentation. -/
def unitCoordinateBond : EpsilonSquareLatticeDirectedBond spacing where
  source := (0, 1)
  target := (1, 1)
  nearestNeighbor := Or.inl ⟨Or.inl (by norm_num), rfl⟩

/-- A concrete one-coordinate/one-plaquette finite presentation over the unit group. It proves the
presentation API is inhabited without constructing a nontrivial Yang--Mills lattice field. -/
def unitPresentation :
    TwoDimensionalFiniteAxialPlaquettePresentationData Unit spacing where
  Coordinate := Unit
  coordinateFintype := inferInstance
  coordinateDecidableEq := inferInstance
  coordinateNonempty := inferInstance
  Plaquette := Unit
  plaquetteFintype := inferInstance
  plaquetteDecidableEq := inferInstance
  plaquetteNonempty := inferInstance
  coordinateBond := fun _ => unitCoordinateBond
  coordinateBond_injective := fun _ _ _ => Subsingleton.elim _ _
  coordinateBond_reverse_disjoint := fun _ _ equality => by
    have sourceEquality := congrArg EpsilonSquareLatticeDirectedBond.source equality
    norm_num [unitCoordinateBond] at sourceEquality
  coordinateBond_not_axial := fun _ => by
    simp [unitCoordinateBond, epsilonSquareLatticeIsAxialTreeBond]
  extension := fun _ => EpsilonSquareLatticeAxialConfiguration.identity
  extension_measurable := measurable_const
  extension_coordinate := fun _ _ => rfl
  extension_unrepresented := fun _ _ _ _ => rfl
  plaquette := fun _ => ⟨(0, 0)⟩
  plaquette_injective := fun _ _ _ => Subsingleton.elim _ _
  plaquette_boundary_covered := by
    intro label bond membership
    simp [EpsilonSquareLatticePlaquette.boundaryBonds] at membership
    rcases membership with bottom | right | top | left
    · subst bond
      exact Or.inl (Or.inr ⟨rfl, rfl⟩)
    · subst bond
      exact Or.inl (Or.inl rfl)
    · subst bond
      exact Or.inr ⟨(), Or.inr (by
        ext <;> norm_num [unitCoordinateBond,
          EpsilonSquareLatticePlaquette.topBond,
          EpsilonSquareLatticeDirectedBond.reverse])⟩
    · subst bond
      exact Or.inl (Or.inl rfl)

/-- A represented bond and a reverse represented bond cannot become independent coordinates. -/
theorem exact_reverse_coordinate_disjoint
    {G : Type*} [Group G] [MeasurableSpace G]
    (presentation : TwoDimensionalFiniteAxialPlaquettePresentationData G spacing)
    (first second : presentation.Coordinate) :
    presentation.coordinateBond first ≠
      (presentation.coordinateBond second).reverse :=
  presentation.coordinateBond_reverse_disjoint first second

/-- Every selected plaquette boundary bond is either frozen by the exact axial tree or represented
by one finite coordinate in one of its two orientations. -/
theorem exact_plaquette_boundary_coverage
    {G : Type*} [Group G] [MeasurableSpace G]
    (presentation : TwoDimensionalFiniteAxialPlaquettePresentationData G spacing)
    (label : presentation.Plaquette)
    (bond : EpsilonSquareLatticeDirectedBond spacing)
    (membership : bond ∈ (presentation.plaquette label).boundaryBonds) :
    epsilonSquareLatticeIsAxialTreeBond bond ∨
      ∃ coordinate, bond = presentation.coordinateBond coordinate ∨
        bond = (presentation.coordinateBond coordinate).reverse :=
  presentation.plaquette_boundary_covered label bond membership

/-- A disconnected boundary bond contradicts the exact coverage field. -/
theorem disconnected_plaquette_blocked
    {G : Type*} [Group G] [MeasurableSpace G]
    (presentation : TwoDimensionalFiniteAxialPlaquettePresentationData G spacing)
    (label : presentation.Plaquette)
    (bond : EpsilonSquareLatticeDirectedBond spacing)
    (membership : bond ∈ (presentation.plaquette label).boundaryBonds)
    (notTree : ¬ epsilonSquareLatticeIsAxialTreeBond bond)
    (unrepresented : ∀ coordinate, bond ≠ presentation.coordinateBond coordinate ∧
      bond ≠ (presentation.coordinateBond coordinate).reverse) : False := by
  rcases presentation.plaquette_boundary_covered label bond membership with tree | represented
  · exact notTree tree
  · obtain ⟨coordinate, forward | reverse⟩ := represented
    · exact (unrepresented coordinate).1 forward
    · exact (unrepresented coordinate).2 reverse

/-- Finite-coordinate extensions cannot identify two coordinate configurations. -/
theorem exact_extension_injective
    {G : Type*} [Group G] [MeasurableSpace G]
    (presentation : TwoDimensionalFiniteAxialPlaquettePresentationData G spacing) :
    Function.Injective presentation.extension :=
  presentation.extension_injective

/-- The finite weight is exactly the product over every presented actual plaquette. -/
theorem exact_weight_formula
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [MeasurableSpace G] [BorelSpace G] [MeasurableMul₂ G]
    (action : TwoDimensionalLatticeActionData G)
    (presentation : TwoDimensionalFiniteAxialPlaquettePresentationData G spacing)
    (configuration : presentation.Coordinate → G) :
    twoDimensionalFiniteAxialPlaquetteWeight action presentation configuration = by
      letI := presentation.plaquetteFintype
      exact ∏ label : presentation.Plaquette,
        ENNReal.ofReal (action.action
          (epsilonSquareLatticeAxialPlaquetteHolonomy
            (presentation.plaquette label) (presentation.extension configuration))) :=
  rfl

/-- Every exact finite weight is measurable and nonzero. -/
theorem exact_weight_contract
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [MeasurableSpace G] [BorelSpace G] [MeasurableMul₂ G]
    (action : TwoDimensionalLatticeActionData G)
    (presentation : TwoDimensionalFiniteAxialPlaquettePresentationData G spacing)
    (configuration : presentation.Coordinate → G) :
    Measurable (twoDimensionalFiniteAxialPlaquetteWeight action presentation) ∧
      twoDimensionalFiniteAxialPlaquetteWeight action presentation configuration ≠ 0 :=
  ⟨twoDimensionalFiniteAxialPlaquetteWeight.measurable action presentation,
    twoDimensionalFiniteAxialPlaquetteWeight.ne_zero action presentation configuration⟩

/-- The exact partition-function certificate derives a probability-normalized nonzero measure. -/
theorem exact_measure_contract
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [MeasurableSpace G] [BorelSpace G] [MeasurableMul₂ G]
    (action : TwoDimensionalLatticeActionData G)
    (presentation : TwoDimensionalFiniteAxialPlaquettePresentationData G spacing)
    (normalizer : TwoDimensionalFiniteAxialNormalizerData action presentation) :
    twoDimensionalFiniteAxialMeasure action presentation univ = 1 ∧
      twoDimensionalFiniteAxialMeasure action presentation ≠ 0 :=
  ⟨twoDimensionalFiniteAxialMeasure.apply_univ action presentation normalizer,
    twoDimensionalFiniteAxialMeasure.ne_zero action presentation normalizer⟩

/-- A zero finite axial measure is rejected by the exact partition-function normalization. -/
theorem zero_measure_blocked
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [MeasurableSpace G] [BorelSpace G] [MeasurableMul₂ G]
    (action : TwoDimensionalLatticeActionData G)
    (presentation : TwoDimensionalFiniteAxialPlaquettePresentationData G spacing)
    (normalizer : TwoDimensionalFiniteAxialNormalizerData action presentation)
    (claimed : twoDimensionalFiniteAxialMeasure action presentation = 0) : False :=
  (twoDimensionalFiniteAxialMeasure.ne_zero action presentation normalizer) claimed

/-- The exact partition function of the unit presentation with the constant action is one. -/
theorem unit_normalizer_eq_one :
    twoDimensionalFiniteAxialNormalizer
      (TwoDimensionalLatticeActionData.constantOne (G := Unit))
      (unitPresentation (spacing := spacing)) = 1 := by
  simp [twoDimensionalFiniteAxialNormalizer,
    twoDimensionalFiniteAxialPlaquetteWeight,
    TwoDimensionalLatticeActionData.constantOne,
    unitPresentation]
  exact normalizedCompactHaarFiniteProductMeasure_univ Unit Unit

/-- Hence the exact normalizer certificate, not only the presentation carrier, is inhabited. -/
def unitNormalizerData :
    TwoDimensionalFiniteAxialNormalizerData
      (TwoDimensionalLatticeActionData.constantOne (G := Unit))
      (unitPresentation (spacing := spacing)) where
  normalizer_ne_zero := by rw [unit_normalizer_eq_one]; exact one_ne_zero
  normalizer_ne_top := by rw [unit_normalizer_eq_one]; exact ENNReal.one_ne_top

/-- The finite presentation carrier itself is positively inhabited. -/
theorem presentation_nonempty :
    Nonempty (TwoDimensionalFiniteAxialPlaquettePresentationData.{0, 0, 0} Unit spacing) :=
  ⟨unitPresentation⟩

end

end YangMills.Dimensions.TwoDimensionalFiniteAxialPlaquetteMeasure.Probes
