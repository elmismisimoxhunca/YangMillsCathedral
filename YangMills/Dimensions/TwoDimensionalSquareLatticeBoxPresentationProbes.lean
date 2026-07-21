/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Dimensions.TwoDimensionalSquareLatticeBoxPresentation

/-!
# Probes for exact square-box finite presentations
-/

namespace YangMills.Dimensions.TwoDimensionalSquareLatticeBoxPresentation.Probes

noncomputable section

universe uG

variable
    {G : Type uG} [Group G] [MeasurableSpace G] [MeasurableInv G]
    (spacing : PositiveLatticeSpacing) (radius : PositiveSquareLatticeBoxRadius)

/-- The adapter's coordinate carrier is literally the exact box-coordinate subtype. -/
theorem exact_coordinate_carrier :
    (twoDimensionalSquareLatticeBoxPresentation (G := G) spacing radius).Coordinate =
      EpsilonSquareLatticeBoxCoordinate spacing radius :=
  rfl

/-- The adapter's plaquette carrier is literally the exact box-plaquette subtype. -/
theorem exact_plaquette_carrier :
    (twoDimensionalSquareLatticeBoxPresentation (G := G) spacing radius).Plaquette =
      EpsilonSquareLatticeBoxPlaquette spacing radius :=
  rfl

omit [MeasurableSpace G] [MeasurableInv G] in
/-- Every finite coordinate is recovered on its exact infinite directed bond. -/
theorem exact_coordinate_recovery
    (configuration : EpsilonSquareLatticeBoxCoordinate spacing radius → G)
    (coordinate : EpsilonSquareLatticeBoxCoordinate spacing radius) :
    epsilonSquareLatticeBoxAxialExtension spacing radius configuration coordinate.1 =
      configuration coordinate :=
  epsilonSquareLatticeBoxAxialExtension.coordinate spacing radius configuration coordinate

/-- The extension remains measurable on the exact induced carriers. -/
theorem exact_extension_measurable :
    Measurable (epsilonSquareLatticeBoxAxialExtension (G := G) spacing radius) :=
  epsilonSquareLatticeBoxAxialExtension.measurable spacing radius

omit [MeasurableSpace G] [MeasurableInv G] in
/-- Every unrepresented off-tree bond is literally the identity. -/
theorem exact_unrepresented_identity
    (configuration : EpsilonSquareLatticeBoxCoordinate spacing radius → G)
    (bond : EpsilonSquareLatticeDirectedBond spacing)
    (notTree : ¬ epsilonSquareLatticeIsAxialTreeBond bond)
    (forward : bond ∉ epsilonSquareLatticeBoxAxialCoordinates spacing radius)
    (reverse : bond.reverse ∉ epsilonSquareLatticeBoxAxialCoordinates spacing radius) :
    epsilonSquareLatticeBoxAxialExtension spacing radius configuration bond = 1 :=
  epsilonSquareLatticeBoxAxialExtension.unrepresented
    spacing radius configuration bond notTree forward reverse

/-- Every adapted plaquette boundary is connected to a finite coordinate or the exact axial tree. -/
theorem exact_boundary_coverage
    (label : (twoDimensionalSquareLatticeBoxPresentation (G := G) spacing radius).Plaquette)
    (bond : EpsilonSquareLatticeDirectedBond spacing)
    (membership : bond ∈
      ((twoDimensionalSquareLatticeBoxPresentation (G := G) spacing radius).plaquette label).boundaryBonds) :
    epsilonSquareLatticeIsAxialTreeBond bond ∨
      ∃ coordinate,
        bond = (twoDimensionalSquareLatticeBoxPresentation (G := G)
          spacing radius).coordinateBond coordinate ∨
        bond = ((twoDimensionalSquareLatticeBoxPresentation (G := G)
          spacing radius).coordinateBond coordinate).reverse :=
  (twoDimensionalSquareLatticeBoxPresentation (G := G) spacing radius).plaquette_boundary_covered
    label bond membership

/-- A concrete finite coordinate can carry a nonidentity value through the exact extension. -/
theorem nonidentity_coordinate_survives
    (coordinate : EpsilonSquareLatticeBoxCoordinate spacing radius) :
    epsilonSquareLatticeBoxAxialExtension spacing radius
        (fun _ => Multiplicative.ofAdd (1 : ℤ)) coordinate.1 ≠ 1 := by
  rw [epsilonSquareLatticeBoxAxialExtension.coordinate]
  norm_num

/-- The concrete box presentation exists at every positive radius. -/
theorem presentation_nonempty
    (radius : PositiveSquareLatticeBoxRadius) :
    Nonempty (TwoDimensionalFiniteAxialPlaquettePresentationData.{uG, 0, 0} G spacing) :=
  ⟨twoDimensionalSquareLatticeBoxPresentation (G := G) spacing radius⟩

/-- A disconnected non-tree boundary contradicts the adapted presentation. -/
theorem disconnected_boundary_blocked
    (label : (twoDimensionalSquareLatticeBoxPresentation (G := G) spacing radius).Plaquette)
    (bond : EpsilonSquareLatticeDirectedBond spacing)
    (membership : bond ∈
      ((twoDimensionalSquareLatticeBoxPresentation (G := G) spacing radius).plaquette label).boundaryBonds)
    (notTree : ¬ epsilonSquareLatticeIsAxialTreeBond bond)
    (absent : ∀ coordinate,
      bond ≠ (twoDimensionalSquareLatticeBoxPresentation (G := G)
        spacing radius).coordinateBond coordinate ∧
      bond ≠ ((twoDimensionalSquareLatticeBoxPresentation (G := G)
        spacing radius).coordinateBond coordinate).reverse) : False := by
  rcases exact_boundary_coverage spacing radius label bond membership with tree | represented
  · exact notTree tree
  · obtain ⟨coordinate, forward | reverse⟩ := represented
    · exact (absent coordinate).1 forward
    · exact (absent coordinate).2 reverse

end

end YangMills.Dimensions.TwoDimensionalSquareLatticeBoxPresentation.Probes
