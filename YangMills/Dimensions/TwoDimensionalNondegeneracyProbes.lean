/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Dimensions.OneDimensionalBoundary
import YangMills.Dimensions.TwoDimensionalNondegeneracy

/-!
# Hostile probes for two-dimensional nondegeneracy

The probes expose the explicit area, spatial, spacelike-support, and finite-plaquette witnesses. They
reject zero curvature slots, malformed holonomy, identity substitution for a nonidentity selected
link, and any confusion between the two-dimensional consistency index and Clay's dimension four.
-/

namespace YangMills.Dimensions.TwoDimensionalNondegeneracy.Probes

open YangMills.Lattice
open YangMills.Minkowski

noncomputable section

/-- The standard ordered area coefficient is exactly one. -/
theorem exact_standard_area :
    twoDimensionalAreaForm (fun i =>
      if i = 0 then twoDimensionalTimeBasisVector else twoDimensionalSpatialBasisVector) = 1 :=
  twoDimensionalAreaForm_standardBasis

/-- Replacing the genuine two-dimensional area form by zero is contradictory. -/
theorem zero_area_form_blocked (claimed : twoDimensionalAreaForm = 0) : False :=
  twoDimensionalAreaForm_ne_zero claimed

/-- Dimension two, unlike dimension one, has an explicit normalized spatial direction. -/
theorem exact_spatial_direction :
    ∃ direction : EuclideanUnitSpatialDirection EuclideanDimension.two,
      direction.vector ≠ 0 :=
  ⟨twoDimensionalKinematicNondegeneracyData.spatialDirection,
    twoDimensionalKinematicNondegeneracyData.spatialDirection.vector_ne_zero⟩

/-- Dimension-two locality tests have a genuinely nonzero spacelike-separated domain. -/
theorem exact_nonzero_spacelike_tests :
    ∃ f g : ScalarMinkowskiSchwartzTestFunction EuclideanDimension.two,
      f ≠ 0 ∧ g ≠ 0 ∧ HaveSpacelikeSeparatedTopologicalSupports f g :=
  twoDimensionalKinematicNondegeneracyData.nonzeroSpacelikeTests

/-- The two coordinate directions supply the unique ordered elementary plane used by the witness. -/
theorem exact_ordered_plane :
    twoDimensionalTimeIndex < twoDimensionalSpatialIndex :=
  twoDimensional_time_lt_spatial

/-- The concrete one-link field realizes every prescribed group element as selected holonomy. -/
theorem exact_selected_plaquette_holonomy
    {G : Type*} [Group G] (u : G) :
    plaquetteHolonomy (twoDimensionalSingleLinkGaugeField u)
      twoDimensionalPlaquetteOrigin twoDimensionalTimeIndex twoDimensionalSpatialIndex = u :=
  twoDimensionalSingleLinkGaugeField_plaquetteHolonomy u

/-- A malformed selected holonomy is rejected. -/
theorem malformed_selected_holonomy_blocked
    {G : Type*} [Group G] (u wrong : G) (different : wrong ≠ u)
    (claimed : plaquetteHolonomy (twoDimensionalSingleLinkGaugeField u)
      twoDimensionalPlaquetteOrigin twoDimensionalTimeIndex twoDimensionalSpatialIndex = wrong) :
    False := by
  apply different
  rw [← claimed]
  exact twoDimensionalSingleLinkGaugeField_plaquetteHolonomy u

/-- If the selected element is nonidentity, the concrete gauge field cannot be the identity field. -/
theorem nonidentity_single_link_field_blocked
    {G : Type*} [Group G] (u : G) (nonidentity : u ≠ 1)
    (claimed : twoDimensionalSingleLinkGaugeField u =
      (fun _ : PositiveOrientedLink EuclideanDimension.two
        twoDimensionalPlaquetteLattice => 1)) : False := by
  apply nonidentity
  have at_selected := congrFun claimed
    (⟨twoDimensionalPlaquetteOrigin, twoDimensionalTimeIndex⟩ :
      PositiveOrientedLink EuclideanDimension.two twoDimensionalPlaquetteLattice)
  simpa [twoDimensionalSingleLinkGaugeField] using at_selected

/-- Every admissible potential is tested at a concrete plaquette with strictly positive density. -/
theorem exact_positive_plaquette_density
    {G : Type*} [Group G] (potential : PlaquettePotentialData G) :
    let data := twoDimensionalPositivePlaquetteData potential
    0 < potential.potential
      (plaquetteHolonomy data.gaugeField twoDimensionalPlaquetteOrigin
        twoDimensionalTimeIndex twoDimensionalSpatialIndex) := by
  let data := twoDimensionalPositivePlaquetteData potential
  dsimp only
  rw [data.exactHolonomy]
  exact data.potentialPositive

/-- The lower-dimensional consistency index cannot be substituted for the Clay endpoint. -/
theorem two_dimension_cannot_be_four :
    EuclideanDimension.two ≠ EuclideanDimension.four :=
  EuclideanDimension.two_ne_four

/-- A claim that every dimension-two continuous alternating two-form vanishes is refuted by the
explicit area form; the dimension-one vanishing theorem therefore cannot be reused here. -/
theorem dimension_one_curvature_degeneracy_cannot_extend_to_two
    (claimed : ∀ ω :
      EuclideanDimension.two.Spacetime [⋀^Fin 2]→L[ℝ] ℝ, ω = 0) : False :=
  twoDimensionalAreaForm_ne_zero (claimed twoDimensionalAreaForm)

end

end YangMills.Dimensions.TwoDimensionalNondegeneracy.Probes
