/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Dimensions.TwoDimensionalSquareLatticeFiniteVolumePlaquettes

/-!
# Probes for Driver's interacting finite-volume plaquettes
-/

namespace YangMills.Dimensions.TwoDimensionalSquareLatticeFiniteVolumePlaquettes.Probes

noncomputable section

/-- Membership in `J(Bₙ)` is exactly membership in the `2n × 2n` box plaquettes. -/
theorem exact_interacting_iff_box
    (spacing : PositiveLatticeSpacing) (radius : PositiveSquareLatticeBoxRadius)
    (plaquette : EpsilonSquareLatticePlaquette spacing) :
    epsilonSquareLatticeFiniteVolumeInteractingPlaquette spacing radius plaquette ↔
      plaquette ∈ epsilonSquareLatticeBoxPlaquettes spacing radius :=
  epsilonSquareLatticeFiniteVolumeInteractingPlaquette.iff_box spacing radius plaquette

/-- Every selected box plaquette actually contains a finite variable bond. -/
theorem selected_plaquette_nonvacuous
    (spacing : PositiveLatticeSpacing) (radius : PositiveSquareLatticeBoxRadius)
    (plaquette : EpsilonSquareLatticePlaquette spacing)
    (selected : plaquette ∈ epsilonSquareLatticeBoxPlaquettes spacing radius) :
    ∃ bond ∈ plaquette.boundaryBonds,
      epsilonSquareLatticeFiniteVolumeBond spacing radius bond :=
  (epsilonSquareLatticeFiniteVolumeInteractingPlaquette.iff_box
    spacing radius plaquette).mpr selected

/-- A disconnected selected plaquette is hostilely rejected. -/
theorem disconnected_selected_plaquette_blocked
    (spacing : PositiveLatticeSpacing) (radius : PositiveSquareLatticeBoxRadius)
    (plaquette : EpsilonSquareLatticePlaquette spacing)
    (selected : plaquette ∈ epsilonSquareLatticeBoxPlaquettes spacing radius)
    (disconnected : ∀ bond ∈ plaquette.boundaryBonds,
      ¬ epsilonSquareLatticeFiniteVolumeBond spacing radius bond) : False := by
  obtain ⟨bond, boundary, finiteVolume⟩ := selected_plaquette_nonvacuous
    spacing radius plaquette selected
  exact disconnected bond boundary finiteVolume

/-- An interacting plaquette omitted from the action box is hostilely rejected. -/
theorem omitted_interacting_plaquette_blocked
    (spacing : PositiveLatticeSpacing) (radius : PositiveSquareLatticeBoxRadius)
    (plaquette : EpsilonSquareLatticePlaquette spacing)
    (interacting : epsilonSquareLatticeFiniteVolumeInteractingPlaquette
      spacing radius plaquette)
    (omitted : plaquette ∉ epsilonSquareLatticeBoxPlaquettes spacing radius) : False :=
  omitted ((epsilonSquareLatticeFiniteVolumeInteractingPlaquette.iff_box
    spacing radius plaquette).mp interacting)

end

end YangMills.Dimensions.TwoDimensionalSquareLatticeFiniteVolumePlaquettes.Probes
