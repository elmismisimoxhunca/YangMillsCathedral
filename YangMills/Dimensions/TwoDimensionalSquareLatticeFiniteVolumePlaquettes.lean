/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Dimensions.TwoDimensionalSquareLatticeConditionedAxialExtension

/-!
# Driver's interacting plaquettes `J(Bₙ)`

The action product in Driver (7.1) and (7.2) ranges over elementary plaquettes incident to the finite
bond set `Bₙ`. This module defines that incidence literally and identifies it with the already
constructed `2n × 2n` square-box plaquette set.
-/

namespace YangMills.Dimensions

noncomputable section

/-- An elementary plaquette belongs to Driver's `J(Bₙ)` exactly when its boundary contains a bond
of `Bₙ`. -/
def epsilonSquareLatticeFiniteVolumeInteractingPlaquette
    (spacing : PositiveLatticeSpacing) (radius : PositiveSquareLatticeBoxRadius)
    (plaquette : EpsilonSquareLatticePlaquette spacing) : Prop :=
  ∃ bond ∈ plaquette.boundaryBonds,
    epsilonSquareLatticeFiniteVolumeBond spacing radius bond

namespace epsilonSquareLatticeFiniteVolumeInteractingPlaquette

/-- Driver's `J(Bₙ)` is exactly the elementary plaquette set of the closed side-`2n` box. -/
theorem iff_box
    (spacing : PositiveLatticeSpacing) (radius : PositiveSquareLatticeBoxRadius)
    (plaquette : EpsilonSquareLatticePlaquette spacing) :
    epsilonSquareLatticeFiniteVolumeInteractingPlaquette spacing radius plaquette ↔
      plaquette ∈ epsilonSquareLatticeBoxPlaquettes spacing radius := by
  rw [epsilonSquareLatticeBoxPlaquettes.mem_iff]
  unfold epsilonSquareLatticeFiniteVolumeInteractingPlaquette
  simp only [EpsilonSquareLatticePlaquette.boundaryBonds]
  unfold epsilonSquareLatticeFiniteVolumeBond squareLatticeInnerClosedBoxPoint
  simp [EpsilonSquareLatticePlaquette.bottomBond,
    EpsilonSquareLatticePlaquette.rightBond,
    EpsilonSquareLatticePlaquette.topBond,
    EpsilonSquareLatticePlaquette.leftBond]
  have positive : 1 ≤ radius.1 := radius.2
  omega

end epsilonSquareLatticeFiniteVolumeInteractingPlaquette

end

end YangMills.Dimensions
