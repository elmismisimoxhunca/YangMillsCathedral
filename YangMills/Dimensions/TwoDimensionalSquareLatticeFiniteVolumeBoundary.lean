/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Dimensions.TwoDimensionalSquareLatticeBoxProjectiveConsistency

/-!
# Driver's finite-volume bond and boundary geometry

Driver §7 distinguishes the bonds `Bₙ` having at least one endpoint in the closed square `Aₙ₋₁`
from the larger bond set `B̄ₙ` whose two endpoints lie in `Aₙ`. Boundary conditions in (7.1) and
(7.2) freeze `Bₙᶜ`; they are not the free finite box laws (7.3) and (7.4).

This module records that exact distinction on the scaled square lattice and proves that every bond of
`Bₙ` has both endpoints in `Aₙ`. It constructs no delta-conditioned measure or weak limit.
-/

namespace YangMills.Dimensions

noncomputable section

/-- Integer sites of Driver's closed square `Aₙ`. -/
def squareLatticeClosedBoxPoint
    (radius : PositiveSquareLatticeBoxRadius) (site : ℤ × ℤ) : Prop :=
  -(radius.1 : ℤ) ≤ site.1 ∧ site.1 ≤ (radius.1 : ℤ) ∧
    -(radius.1 : ℤ) ≤ site.2 ∧ site.2 ≤ (radius.1 : ℤ)

/-- Integer sites of Driver's closed square `Aₙ₋₁`. -/
def squareLatticeInnerClosedBoxPoint
    (radius : PositiveSquareLatticeBoxRadius) (site : ℤ × ℤ) : Prop :=
  -((radius.1 - 1 : ℕ) : ℤ) ≤ site.1 ∧ site.1 ≤ ((radius.1 - 1 : ℕ) : ℤ) ∧
    -((radius.1 - 1 : ℕ) : ℤ) ≤ site.2 ∧ site.2 ≤ ((radius.1 - 1 : ℕ) : ℤ)

/-- Driver's `Bₙ`: directed bonds with initial or final site in `Aₙ₋₁`. -/
def epsilonSquareLatticeFiniteVolumeBond
    (spacing : PositiveLatticeSpacing) (radius : PositiveSquareLatticeBoxRadius)
    (bond : EpsilonSquareLatticeDirectedBond spacing) : Prop :=
  squareLatticeInnerClosedBoxPoint radius bond.source ∨
    squareLatticeInnerClosedBoxPoint radius bond.target

/-- Driver's `B̄ₙ`: directed bonds whose initial and final sites both lie in `Aₙ`. -/
def epsilonSquareLatticeOuterFiniteVolumeBond
    (spacing : PositiveLatticeSpacing) (radius : PositiveSquareLatticeBoxRadius)
    (bond : EpsilonSquareLatticeDirectedBond spacing) : Prop :=
  squareLatticeClosedBoxPoint radius bond.source ∧
    squareLatticeClosedBoxPoint radius bond.target

/-- Driver's boundary condition freezes precisely the complement `Bₙᶜ`. -/
def epsilonSquareLatticeBoundaryConditionBond
    (spacing : PositiveLatticeSpacing) (radius : PositiveSquareLatticeBoxRadius)
    (bond : EpsilonSquareLatticeDirectedBond spacing) : Prop :=
  ¬ epsilonSquareLatticeFiniteVolumeBond spacing radius bond

namespace squareLatticeInnerClosedBoxPoint

/-- `Aₙ₋₁` is contained in `Aₙ` for every positive radius. -/
theorem closedBox
    (radius : PositiveSquareLatticeBoxRadius) (site : ℤ × ℤ)
    (inner : squareLatticeInnerClosedBoxPoint radius site) :
    squareLatticeClosedBoxPoint radius site := by
  unfold squareLatticeInnerClosedBoxPoint at inner
  unfold squareLatticeClosedBoxPoint
  have positive : 1 ≤ radius.1 := radius.2
  omega

end squareLatticeInnerClosedBoxPoint

namespace epsilonSquareLatticeFiniteVolumeBond

/-- Every nearest neighbor of a site in `Aₙ₋₁` lies in `Aₙ`. -/
private theorem neighbor_closedBox
    (radius : PositiveSquareLatticeBoxRadius) (first second : ℤ × ℤ)
    (nearest : SquareLatticeNearestNeighbor first second)
    (inner : squareLatticeInnerClosedBoxPoint radius first) :
    squareLatticeClosedBoxPoint radius second := by
  unfold SquareLatticeNearestNeighbor at nearest
  unfold squareLatticeInnerClosedBoxPoint at inner
  unfold squareLatticeClosedBoxPoint
  have positive : 1 ≤ radius.1 := radius.2
  rcases nearest with horizontal | vertical
  · rcases horizontal.1 with right | left <;> omega
  · rcases vertical.1 with up | down <;> omega

/-- Driver's finite variable bonds `Bₙ` are literally contained in `B̄ₙ`. -/
theorem outer
    (spacing : PositiveLatticeSpacing) (radius : PositiveSquareLatticeBoxRadius)
    (bond : EpsilonSquareLatticeDirectedBond spacing)
    (finiteVolume : epsilonSquareLatticeFiniteVolumeBond spacing radius bond) :
    epsilonSquareLatticeOuterFiniteVolumeBond spacing radius bond := by
  unfold epsilonSquareLatticeFiniteVolumeBond at finiteVolume
  unfold epsilonSquareLatticeOuterFiniteVolumeBond
  rcases finiteVolume with sourceInner | targetInner
  · exact ⟨squareLatticeInnerClosedBoxPoint.closedBox radius bond.source sourceInner,
      neighbor_closedBox radius bond.source bond.target bond.nearestNeighbor sourceInner⟩
  · exact ⟨neighbor_closedBox radius bond.target bond.source
        (EpsilonSquareLatticeDirectedBond.nearestNeighbor_symm bond.nearestNeighbor) targetInner,
      squareLatticeInnerClosedBoxPoint.closedBox radius bond.target targetInner⟩

end epsilonSquareLatticeFiniteVolumeBond

namespace epsilonSquareLatticeBoundaryConditionBond

/-- No finite variable bond is simultaneously frozen by the boundary condition. -/
theorem disjoint
    (spacing : PositiveLatticeSpacing) (radius : PositiveSquareLatticeBoxRadius)
    (bond : EpsilonSquareLatticeDirectedBond spacing)
    (finiteVolume : epsilonSquareLatticeFiniteVolumeBond spacing radius bond)
    (boundary : epsilonSquareLatticeBoundaryConditionBond spacing radius bond) : False :=
  boundary finiteVolume

end epsilonSquareLatticeBoundaryConditionBond

end

end YangMills.Dimensions
