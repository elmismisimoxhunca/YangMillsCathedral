/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Dimensions.TwoDimensionalSquareLatticeFiniteVolumeBoundary

/-!
# Probes for Driver's finite-volume boundary geometry
-/

namespace YangMills.Dimensions.TwoDimensionalSquareLatticeFiniteVolumeBoundary.Probes

noncomputable section

/-- Radius one, used to expose the distinction between `B₁` and `B̄₁`. -/
def radiusOne : PositiveSquareLatticeBoxRadius := ⟨1, by decide⟩

/-- The origin belongs to `A₀` at radius one. -/
theorem origin_inner : squareLatticeInnerClosedBoxPoint radiusOne (0, 0) := by
  simp [radiusOne, squareLatticeInnerClosedBoxPoint]

/-- A bond leaving the origin is a finite variable bond and hence lies in the outer box. -/
theorem origin_right_finite_and_outer (spacing : PositiveLatticeSpacing) :
    epsilonSquareLatticeFiniteVolumeBond spacing radiusOne
        (epsilonSquareLatticeRightBond spacing (0, 0)) ∧
      epsilonSquareLatticeOuterFiniteVolumeBond spacing radiusOne
        (epsilonSquareLatticeRightBond spacing (0, 0)) := by
  have finite : epsilonSquareLatticeFiniteVolumeBond spacing radiusOne
      (epsilonSquareLatticeRightBond spacing (0, 0)) := by
    exact Or.inl origin_inner
  exact ⟨finite, epsilonSquareLatticeFiniteVolumeBond.outer spacing radiusOne _ finite⟩

/-- A top-edge bond lies in `B̄₁` but not in `B₁`, so the two source-defined sets cannot collapse. -/
theorem outer_not_finite_witness (spacing : PositiveLatticeSpacing) :
    epsilonSquareLatticeOuterFiniteVolumeBond spacing radiusOne
        (epsilonSquareLatticeRightBond spacing (-1, 1)) ∧
      ¬ epsilonSquareLatticeFiniteVolumeBond spacing radiusOne
        (epsilonSquareLatticeRightBond spacing (-1, 1)) := by
  constructor
  · norm_num [epsilonSquareLatticeOuterFiniteVolumeBond,
      squareLatticeClosedBoxPoint, epsilonSquareLatticeRightBond, radiusOne]
    exact radiusOne.2
  · norm_num [epsilonSquareLatticeFiniteVolumeBond,
      squareLatticeInnerClosedBoxPoint, epsilonSquareLatticeRightBond, radiusOne]

/-- A bond beyond `B₁` is genuinely a frozen boundary-condition bond. -/
theorem external_boundary_witness (spacing : PositiveLatticeSpacing) :
    epsilonSquareLatticeBoundaryConditionBond spacing radiusOne
      (epsilonSquareLatticeRightBond spacing (1, 0)) := by
  simp [epsilonSquareLatticeBoundaryConditionBond,
    epsilonSquareLatticeFiniteVolumeBond, squareLatticeInnerClosedBoxPoint,
    epsilonSquareLatticeRightBond, radiusOne]

/-- A proposed bond that is both finite and frozen is hostilely rejected. -/
theorem finite_boundary_overlap_blocked
    (spacing : PositiveLatticeSpacing) (radius : PositiveSquareLatticeBoxRadius)
    (bond : EpsilonSquareLatticeDirectedBond spacing)
    (finiteVolume : epsilonSquareLatticeFiniteVolumeBond spacing radius bond)
    (boundary : epsilonSquareLatticeBoundaryConditionBond spacing radius bond) : False :=
  epsilonSquareLatticeBoundaryConditionBond.disjoint spacing radius bond finiteVolume boundary

/-- The finite-volume boundary geometry remains strictly two-dimensional. -/
theorem finite_boundary_not_four_dimensional :
    EuclideanDimension.two ≠ EuclideanDimension.four :=
  EuclideanDimension.two_ne_four

end

end YangMills.Dimensions.TwoDimensionalSquareLatticeFiniteVolumeBoundary.Probes
