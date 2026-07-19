/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Dimensions.FourDimensionalContractSeparation

/-!
# Hostile probes for Clay-dimension separation

These probes lock dimension-index rejection and the absence of real-linear coordinate-carrier
equivalences. They do not yet prove witness-level separation for the still-absent final acceptance
proposition or assert nonexistence of any lower-dimensional theory.
-/

namespace YangMills.Dimensions.FourDimensionalContractSeparation.Probes

open YangMills

/-- Four is accepted by the exact endpoint predicate. -/
example : IsFourDimensionalClayEndpoint EuclideanDimension.four :=
  rfl

/-- The lower-dimensional index union does not contain four. -/
theorem four_not_lower_dimension :
    ¬ (EuclideanDimension.four = EuclideanDimension.one ∨
      EuclideanDimension.four = EuclideanDimension.two ∨
      EuclideanDimension.four = EuclideanDimension.three) := by
  simp [EuclideanDimension.one, EuclideanDimension.two,
    EuclideanDimension.three, EuclideanDimension.four]

/-- One-dimensional consistency data cannot pass the Clay endpoint tag. -/
example : ¬ IsFourDimensionalClayEndpoint EuclideanDimension.one :=
  lowerDimension_not_clayEndpoint EuclideanDimension.one (Or.inl rfl)

/-- Two-dimensional consistency data cannot pass the Clay endpoint tag. -/
example : ¬ IsFourDimensionalClayEndpoint EuclideanDimension.two :=
  lowerDimension_not_clayEndpoint EuclideanDimension.two (Or.inr (Or.inl rfl))

/-- Three-dimensional consistency data cannot pass the Clay endpoint tag. -/
example : ¬ IsFourDimensionalClayEndpoint EuclideanDimension.three :=
  lowerDimension_not_clayEndpoint EuclideanDimension.three (Or.inr (Or.inr rfl))

/-- A one-dimensional coordinate carrier cannot be relabeled by a real-linear equivalence to `ℝ⁴`. -/
example : ¬ Nonempty
    (EuclideanDimension.one.Spacetime ≃ₗ[ℝ] EuclideanDimension.four.Spacetime) :=
  lowerDimensionalSpacetime_not_linearEquiv_four EuclideanDimension.one (Or.inl rfl)

/-- A two-dimensional coordinate carrier cannot be relabeled by a real-linear equivalence to `ℝ⁴`. -/
example : ¬ Nonempty
    (EuclideanDimension.two.Spacetime ≃ₗ[ℝ] EuclideanDimension.four.Spacetime) :=
  lowerDimensionalSpacetime_not_linearEquiv_four EuclideanDimension.two (Or.inr (Or.inl rfl))

/-- The actual three-dimensional and four-dimensional core bases cannot be identified linearly. -/
example : ¬ Nonempty
    (ThreeDimensionalEuclideanBase ≃ₗ[ℝ] FourDimensionalEuclideanBase) :=
  threeDimensionalBase_not_linearEquiv_fourDimensionalBase

end YangMills.Dimensions.FourDimensionalContractSeparation.Probes
