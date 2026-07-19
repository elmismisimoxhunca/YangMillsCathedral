/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Dimensions.FourDimensionalContinuumCoreAcceptance
import YangMills.Dimensions.ThreeDimensionalContinuumCoreAcceptance

/-!
# Separation of lower-dimensional consistency regimes from the Clay endpoint

Dimensions one through three are project consistency regimes, while the Clay/Jaffe–Witten endpoint
is four-dimensional spacetime. This module records both index-level separation and a concrete
coordinate-carrier obstruction: no lower-dimensional real Euclidean spacetime is linearly
equivalent to the four-dimensional carrier.

These are dimension-index and real-linear coordinate-carrier separation lemmas, not yet a
witness-level separation theorem for the still-absent final acceptance proposition and not
nonexistence results for lower-dimensional theories.
-/

namespace YangMills.Dimensions

/-- The exact predicate selecting the Clay spacetime dimension. -/
def IsFourDimensionalClayEndpoint (d : EuclideanDimension) : Prop :=
  d = EuclideanDimension.four

/-- Every supported lower-dimensional consistency index is rejected by the Clay endpoint predicate. -/
theorem lowerDimension_not_clayEndpoint
    (d : EuclideanDimension)
    (lower : d = EuclideanDimension.one ∨ d = EuclideanDimension.two ∨
      d = EuclideanDimension.three) :
    ¬ IsFourDimensionalClayEndpoint d := by
  rcases lower with rfl | rfl | rfl <;>
    simp [IsFourDimensionalClayEndpoint, EuclideanDimension.one,
      EuclideanDimension.two, EuclideanDimension.three, EuclideanDimension.four]

/-- No supported lower-dimensional Euclidean coordinate spacetime is real-linearly equivalent to
four-dimensional spacetime. The obstruction is the exact finite rank, not an arbitrary tag. -/
theorem lowerDimensionalSpacetime_not_linearEquiv_four
    (d : EuclideanDimension)
    (lower : d = EuclideanDimension.one ∨ d = EuclideanDimension.two ∨
      d = EuclideanDimension.three) :
    ¬ Nonempty (d.Spacetime ≃ₗ[ℝ] EuclideanDimension.four.Spacetime) := by
  rintro ⟨equiv⟩
  have ranks := LinearEquiv.finrank_eq equiv
  rcases lower with rfl | rfl | rfl <;>
    norm_num [EuclideanDimension.finrank_spacetime] at ranks

/-- In particular, the existing three-dimensional core base cannot be substituted by a linear
coordinate identification with the four-dimensional core base. -/
theorem threeDimensionalBase_not_linearEquiv_fourDimensionalBase :
    ¬ Nonempty (ThreeDimensionalEuclideanBase ≃ₗ[ℝ] FourDimensionalEuclideanBase) :=
  lowerDimensionalSpacetime_not_linearEquiv_four EuclideanDimension.three (Or.inr (Or.inr rfl))

end YangMills.Dimensions
