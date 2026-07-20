/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Mathematics.LieGroupRightInvariantField

namespace YangMills.Mathematics.LieGroupRightInvariantField.Probes

open scoped Manifold ContDiff

universe uE uH uG

noncomputable section

variable {E : Type uE} {H : Type uH}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H)
    {G : Type uG} [Group G] [TopologicalSpace G] [ChartedSpace H G]
    [LieGroup I ∞ G]

/-- Right translation carries the field value at `g` to its value at `g * a`. -/
theorem exact_right_translation_invariance
    (Y : GroupLieAlgebra I G) (g a : G) :
    mfderiv I I (fun q : G => q * a) g (mulRightInvariantVectorField I Y g) =
      mulRightInvariantVectorField I Y (g * a) :=
  mfderiv_mul_right_mulRightInvariantVectorField I Y g a

/-- Left trivialization has the exact inverse-adjoint coefficient. -/
theorem exact_left_trivialized_coefficient
    (Y : GroupLieAlgebra I G) (g : G) :
    mulRightInvariantVectorField I Y g =
      mulInvariantVectorField (lieGroupAdjoint I g⁻¹ Y) g :=
  mulRightInvariantVectorField_eq_mulInvariant_adjoint_inv I Y g

/-- The tangent-bundle-valued right-invariant field is genuinely smooth. -/
theorem exact_right_invariant_field_smooth (Y : GroupLieAlgebra I G) :
    ContMDiff I I.tangent ∞
      (fun g : G => (⟨g, mulRightInvariantVectorField I Y g⟩ : TangentBundle I G)) :=
  contMDiff_mulRightInvariantVectorField I Y

/-- The inverse-adjoint orbit keeps the exact inverse and generator. -/
theorem exact_inverse_adjoint_orbit
    (Y : GroupLieAlgebra I G) (g : G) :
    inverseAdjointOrbit I Y g = lieGroupAdjoint I g⁻¹ Y := rfl

/-- The exact inverse-adjoint orbit has smooth model coordinates. -/
theorem exact_inverse_adjoint_orbit_smooth (Y : GroupLieAlgebra I G) :
    ContMDiff I 𝓘(ℝ, E) ∞
      (fun g : G => groupLieAlgebraModelEquiv I (inverseAdjointOrbit I Y g)) :=
  inverseAdjointOrbit_contMDiff I Y

/-- Failure of the exact right-translation law is rejected. -/
theorem mismatched_right_translation_blocked
    (Y : GroupLieAlgebra I G) (g a : G)
    (wrong : mfderiv I I (fun q : G => q * a) g (mulRightInvariantVectorField I Y g) ≠
      mulRightInvariantVectorField I Y (g * a)) : False :=
  wrong (mfderiv_mul_right_mulRightInvariantVectorField I Y g a)

/-- A changed inverse-adjoint coefficient is rejected. -/
theorem mismatched_left_trivialized_coefficient_blocked
    (Y : GroupLieAlgebra I G) (g : G)
    (wrong : mulRightInvariantVectorField I Y g ≠
      mulInvariantVectorField (lieGroupAdjoint I g⁻¹ Y) g) : False :=
  wrong (mulRightInvariantVectorField_eq_mulInvariant_adjoint_inv I Y g)

end

end YangMills.Mathematics.LieGroupRightInvariantField.Probes
