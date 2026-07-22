/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Minkowski.PoincareComplexSignSL2

/-!
# Hostile probes for concrete complex signs in `SL(2, ℂ)`
-/

namespace YangMills.Minkowski.PoincareComplexSignSL2.Probes

/-- Every literal sign produces an actual determinant-one matrix. -/
theorem exact_determinant_one (sign : ComplexSign) :
    Matrix.det (complexSignToSL2 sign : Matrix (Fin 2) (Fin 2) ℂ) = 1 :=
  Matrix.SpecialLinearGroup.det_coe _

/-- The literal sign embedding is genuinely injective. -/
theorem exact_sign_injection : Function.Injective complexSignToSL2 :=
  complexSignToSL2_injective

/-- The exact matrix-sign subgroup is the image of the injective literal-sign homomorphism. -/
theorem exact_matrix_sign_subgroup (sign : ComplexSign) :
    complexSignToSL2 sign ∈ complexSignSL2Subgroup :=
  ⟨sign, rfl⟩

/-- Every accepted abstract two-sheet kernel is multiplicatively equivalent to the concrete matrix
sign subgroup, without identifying the two ambient groups. -/
noncomputable def exact_abstract_kernel_matrix_sign_equiv
    (d : EuclideanDimension)
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (targetGroup : ProperOrthochronousPoincareTargetGroupData d)
    (cover : ProperOrthochronousPoincareDoubleCoverData d G) :
    properOrthochronousPoincareProjectionKernel d targetGroup cover ≃*
      complexSignSL2Subgroup :=
  projectionKernelMulEquivSL2SignSubgroup d targetGroup cover

/-- The accepted abstract negative kernel element corresponds to the concrete negative matrix-sign
subgroup element under the composed equivalence. -/
theorem exact_abstract_negative_matrix_sign
    (d : EuclideanDimension)
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (targetGroup : ProperOrthochronousPoincareTargetGroupData d)
    (cover : ProperOrthochronousPoincareDoubleCoverData d G) :
    projectionKernelMulEquivSL2SignSubgroup d targetGroup cover
        (negativeProjectionKernelElement d targetGroup cover) =
      complexSignMulEquivSL2Subgroup negativeComplexSign :=
  projectionKernelMulEquivSL2SignSubgroup_negative d targetGroup cover

/-- The negative sign has the exact diagonal/off-diagonal matrix entries of `-I`. -/
theorem exact_negative_matrix_entries :
    (complexSignToSL2 negativeComplexSign : Matrix (Fin 2) (Fin 2) ℂ) 0 0 = -1 ∧
      (complexSignToSL2 negativeComplexSign : Matrix (Fin 2) (Fin 2) ℂ) 1 1 = -1 ∧
      (complexSignToSL2 negativeComplexSign : Matrix (Fin 2) (Fin 2) ℂ) 0 1 = 0 := by
  simp [complexSignToSL2_negative_coe, Matrix.scalar_apply]

/-- The scalar sign image is central in the concrete matrix group. -/
theorem exact_scalar_center
    (sign : ComplexSign) (matrix : ComplexSpecialLinearTwo) :
    complexSignToSL2 sign * matrix = matrix * complexSignToSL2 sign :=
  complexSignToSL2_central sign matrix

/-- Collapsing the negative scalar matrix to the identity is hostilely rejected. -/
theorem negative_matrix_collapse_blocked
    (wrong : complexSignToSL2 negativeComplexSign = 1) : False :=
  complexSignToSL2_negative_ne_one wrong

end YangMills.Minkowski.PoincareComplexSignSL2.Probes
