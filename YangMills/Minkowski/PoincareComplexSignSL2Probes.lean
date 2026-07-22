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
