/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Minkowski.ComplexLorentzKinematics

/-!
# Hostile probes for proper complex Lorentz kinematics

The probes expose the non-Hermitian bilinear form, determinant-one condition, group action,
continuity, and a concrete nonidentity four-dimensional transformation. They reject determinant
`-1` and form-nonpreserving substitutes.
-/

namespace YangMills.Minkowski.ComplexLorentzKinematics.Probes

noncomputable section

/-- The form is the exact complex-bilinear mostly-minus coordinate sum, with no conjugation. -/
theorem exact_complex_bilinear_form
    (d : EuclideanDimension) (z w : ComplexifiedSpacetime d) :
    complexMinkowskiBilinearForm d z w =
      ∑ i, (d.minkowskiWeight i : ℂ) * z i * w i :=
  rfl

/-- Every accepted transformation preserves the exact form and has determinant one. -/
theorem exact_proper_complex_lorentz_laws
    {d : EuclideanDimension} (transformation : ProperComplexLorentzTransformation d)
    (z w : ComplexifiedSpacetime d) :
    complexMinkowskiBilinearForm d (transformation.linear z)
        (transformation.linear w) = complexMinkowskiBilinearForm d z w ∧
      LinearMap.det transformation.linear.toLinearEquiv.toLinearMap = 1 :=
  ⟨transformation.preserves_bilinear z w, transformation.determinant_one⟩

/-- Simultaneous action follows exact group multiplication and inversion. -/
theorem exact_configuration_action
    {d : EuclideanDimension}
    (first second : ProperComplexLorentzTransformation d)
    {n : ℕ} (z : Fin n → ComplexifiedSpacetime d) :
    ProperComplexLorentzTransformation.actConfiguration (first * second) z =
        ProperComplexLorentzTransformation.actConfiguration first
          (ProperComplexLorentzTransformation.actConfiguration second z) ∧
      ProperComplexLorentzTransformation.actConfiguration first⁻¹
          (ProperComplexLorentzTransformation.actConfiguration first z) = z :=
  ⟨ProperComplexLorentzTransformation.actConfiguration_mul first second z,
    ProperComplexLorentzTransformation.actConfiguration_inv first z⟩

/-- Fixed-transformation action is genuinely continuous on every finite configuration space. -/
theorem exact_configuration_action_continuous
    {d : EuclideanDimension}
    (transformation : ProperComplexLorentzTransformation d) (n : ℕ) :
    Continuous (ProperComplexLorentzTransformation.actConfiguration transformation :
      (Fin n → ComplexifiedSpacetime d) → Fin n → ComplexifiedSpacetime d) :=
  ProperComplexLorentzTransformation.continuous_actConfiguration transformation n

/-- The proper complex group is not represented only by the identity in four dimensions. -/
theorem four_dimensional_nonidentity_exists :
    ∃ transformation : ProperComplexLorentzTransformation EuclideanDimension.four,
      transformation ≠ 1 :=
  ⟨ProperComplexLorentzTransformation.fourDimensionalComplexNegation,
    ProperComplexLorentzTransformation.fourDimensionalComplexNegation_ne_one⟩

/-- The concrete four-dimensional nonidentity acts by coordinatewise negation. -/
theorem four_dimensional_negation_action
    (z : ComplexifiedSpacetime EuclideanDimension.four) :
    ProperComplexLorentzTransformation.fourDimensionalComplexNegation.linear z = -z := by
  rfl

/-- A determinant-minus-one complex automorphism cannot be substituted for a proper one. -/
theorem determinant_minus_one_blocked
    {d : EuclideanDimension}
    (candidate : ComplexifiedSpacetime d ≃L[ℂ] ComplexifiedSpacetime d)
    (determinant_minus_one :
      LinearMap.det candidate.toLinearEquiv.toLinearMap = -1) :
    ¬ ∃ transformation : ProperComplexLorentzTransformation d,
      transformation.linear = candidate := by
  rintro ⟨transformation, equality⟩
  have determinant_one := transformation.determinant_one
  rw [equality, determinant_minus_one] at determinant_one
  norm_num at determinant_one

/-- A complex automorphism failing the bilinear law cannot be substituted for a Lorentz one. -/
theorem non_lorentz_automorphism_blocked
    {d : EuclideanDimension}
    (candidate : ComplexifiedSpacetime d ≃L[ℂ] ComplexifiedSpacetime d)
    (z w : ComplexifiedSpacetime d)
    (failure : complexMinkowskiBilinearForm d (candidate z) (candidate w) ≠
      complexMinkowskiBilinearForm d z w) :
    ¬ ∃ transformation : ProperComplexLorentzTransformation d,
      transformation.linear = candidate := by
  rintro ⟨transformation, equality⟩
  apply failure
  rw [← equality]
  exact transformation.preserves_bilinear z w

end

end YangMills.Minkowski.ComplexLorentzKinematics.Probes
