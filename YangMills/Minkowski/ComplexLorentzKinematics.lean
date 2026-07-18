/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Minkowski.WightmanTubeGeometry

/-!
# Proper complex Lorentz kinematics

Streater–Wightman printed pp. 13–14 defines the complex Lorentz group by preservation of the
complex-bilinear Minkowski form and distinguishes the proper component by determinant `+1`.
This module packages the corresponding finite-dimensional complex-linear transformations in every
project dimension `1 ≤ d ≤ 4`. The source formulas are four-dimensional; dimensions one through
three are project consistency infrastructure, not a verbatim source quantifier.

The source's connectedness and complex Lie-group/analytic structure are not formalized here. The
word “proper” records the determinant-one condition only. No extended-tube continuation or quantum
correlator is constructed.
-/

namespace YangMills.Minkowski

noncomputable section

/-- Complex-bilinear, not Hermitian, extension of the mostly-minus Minkowski form. -/
def complexMinkowskiBilinearForm (d : EuclideanDimension)
    (z w : ComplexifiedSpacetime d) : ℂ :=
  ∑ i, (d.minkowskiWeight i : ℂ) * z i * w i

/-- A determinant-one complex-linear automorphism preserving the complex-bilinear Minkowski form.
No group topology or connectedness theorem is hidden in this carrier. -/
@[ext]
structure ProperComplexLorentzTransformation (d : EuclideanDimension) where
  linear : ComplexifiedSpacetime d ≃L[ℂ] ComplexifiedSpacetime d
  preserves_bilinear : ∀ z w,
    complexMinkowskiBilinearForm d (linear z) (linear w) =
      complexMinkowskiBilinearForm d z w
  determinant_one : LinearMap.det linear.toLinearEquiv.toLinearMap = 1

namespace ProperComplexLorentzTransformation

variable {d : EuclideanDimension}

instance : One (ProperComplexLorentzTransformation d) := ⟨{
  linear := 1
  preserves_bilinear := by intros; rfl
  determinant_one := by
    rw [show (1 : ComplexifiedSpacetime d ≃L[ℂ]
        ComplexifiedSpacetime d).toLinearEquiv.toLinearMap = LinearMap.id from rfl,
      LinearMap.det_id] }⟩

instance : Mul (ProperComplexLorentzTransformation d) := ⟨fun first second => {
  linear := first.linear * second.linear
  preserves_bilinear := by
    intro z w
    exact (first.preserves_bilinear _ _).trans (second.preserves_bilinear _ _)
  determinant_one := by
    rw [show (first.linear * second.linear).toLinearEquiv.toLinearMap =
        first.linear.toLinearEquiv.toLinearMap ∘ₗ
          second.linear.toLinearEquiv.toLinearMap from rfl,
      LinearMap.det_comp, first.determinant_one, second.determinant_one, one_mul] }⟩

instance : Inv (ProperComplexLorentzTransformation d) := ⟨fun transformation => {
  linear := transformation.linear⁻¹
  preserves_bilinear := by
    intro z w
    have preserved := transformation.preserves_bilinear
      (transformation.linear⁻¹ z) (transformation.linear⁻¹ w)
    calc
      complexMinkowskiBilinearForm d
          (transformation.linear⁻¹ z) (transformation.linear⁻¹ w) =
        complexMinkowskiBilinearForm d
          (transformation.linear (transformation.linear⁻¹ z))
          (transformation.linear (transformation.linear⁻¹ w)) := preserved.symm
      _ = complexMinkowskiBilinearForm d z w := by
        change complexMinkowskiBilinearForm d
          (transformation.linear (transformation.linear.symm z))
          (transformation.linear (transformation.linear.symm w)) = _
        rw [transformation.linear.apply_symm_apply,
          transformation.linear.apply_symm_apply]
  determinant_one := by
    have composition : transformation.linear.toLinearEquiv.toLinearMap ∘ₗ
        (transformation.linear⁻¹).toLinearEquiv.toLinearMap = LinearMap.id := by
      apply LinearMap.ext
      intro z
      exact transformation.linear.apply_symm_apply z
    have determinantComposition := congrArg LinearMap.det composition
    rw [LinearMap.det_comp, transformation.determinant_one, one_mul,
      LinearMap.det_id] at determinantComposition
    exact determinantComposition }⟩

instance : Group (ProperComplexLorentzTransformation d) where
  mul_assoc first second third := by
    apply ProperComplexLorentzTransformation.ext
    exact mul_assoc _ _ _
  one_mul transformation := by
    apply ProperComplexLorentzTransformation.ext
    exact one_mul _
  mul_one transformation := by
    apply ProperComplexLorentzTransformation.ext
    exact mul_one _
  inv_mul_cancel transformation := by
    apply ProperComplexLorentzTransformation.ext
    exact inv_mul_cancel _

/-- In four dimensions, complex coordinate negation is a nonidentity proper complex Lorentz
transformation. Streater–Wightman notes that `1` and `-1` are connected inside the proper complex
group; only the algebraic transformation is constructed here. -/
def fourDimensionalComplexNegation :
    ProperComplexLorentzTransformation EuclideanDimension.four where
  linear := ContinuousLinearEquiv.neg ℂ
  preserves_bilinear := by
    intro z w
    simp [complexMinkowskiBilinearForm]
  determinant_one := by
    rw [show (ContinuousLinearEquiv.neg ℂ :
        ComplexifiedSpacetime EuclideanDimension.four ≃L[ℂ]
          ComplexifiedSpacetime EuclideanDimension.four).toLinearEquiv.toLinearMap =
        (-1 : ℂ) • LinearMap.id from by ext z i; simp]
    rw [LinearMap.det_smul, LinearMap.det_id]
    norm_num [EuclideanDimension.four, ComplexifiedSpacetime]

/-- Four-dimensional complex negation is genuinely nonidentity. -/
theorem fourDimensionalComplexNegation_ne_one :
    fourDimensionalComplexNegation ≠ 1 := by
  intro equality
  have functionEquality := congrArg
    (fun transformation : ProperComplexLorentzTransformation EuclideanDimension.four =>
      transformation.linear (fun _ => 1)) equality
  have coordinateEquality := congrFun functionEquality EuclideanDimension.four.timeIndex
  change (-1 : ℂ) = 1 at coordinateEquality
  norm_num at coordinateEquality

/-- Simultaneous action on every relative complex spacetime coordinate. -/
def actConfiguration (transformation : ProperComplexLorentzTransformation d)
    {n : ℕ} (z : Fin n → ComplexifiedSpacetime d) :
    Fin n → ComplexifiedSpacetime d :=
  fun j => transformation.linear (z j)

@[simp]
theorem actConfiguration_one {n : ℕ} (z : Fin n → ComplexifiedSpacetime d) :
    actConfiguration (1 : ProperComplexLorentzTransformation d) z = z :=
  rfl

@[simp]
theorem actConfiguration_mul
    (first second : ProperComplexLorentzTransformation d)
    {n : ℕ} (z : Fin n → ComplexifiedSpacetime d) :
    actConfiguration (first * second) z =
      actConfiguration first (actConfiguration second z) :=
  rfl

@[simp]
theorem actConfiguration_inv
    (transformation : ProperComplexLorentzTransformation d)
    {n : ℕ} (z : Fin n → ComplexifiedSpacetime d) :
    actConfiguration transformation⁻¹ (actConfiguration transformation z) = z := by
  funext j
  exact transformation.linear.symm_apply_apply (z j)

/-- For each fixed proper complex Lorentz transformation, simultaneous finite-configuration action
is continuous. -/
theorem continuous_actConfiguration
    (transformation : ProperComplexLorentzTransformation d) (n : ℕ) :
    Continuous (actConfiguration transformation :
      (Fin n → ComplexifiedSpacetime d) → Fin n → ComplexifiedSpacetime d) := by
  apply continuous_pi
  intro j
  exact transformation.linear.continuous.comp (continuous_apply j)

end ProperComplexLorentzTransformation

end

end YangMills.Minkowski
