/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Minkowski.MinkowskiBilinearForm

/-!
# Proper-orthochronous Minkowski/Poincaré kinematics

Streater–Wightman, printed pp. 9–10, equations `(1-4)`–`(1-9)`, fixes the four-dimensional
mostly-minus scalar product, defines Lorentz transformations by its preservation, and classifies the
proper and orthochronous component by determinant and future-time sign. Printed p. 14, equations
`(1-22)`–`(1-23)`, gives the affine Poincaré action and inhomogeneous `SL(2,ℂ)` group. Printed p. 97
later requires one continuous unitary representation of that cover. Before representing it on a
Hilbert space, this module records the underlying real affine kinematics in every supported
spacetime dimension. Extending the source's four-dimensional formulas to dimensions one through
four is explicit project infrastructure, not a verbatim source quantifier.

A Lorentz transformation preserves the project's chosen mostly-minus Minkowski quadratic form, has
determinant one, and sends the selected future time basis to a vector with positive time component.
A Poincaré transformation pairs it with a translation and acts by `x ↦ Λx + a`.

No topological group, cover, Hilbert-space representation, field, reconstruction, spectrum, or mass
gap is introduced here. In particular, this Minkowski surface is independent of the Euclidean
Schwinger candidate.
-/

namespace YangMills.Minkowski

/-- The real coordinate carrier used for Minkowski kinematics in dimension `d`.
Its quadratic form is always supplied separately and is never confused with Euclidean signature. -/
abbrev Spacetime (d : EuclideanDimension) := d.CoordinateVector

/-- A proper-orthochronous Lorentz transformation for the chosen mostly-minus quadratic form. -/
structure ProperOrthochronousLorentzTransformation (d : EuclideanDimension) where
  /-- The invertible real-linear spacetime transformation. -/
  linear : Spacetime d ≃ₗ[ℝ] Spacetime d
  /-- Exact preservation of the Minkowski quadratic form. -/
  preserves_minkowski : ∀ x,
    d.minkowskiQuadraticForm (linear x) = d.minkowskiQuadraticForm x
  /-- Properness excludes determinant-minus-one Lorentz transformations. -/
  determinant_one : LinearMap.det linear.toLinearMap = 1
  /-- Orthochronousness excludes reversal of the selected future time direction. -/
  future_time_positive :
    0 < linear (d.basisVector d.timeIndex) d.timeIndex

namespace ProperOrthochronousLorentzTransformation

/-- Identity belongs to the proper-orthochronous Lorentz component. -/
noncomputable def identity (d : EuclideanDimension) :
    ProperOrthochronousLorentzTransformation d where
  linear := LinearEquiv.refl ℝ _
  preserves_minkowski := by simp
  determinant_one := LinearMap.det_id
  future_time_positive := by
    simp [EuclideanDimension.basisVector, EuclideanDimension.timeIndex]

/-- Every accepted Lorentz transformation sends the time basis to another unit timelike vector. -/
theorem transformed_time_minkowski_norm
    {d : EuclideanDimension} (L : ProperOrthochronousLorentzTransformation d) :
    d.minkowskiQuadraticForm (L.linear (d.basisVector d.timeIndex)) = 1 := by
  rw [L.preserves_minkowski]
  exact d.minkowskiQuadraticForm_time_basisVector

/-- Every accepted Lorentz transformation preserves the exact polarized Minkowski bilinear form.
This is derived from its existing quadratic-form field rather than supplied independently. -/
theorem preserves_minkowskiBilinear
    {d : EuclideanDimension} (L : ProperOrthochronousLorentzTransformation d)
    (x y : Spacetime d) :
    minkowskiBilinearForm d (L.linear x) (L.linear y) =
      minkowskiBilinearForm d x y :=
  minkowskiBilinearForm_map_eq_of_quadratic_preserving d
    L.linear.toLinearMap L.preserves_minkowski x y

/-- The time component of the inverse image of the time basis equals the forward time-basis
component. This is the key algebraic orientation fact needed for inverse closure. -/
theorem inverse_time_eq_forward_time
    {d : EuclideanDimension} (L : ProperOrthochronousLorentzTransformation d) :
    (L.linear.symm (d.basisVector d.timeIndex)) d.timeIndex =
      (L.linear (d.basisVector d.timeIndex)) d.timeIndex := by
  have preserved := L.preserves_minkowskiBilinear
    (d.basisVector d.timeIndex)
    (L.linear.symm (d.basisVector d.timeIndex))
  rw [L.linear.apply_symm_apply,
    minkowskiBilinearForm_timeBasis_left,
    minkowskiBilinearForm_timeBasis_right] at preserved
  exact preserved.symm

/-- The inverse linear transformation sends the time basis to positive time. -/
theorem inverse_future_time_positive
    {d : EuclideanDimension} (L : ProperOrthochronousLorentzTransformation d) :
    0 < (L.linear.symm (d.basisVector d.timeIndex)) d.timeIndex := by
  rw [L.inverse_time_eq_forward_time]
  exact L.future_time_positive

/-- The exact inverse of a proper-orthochronous Lorentz transformation is again
proper-orthochronous. All four fields are derived from the original transformation. -/
noncomputable def inverse
    {d : EuclideanDimension} (L : ProperOrthochronousLorentzTransformation d) :
    ProperOrthochronousLorentzTransformation d where
  linear := L.linear.symm
  preserves_minkowski := by
    intro x
    calc
      d.minkowskiQuadraticForm (L.linear.symm x) =
          d.minkowskiQuadraticForm (L.linear (L.linear.symm x)) :=
        (L.preserves_minkowski (L.linear.symm x)).symm
      _ = d.minkowskiQuadraticForm x := by rw [L.linear.apply_symm_apply]
  determinant_one := by
    have composition : L.linear.toLinearMap ∘ₗ L.linear.symm.toLinearMap =
        LinearMap.id := by
      apply LinearMap.ext
      intro x
      exact L.linear.apply_symm_apply x
    have determinantComposition := congrArg LinearMap.det composition
    rw [LinearMap.det_comp, L.determinant_one, one_mul,
      LinearMap.det_id] at determinantComposition
    exact determinantComposition
  future_time_positive := L.inverse_future_time_positive

/-- The constructed inverse has exactly the inverse linear equivalence. -/
@[simp]
theorem inverse_linear
    {d : EuclideanDimension} (L : ProperOrthochronousLorentzTransformation d) :
    L.inverse.linear = L.linear.symm :=
  rfl

/-- A candidate sending the selected future time basis to time component `-1` is rejected. -/
theorem time_reversal_blocked
    {d : EuclideanDimension} (L : ProperOrthochronousLorentzTransformation d)
    (hreverse : L.linear (d.basisVector d.timeIndex) d.timeIndex = -1) : False := by
  have hpositive := L.future_time_positive
  rw [hreverse] at hpositive
  linarith

/-- A determinant-minus-one candidate is rejected by properness. -/
theorem determinant_minus_one_blocked
    {d : EuclideanDimension} (L : ProperOrthochronousLorentzTransformation d)
    (hdet : LinearMap.det L.linear.toLinearMap = -1) : False := by
  rw [L.determinant_one] at hdet
  norm_num at hdet

end ProperOrthochronousLorentzTransformation

/-- A proper-orthochronous affine Poincaré transformation. -/
structure ProperOrthochronousPoincareTransformation (d : EuclideanDimension) where
  /-- The Lorentz linear part. -/
  lorentz : ProperOrthochronousLorentzTransformation d
  /-- The independent Minkowski translation. -/
  translation : Spacetime d

namespace ProperOrthochronousPoincareTransformation

/-- Identity affine transformation. -/
noncomputable def identity (d : EuclideanDimension) :
    ProperOrthochronousPoincareTransformation d :=
  ⟨ProperOrthochronousLorentzTransformation.identity d, 0⟩

/-- Pure Minkowski translation with identity Lorentz part. -/
noncomputable def pureTranslation
    (d : EuclideanDimension) (a : Spacetime d) :
    ProperOrthochronousPoincareTransformation d :=
  ⟨ProperOrthochronousLorentzTransformation.identity d, a⟩

/-- Exact affine action `x ↦ Λx + a`. -/
def act
    {d : EuclideanDimension} (p : ProperOrthochronousPoincareTransformation d)
    (x : Spacetime d) : Spacetime d :=
  p.lorentz.linear x + p.translation

@[simp] theorem identity_act
    (d : EuclideanDimension) (x : Spacetime d) :
    (identity d).act x = x := by
  simp [act, identity, ProperOrthochronousLorentzTransformation.identity]

@[simp] theorem pureTranslation_act
    (d : EuclideanDimension) (a x : Spacetime d) :
    (pureTranslation d a).act x = x + a := by
  simp [act, pureTranslation, ProperOrthochronousLorentzTransformation.identity]

/-- The affine action remains injective because its Lorentz part is invertible. -/
theorem act_injective
    {d : EuclideanDimension} (p : ProperOrthochronousPoincareTransformation d) :
    Function.Injective p.act := by
  intro x y h
  have hlinear : p.lorentz.linear x = p.lorentz.linear y := by
    exact add_right_cancel h
  exact p.lorentz.linear.injective hlinear

end ProperOrthochronousPoincareTransformation

end YangMills.Minkowski
