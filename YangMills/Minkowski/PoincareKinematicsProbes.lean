/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Minkowski.PoincareKinematics

/-!
# Hostile probes for proper-orthochronous Poincaré kinematics

The probes separately force Minkowski-form preservation, determinant-one properness, future-time
orientation, a wired nonzero translation, and injectivity of the affine action.
-/

namespace YangMills.Minkowski.PoincareKinematics.Probes

/-- Identity has determinant one. -/
theorem identity_is_proper
    (d : EuclideanDimension) :
    LinearMap.det
      (ProperOrthochronousLorentzTransformation.identity d).linear.toLinearMap = 1 :=
  (ProperOrthochronousLorentzTransformation.identity d).determinant_one

/-- Identity preserves the selected future-time orientation. -/
theorem identity_is_orthochronous
    (d : EuclideanDimension) :
    0 < (ProperOrthochronousLorentzTransformation.identity d).linear
      (d.basisVector d.timeIndex) d.timeIndex :=
  (ProperOrthochronousLorentzTransformation.identity d).future_time_positive

/-- Every accepted Lorentz map retains Minkowski value one on the transformed time basis. -/
theorem transformed_time_is_unit_timelike
    {d : EuclideanDimension} (L : ProperOrthochronousLorentzTransformation d) :
    d.minkowskiQuadraticForm (L.linear (d.basisVector d.timeIndex)) = 1 :=
  L.transformed_time_minkowski_norm

/-- Every available transformed spatial basis retains Minkowski value minus one. -/
theorem transformed_spatial_is_unit_spacelike
    {d : EuclideanDimension} (L : ProperOrthochronousLorentzTransformation d)
    (i : Fin d.spatialDimension) :
    d.minkowskiQuadraticForm (L.linear (d.basisVector (d.spatialIndexSucc i))) = -1 := by
  rw [L.preserves_minkowski]
  exact d.minkowskiQuadraticForm_spatial_basisVector i

/-- Time reversal cannot masquerade as an orthochronous transformation. -/
theorem time_reversal_rejected
    {d : EuclideanDimension} (L : ProperOrthochronousLorentzTransformation d)
    (hreverse : L.linear (d.basisVector d.timeIndex) d.timeIndex = -1) : False :=
  L.time_reversal_blocked hreverse

/-- A determinant-minus-one map cannot masquerade as proper. -/
theorem orientation_reversal_rejected
    {d : EuclideanDimension} (L : ProperOrthochronousLorentzTransformation d)
    (hdet : LinearMap.det L.linear.toLinearMap = -1) : False :=
  L.determinant_minus_one_blocked hdet

/-- A pure translation acts by exact addition rather than being ignored. -/
theorem exact_pure_translation
    (d : EuclideanDimension) (a x : Minkowski.Spacetime d) :
    (ProperOrthochronousPoincareTransformation.pureTranslation d a).act x = x + a :=
  ProperOrthochronousPoincareTransformation.pureTranslation_act d a x

/-- Translating the origin by the time basis reaches that exact nonzero Minkowski vector. -/
theorem time_translation_moves_origin
    (d : EuclideanDimension) :
    (ProperOrthochronousPoincareTransformation.pureTranslation d
      (d.basisVector d.timeIndex)).act 0 = d.basisVector d.timeIndex := by
  simp

/-- The nonzero translated origin has Minkowski quadratic value one. -/
theorem time_translated_origin_minkowski_value
    (d : EuclideanDimension) :
    d.minkowskiQuadraticForm
      ((ProperOrthochronousPoincareTransformation.pureTranslation d
        (d.basisVector d.timeIndex)).act 0) = 1 := by
  rw [time_translation_moves_origin]
  exact d.minkowskiQuadraticForm_time_basisVector

/-- A Poincaré affine action cannot collapse distinct spacetime points. -/
theorem affine_action_injective
    {d : EuclideanDimension} (p : ProperOrthochronousPoincareTransformation d) :
    Function.Injective p.act :=
  p.act_injective

end YangMills.Minkowski.PoincareKinematics.Probes
