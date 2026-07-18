/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Euclidean.SchwingerCovariance

/-!
# Hostile probes for scalar Schwinger Euclidean covariance

The probes reject orientation reversal, exhibit a nonzero translation in every supported dimension,
verify that it reaches the exact Schwartz pullback, and tie `(E1)` to the same distribution family,
arity, motion, and test function.
-/

namespace YangMills.Euclidean.SchwingerCovariance.Probes

/-- The first Euclidean coordinate unit vector exists in every supported positive dimension. -/
noncomputable def firstCoordinateUnit (d : EuclideanDimension) : d.Spacetime :=
  EuclideanSpace.single ⟨0, d.one_le⟩ 1

/-- The designated first-coordinate translation is genuinely nonzero. -/
theorem firstCoordinateUnit_ne_zero (d : EuclideanDimension) :
    firstCoordinateUnit d ≠ 0 := by
  intro hzero
  have atFirst := congrArg (fun x : d.Spacetime => x ⟨0, d.one_le⟩) hzero
  simp [firstCoordinateUnit] at atFirst

/-- A proper rigid motion cannot carry determinant `-1`; orientation-reversing orthogonal maps do
not silently enter the `SO(d)` requirement. -/
theorem orientation_reversing_determinant_blocked
    {d : EuclideanDimension} (motion : EuclideanProperRigidMotion d)
    (hreversing : LinearMap.det motion.rotation.toLinearEquiv.toLinearMap = -1) : False := by
  rw [motion.rotation_det] at hreversing
  norm_num at hreversing

/-- The nonzero pure translation reaches every point argument of the exact Schwartz pullback. -/
theorem firstCoordinateTranslation_pullback_apply
    (d : EuclideanDimension) {n : ℕ} (f : ScalarSchwartzTestFunction d n)
    (x : EuclideanNPointSpace d n) :
    pullbackScalarSchwartzTestFunctionByProperRigidMotion d
        (EuclideanProperRigidMotion.pureTranslation d (firstCoordinateUnit d)) f x =
      f (fun i => x i + firstCoordinateUnit d) := by
  rw [pullbackScalarSchwartzTestFunctionByProperRigidMotion_apply]
  rfl

/-- The covariance projection retains the exact family, arity, proper motion, and test function. -/
theorem exact_euclidean_covariance
    {d : EuclideanDimension} {family : ScalarSchwingerDistributionFamily d}
    (covariance : ScalarSchwingerEuclideanCovariance family)
    (n : PositiveArity) (motion : EuclideanProperRigidMotion d)
    (f : ScalarSchwartzTestFunction d n.value) :
    family.positivePoint n
        (pullbackScalarSchwartzTestFunctionByProperRigidMotion d motion f) =
      family.positivePoint n f :=
  covariance.invariant n motion f

/-- A changed value under the exact designated proper motion contradicts `(E1)`; covariance of an
unrelated family cannot discharge the requirement. -/
theorem euclidean_covariance_value_replacement_blocked
    {d : EuclideanDimension} {family : ScalarSchwingerDistributionFamily d}
    (covariance : ScalarSchwingerEuclideanCovariance family)
    (n : PositiveArity) (motion : EuclideanProperRigidMotion d)
    (f : ScalarSchwartzTestFunction d n.value)
    (hmismatch :
      family.positivePoint n
          (pullbackScalarSchwartzTestFunctionByProperRigidMotion d motion f) ≠
        family.positivePoint n f) : False :=
  hmismatch (covariance.invariant n motion f)

end YangMills.Euclidean.SchwingerCovariance.Probes
