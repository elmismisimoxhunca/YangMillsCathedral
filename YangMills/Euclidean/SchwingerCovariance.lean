/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Euclidean.SchwingerRegularity

/-!
# Proper-Euclidean covariance for scalar Schwinger distributions

Osterwalder–Schrader I, printed p. 88, axiom `(E1)`, requires invariance under simultaneous
proper Euclidean rotations and translations of all point arguments. This module keeps the proper
rotation and translation named, acts diagonally on the exact `n`-point configuration space, and
constructs the resulting pullback on the actual Mathlib Schwartz space.

A proper rotation is represented by a real linear isometry whose determinant is exactly one. The
pullback convention evaluates a test function at `R xᵢ + a`; OS-I uses this convention in its
printed definition of `f_(a,R)`. This module supplies only scalar `(E1)`: it does not assert
reflection positivity, clustering, reconstruction, or existence.
-/

open scoped SchwartzMap

namespace YangMills

/-- A proper Euclidean rigid motion in the selected spacetime dimension.

The determinant field excludes orientation-reversing orthogonal transformations instead of
silently strengthening `SO(d)` covariance to all of `O(d)`. -/
structure EuclideanProperRigidMotion (d : EuclideanDimension) where
  /-- The orthogonal linear part. -/
  rotation : d.Spacetime ≃ₗᵢ[ℝ] d.Spacetime
  /-- The linear part is orientation-preserving. -/
  rotation_det : LinearMap.det rotation.toLinearEquiv.toLinearMap = 1
  /-- The Euclidean translation. -/
  translation : d.Spacetime

namespace EuclideanProperRigidMotion

/-- The identity proper Euclidean motion. -/
noncomputable def identity (d : EuclideanDimension) : EuclideanProperRigidMotion d where
  rotation := LinearIsometryEquiv.refl ℝ d.Spacetime
  rotation_det := by exact LinearMap.det_id
  translation := 0

/-- A pure translation, with identity proper rotation. -/
noncomputable def pureTranslation (d : EuclideanDimension) (a : d.Spacetime) :
    EuclideanProperRigidMotion d where
  rotation := LinearIsometryEquiv.refl ℝ d.Spacetime
  rotation_det := by exact LinearMap.det_id
  translation := a

end EuclideanProperRigidMotion

/-- The diagonal rotation on an exact Euclidean `n`-point configuration space. -/
noncomputable def euclideanNPointRotation
    (d : EuclideanDimension) {n : ℕ} (motion : EuclideanProperRigidMotion d) :
    EuclideanNPointSpace d n ≃L[ℝ] EuclideanNPointSpace d n :=
  ContinuousLinearEquiv.piCongrRight
    (fun _ : Fin n => motion.rotation.toContinuousLinearEquiv)

/-- The diagonal translation vector on an exact Euclidean `n`-point configuration space. -/
noncomputable def euclideanNPointTranslation
    (d : EuclideanDimension) {n : ℕ} (motion : EuclideanProperRigidMotion d) :
    EuclideanNPointSpace d n :=
  fun _ => motion.translation

/-- Pullback of scalar Schwartz tests by the simultaneous proper rigid motion
`xᵢ ↦ R xᵢ + a`.

It is composed from Mathlib's continuous pullbacks by a continuous linear equivalence and by a
translation, so the result remains in the same Schwartz space. -/
noncomputable def pullbackScalarSchwartzTestFunctionByProperRigidMotion
    (d : EuclideanDimension) {n : ℕ} (motion : EuclideanProperRigidMotion d) :
    ScalarSchwartzTestFunction d n →L[ℂ] ScalarSchwartzTestFunction d n :=
  (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (euclideanNPointRotation d motion)).comp
    (SchwartzMap.compSubConstCLM ℂ (-euclideanNPointTranslation d motion))

/-- The rigid-motion pullback has the exact source-facing pointwise formula. -/
@[simp] theorem pullbackScalarSchwartzTestFunctionByProperRigidMotion_apply
    (d : EuclideanDimension) {n : ℕ} (motion : EuclideanProperRigidMotion d)
    (f : ScalarSchwartzTestFunction d n) (x : EuclideanNPointSpace d n) :
    pullbackScalarSchwartzTestFunctionByProperRigidMotion d motion f x =
      f (fun i => motion.rotation (x i) + motion.translation) := by
  simp only [pullbackScalarSchwartzTestFunctionByProperRigidMotion,
    ContinuousLinearMap.comp_apply, SchwartzMap.compCLMOfContinuousLinearEquiv_apply]
  apply congrArg f
  funext i
  simp [euclideanNPointRotation, euclideanNPointTranslation]

/-- Scalar Schwinger proper-Euclidean covariance `(E1)` for one exact normalized distribution
family. -/
structure ScalarSchwingerEuclideanCovariance
    {d : EuclideanDimension} (family : ScalarSchwingerDistributionFamily d) : Prop where
  /-- Every positive-arity distribution is invariant under every simultaneous proper rotation and
  translation of its exact point arguments. -/
  invariant : ∀ (n : PositiveArity) (motion : EuclideanProperRigidMotion d)
    (f : ScalarSchwartzTestFunction d n.value),
    family.positivePoint n
        (pullbackScalarSchwartzTestFunctionByProperRigidMotion d motion f) =
      family.positivePoint n f

end YangMills
