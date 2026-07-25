/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Euclidean.SchwingerCovariance
import YangMills.Euclidean.SchwingerSequenceInvolution

/-!
# Exact translations of scalar Schwinger tests and finite sequences

OS-I `(E4)` translates one cluster of test functions by a large spatial displacement. This module
constructs the prior algebraic ingredient for arbitrary Euclidean displacements: the exact
Schwartz pullback `f(x₁ + a, …, xₙ + a)`, its inverse, and its componentwise lift to unrestricted
finite sequences.

No spatial-direction subtype, limit, or clustering axiom is stated here. In particular, finite
cutoff/lattice clustering is not identified with continuum OS clustering.
-/

namespace YangMills

/-- Simultaneous translation pullback on one exact scalar Schwartz arity. -/
noncomputable def translateScalarSchwartzTestFunction
    (d : EuclideanDimension) {n : ℕ} (a : d.Spacetime) :
    ScalarSchwartzTestFunction d n →L[ℂ] ScalarSchwartzTestFunction d n :=
  pullbackScalarSchwartzTestFunctionByProperRigidMotion d
    (EuclideanProperRigidMotion.pureTranslation d a)

/-- Translation pullback has the exact pointwise convention `f(xᵢ + a)`. -/
@[simp] theorem translateScalarSchwartzTestFunction_apply
    (d : EuclideanDimension) {n : ℕ} (a : d.Spacetime)
    (f : ScalarSchwartzTestFunction d n) (x : EuclideanNPointSpace d n) :
    translateScalarSchwartzTestFunction d a f x = f (fun i => x i + a) := by
  simp [translateScalarSchwartzTestFunction,
    EuclideanProperRigidMotion.pureTranslation]

/-- Translation by `-a` after translation by `a` restores the exact Schwartz test. -/
theorem translateScalarSchwartzTestFunction_inverse
    (d : EuclideanDimension) {n : ℕ} (a : d.Spacetime)
    (f : ScalarSchwartzTestFunction d n) :
    translateScalarSchwartzTestFunction d (-a)
      (translateScalarSchwartzTestFunction d a f) = f := by
  ext x
  simp only [translateScalarSchwartzTestFunction_apply]
  apply congrArg f
  funext i
  abel

/-- Translation pullbacks compose according to addition of displacements. -/
theorem translateScalarSchwartzTestFunction_comp
    (d : EuclideanDimension) {n : ℕ} (a b : d.Spacetime)
    (f : ScalarSchwartzTestFunction d n) :
    translateScalarSchwartzTestFunction d b
        (translateScalarSchwartzTestFunction d a f) =
      translateScalarSchwartzTestFunction d (b + a) f := by
  ext x
  simp only [translateScalarSchwartzTestFunction_apply]
  apply congrArg f
  funext i
  abel

/-- Translation fixes every zero-arity Schwartz test because the configuration is empty. -/
@[simp] theorem translateScalarSchwartzTestFunction_zero_arity
    (d : EuclideanDimension) (a : d.Spacetime)
    (f : ScalarSchwartzTestFunction d 0) :
    translateScalarSchwartzTestFunction d a f = f := by
  ext x
  rw [translateScalarSchwartzTestFunction_apply]
  apply congrArg f
  funext i
  exact Fin.elim0 i

@[simp] theorem translateScalarSchwartzTestFunction_zero
    (d : EuclideanDimension) {n : ℕ} (a : d.Spacetime) :
    translateScalarSchwartzTestFunction d a (0 : ScalarSchwartzTestFunction d n) = 0 := by
  ext x
  simp

/-- Translation preserves and reflects vanishing. -/
@[simp] theorem translateScalarSchwartzTestFunction_eq_zero_iff
    (d : EuclideanDimension) {n : ℕ} (a : d.Spacetime)
    (f : ScalarSchwartzTestFunction d n) :
    translateScalarSchwartzTestFunction d a f = 0 ↔ f = 0 := by
  constructor
  · intro h
    have h' := congrArg (translateScalarSchwartzTestFunction d (-a)) h
    rw [translateScalarSchwartzTestFunction_inverse,
      translateScalarSchwartzTestFunction_zero] at h'
    exact h'
  · rintro rfl
    exact translateScalarSchwartzTestFunction_zero d a

/-- Componentwise simultaneous translation of an unrestricted finite sequence. Exact support is
preserved rather than replaced by an arbitrary finite superset. -/
noncomputable def translateScalarFiniteSchwartzSequence
    (d : EuclideanDimension) (a : d.Spacetime)
    (f : ScalarFiniteSchwartzSequence d) : ScalarFiniteSchwartzSequence d where
  support := f.support
  component n := translateScalarSchwartzTestFunction d a (f.component n)
  mem_support_iff n := by
    rw [f.mem_support_iff]
    exact not_congr
      (translateScalarSchwartzTestFunction_eq_zero_iff d a (f.component n)).symm

@[simp] theorem translateScalarFiniteSchwartzSequence_support
    (d : EuclideanDimension) (a : d.Spacetime)
    (f : ScalarFiniteSchwartzSequence d) :
    (translateScalarFiniteSchwartzSequence d a f).support = f.support :=
  rfl

@[simp] theorem translateScalarFiniteSchwartzSequence_component
    (d : EuclideanDimension) (a : d.Spacetime)
    (f : ScalarFiniteSchwartzSequence d) (n : ℕ) :
    (translateScalarFiniteSchwartzSequence d a f).component n =
      translateScalarSchwartzTestFunction d a (f.component n) :=
  rfl

/-- Sequence translation is inverted by the opposite displacement. -/
theorem translateScalarFiniteSchwartzSequence_inverse
    (d : EuclideanDimension) (a : d.Spacetime)
    (f : ScalarFiniteSchwartzSequence d) :
    translateScalarFiniteSchwartzSequence d (-a)
      (translateScalarFiniteSchwartzSequence d a f) = f := by
  apply ScalarFiniteSchwartzSequence.ext
  intro n
  exact translateScalarSchwartzTestFunction_inverse d a (f.component n)

/-- Sequence translations compose without changing arity or support. -/
theorem translateScalarFiniteSchwartzSequence_comp
    (d : EuclideanDimension) (a b : d.Spacetime)
    (f : ScalarFiniteSchwartzSequence d) :
    translateScalarFiniteSchwartzSequence d b
        (translateScalarFiniteSchwartzSequence d a f) =
      translateScalarFiniteSchwartzSequence d (b + a) f := by
  apply ScalarFiniteSchwartzSequence.ext
  intro n
  exact translateScalarSchwartzTestFunction_comp d a b (f.component n)

end YangMills
