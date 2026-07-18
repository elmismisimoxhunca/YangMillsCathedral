/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Euclidean.SchwingerRegularity

/-!
# Euclidean time reflection and positive-time test support

Osterwalder–Schrader I, printed pp. 86–88, selects the first Euclidean coordinate as time, defines
time reflection `θ`, positive-time Schwartz test spaces, and then states reflection positivity
`(E2)`. This module constructs only the geometric reflection, its exact Schwartz pullback, and the
strict positive-time support predicate. It does not state `(E2)`.

The nonzero positive-time test-function existence theorem, the bridge to OS-I's time-ordered and
diagonal-flat source spaces, and the finite test-sequence product needed by `(E2)` remain separate
infrastructure obligations. Keeping them absent prevents a vacuous or carrier-weakened positivity
record whose source-facing test domain has not been constructed and shown nontrivial.
-/

open scoped SchwartzMap

namespace YangMills

/-- The selected first Euclidean coordinate, interpreted as Euclidean time. -/
def euclideanTimeCoordinate (d : EuclideanDimension) : d.CoordinateIndex :=
  ⟨0, d.one_le⟩

/-- Reflection of the selected Euclidean time coordinate, fixing every spatial coordinate. -/
noncomputable def euclideanTimeReflection (d : EuclideanDimension) :
    d.Spacetime ≃ₗᵢ[ℝ] d.Spacetime :=
  LinearIsometryEquiv.piLpCongrRight 2 (fun i : d.CoordinateIndex =>
    if i = euclideanTimeCoordinate d then LinearIsometryEquiv.neg ℝ
    else LinearIsometryEquiv.refl ℝ ℝ)

/-- Euclidean time reflection negates the selected time coordinate. -/
@[simp] theorem euclideanTimeReflection_time
    (d : EuclideanDimension) (x : d.Spacetime) :
    euclideanTimeReflection d x (euclideanTimeCoordinate d) =
      -x (euclideanTimeCoordinate d) := by
  simp [euclideanTimeReflection]

/-- Euclidean time reflection fixes every coordinate distinct from the selected time coordinate. -/
theorem euclideanTimeReflection_space
    (d : EuclideanDimension) (x : d.Spacetime) (i : d.CoordinateIndex)
    (hi : i ≠ euclideanTimeCoordinate d) :
    euclideanTimeReflection d x i = x i := by
  simp [euclideanTimeReflection, hi]

/-- Euclidean time reflection is pointwise involutive. -/
theorem euclideanTimeReflection_involutive
    (d : EuclideanDimension) (x : d.Spacetime) :
    euclideanTimeReflection d (euclideanTimeReflection d x) = x := by
  ext i
  by_cases hi : i = euclideanTimeCoordinate d
  · subst i
    simp
  · rw [euclideanTimeReflection_space d _ i hi, euclideanTimeReflection_space d _ i hi]

/-- Simultaneous Euclidean time reflection on an exact `n`-point configuration space. -/
noncomputable def euclideanNPointTimeReflection
    (d : EuclideanDimension) {n : ℕ} :
    EuclideanNPointSpace d n ≃L[ℝ] EuclideanNPointSpace d n :=
  ContinuousLinearEquiv.piCongrRight
    (fun _ : Fin n => (euclideanTimeReflection d).toContinuousLinearEquiv)

/-- Pullback of scalar Schwartz tests by simultaneous Euclidean time reflection. -/
noncomputable def reflectScalarSchwartzTestFunction
    (d : EuclideanDimension) {n : ℕ} :
    ScalarSchwartzTestFunction d n →L[ℂ] ScalarSchwartzTestFunction d n :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (euclideanNPointTimeReflection d)

/-- The Schwartz reflection pullback evaluates at the reflected exact point configuration. -/
@[simp] theorem reflectScalarSchwartzTestFunction_apply
    (d : EuclideanDimension) {n : ℕ} (f : ScalarSchwartzTestFunction d n)
    (x : EuclideanNPointSpace d n) :
    reflectScalarSchwartzTestFunction d f x =
      f (fun i => euclideanTimeReflection d (x i)) := by
  simp only [reflectScalarSchwartzTestFunction,
    SchwartzMap.compCLMOfContinuousLinearEquiv_apply]
  apply congrArg f
  funext i
  simp [euclideanNPointTimeReflection]

/-- Reflection pullback on scalar Schwartz tests is involutive. -/
theorem reflectScalarSchwartzTestFunction_involutive
    (d : EuclideanDimension) {n : ℕ} (f : ScalarSchwartzTestFunction d n) :
    reflectScalarSchwartzTestFunction d (reflectScalarSchwartzTestFunction d f) = f := by
  ext x
  simp only [reflectScalarSchwartzTestFunction_apply]
  apply congrArg f
  funext i
  exact euclideanTimeReflection_involutive d (x i)

/-- Exact configurations whose every point has strictly positive selected Euclidean time. -/
def strictPositiveTimeConfigurationSet
    (d : EuclideanDimension) (n : ℕ) : Set (EuclideanNPointSpace d n) :=
  {x | ∀ i, 0 < x i (euclideanTimeCoordinate d)}

/-- A scalar Schwartz test has strict positive-time support when its topological support is contained
in the exact positive-time configuration set. -/
def HasStrictPositiveTimeSupport
    (d : EuclideanDimension) {n : ℕ} (f : ScalarSchwartzTestFunction d n) : Prop :=
  tsupport f ⊆ strictPositiveTimeConfigurationSet d n

/-- The scalar strict-positive-time Schwartz test subtype at exact arity `n`.

No nonzero inhabitant is asserted in this module, and this subtype does not yet encode OS-I's
additional time-ordering or diagonal-flat conditions. -/
abbrev ScalarPositiveTimeSchwartzTestFunction
    (d : EuclideanDimension) (n : ℕ) :=
  {f : ScalarSchwartzTestFunction d n // HasStrictPositiveTimeSupport d f}

end YangMills
