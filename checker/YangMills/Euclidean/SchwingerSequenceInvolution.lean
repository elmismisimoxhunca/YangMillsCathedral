/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Euclidean.SchwingerFiniteSequence
import YangMills.Euclidean.SchwingerSchwartzInvolution
import YangMills.Euclidean.SchwingerTimeReflection

/-!
# Involutions on finite scalar Schwinger sequences

This module lifts the reverse-conjugate star and Euclidean time reflection componentwise to the
unrestricted finite sequence carrier. Exact support is preserved because both component operations
are involutive and reflect zero. Their composition is the `Θ f*` operation appearing in
Osterwalder–Schrader reflection positivity.

The combined operation is defined here, but no positivity inequality `(E2)` is asserted.
-/

namespace YangMills

/-- Two unrestricted finite sequences are equal when all exact dependent components are equal.
Their exact-support fields then force the support finsets to agree. -/
@[ext] theorem ScalarFiniteSchwartzSequence.ext
    {d : EuclideanDimension} {f g : ScalarFiniteSchwartzSequence d}
    (h : ∀ n, f.component n = g.component n) : f = g := by
  have hs : f.support = g.support := by
    ext n
    rw [f.mem_support_iff, g.mem_support_iff, h n]
  cases f with
  | mk fs fc fh =>
    cases g with
    | mk gs gc gh =>
      simp only at hs h
      subst gs
      have hc : fc = gc := funext h
      subst gc
      rfl

/-- Componentwise reverse-conjugate star on an unrestricted finite sequence. -/
noncomputable def finiteSchwartzSequenceStar
    (d : EuclideanDimension) (f : ScalarFiniteSchwartzSequence d) :
    ScalarFiniteSchwartzSequence d where
  support := f.support
  component n := reverseConjugateScalarSchwartz d (f.component n)
  mem_support_iff n := by
    rw [f.mem_support_iff]
    exact not_congr
      (reverseConjugateScalarSchwartz_eq_zero_iff d (f.component n)).symm

/-- Sequence star preserves exact support definitionally. -/
@[simp] theorem finiteSchwartzSequenceStar_support
    (d : EuclideanDimension) (f : ScalarFiniteSchwartzSequence d) :
    (finiteSchwartzSequenceStar d f).support = f.support :=
  rfl

/-- Sequence star has the exact reverse-conjugate component. -/
@[simp] theorem finiteSchwartzSequenceStar_component
    (d : EuclideanDimension) (f : ScalarFiniteSchwartzSequence d) (n : ℕ) :
    (finiteSchwartzSequenceStar d f).component n =
      reverseConjugateScalarSchwartz d (f.component n) :=
  rfl

/-- Componentwise sequence star is involutive. -/
theorem finiteSchwartzSequenceStar_involutive
    (d : EuclideanDimension) (f : ScalarFiniteSchwartzSequence d) :
    finiteSchwartzSequenceStar d (finiteSchwartzSequenceStar d f) = f := by
  apply ScalarFiniteSchwartzSequence.ext
  intro n
  exact reverseConjugateScalarSchwartz_involutive d (f.component n)

/-- Time reflection sends the zero Schwartz test to zero. -/
@[simp] theorem reflectScalarSchwartzTestFunction_zero
    (d : EuclideanDimension) {n : ℕ} :
    reflectScalarSchwartzTestFunction d (0 : ScalarSchwartzTestFunction d n) = 0 := by
  ext x
  simp

/-- Time reflection preserves and reflects vanishing. -/
@[simp] theorem reflectScalarSchwartzTestFunction_eq_zero_iff
    (d : EuclideanDimension) {n : ℕ} (f : ScalarSchwartzTestFunction d n) :
    reflectScalarSchwartzTestFunction d f = 0 ↔ f = 0 := by
  constructor
  · intro h
    have h' := congrArg (reflectScalarSchwartzTestFunction d) h
    rw [reflectScalarSchwartzTestFunction_involutive,
      reflectScalarSchwartzTestFunction_zero] at h'
    exact h'
  · rintro rfl
    exact reflectScalarSchwartzTestFunction_zero d

/-- Componentwise Euclidean time reflection on an unrestricted finite sequence. -/
noncomputable def finiteSchwartzSequenceTimeReflection
    (d : EuclideanDimension) (f : ScalarFiniteSchwartzSequence d) :
    ScalarFiniteSchwartzSequence d where
  support := f.support
  component n := reflectScalarSchwartzTestFunction d (f.component n)
  mem_support_iff n := by
    rw [f.mem_support_iff]
    exact not_congr
      (reflectScalarSchwartzTestFunction_eq_zero_iff d (f.component n)).symm

@[simp] theorem finiteSchwartzSequenceTimeReflection_support
    (d : EuclideanDimension) (f : ScalarFiniteSchwartzSequence d) :
    (finiteSchwartzSequenceTimeReflection d f).support = f.support :=
  rfl

@[simp] theorem finiteSchwartzSequenceTimeReflection_component
    (d : EuclideanDimension) (f : ScalarFiniteSchwartzSequence d) (n : ℕ) :
    (finiteSchwartzSequenceTimeReflection d f).component n =
      reflectScalarSchwartzTestFunction d (f.component n) :=
  rfl

/-- Componentwise Euclidean time reflection is involutive. -/
theorem finiteSchwartzSequenceTimeReflection_involutive
    (d : EuclideanDimension) (f : ScalarFiniteSchwartzSequence d) :
    finiteSchwartzSequenceTimeReflection d
      (finiteSchwartzSequenceTimeReflection d f) = f := by
  apply ScalarFiniteSchwartzSequence.ext
  intro n
  exact reflectScalarSchwartzTestFunction_involutive d (f.component n)

/-- Time reflection commutes with reverse-conjugation on each exact scalar component. -/
theorem reflect_reverseConjugate_commute
    (d : EuclideanDimension) {n : ℕ} (f : ScalarSchwartzTestFunction d n) :
    reflectScalarSchwartzTestFunction d (reverseConjugateScalarSchwartz d f) =
      reverseConjugateScalarSchwartz d (reflectScalarSchwartzTestFunction d f) := by
  ext x
  simp only [reflectScalarSchwartzTestFunction_apply,
    reverseConjugateScalarSchwartz_apply]

/-- The exact finite-sequence operation `Θ f*`: star first, then Euclidean time reflection. -/
noncomputable def finiteSchwartzSequenceReflectedStar
    (d : EuclideanDimension) (f : ScalarFiniteSchwartzSequence d) :
    ScalarFiniteSchwartzSequence d :=
  finiteSchwartzSequenceTimeReflection d (finiteSchwartzSequenceStar d f)

@[simp] theorem finiteSchwartzSequenceReflectedStar_support
    (d : EuclideanDimension) (f : ScalarFiniteSchwartzSequence d) :
    (finiteSchwartzSequenceReflectedStar d f).support = f.support :=
  rfl

/-- The combined reflected-star operation is itself involutive. -/
theorem finiteSchwartzSequenceReflectedStar_involutive
    (d : EuclideanDimension) (f : ScalarFiniteSchwartzSequence d) :
    finiteSchwartzSequenceReflectedStar d
      (finiteSchwartzSequenceReflectedStar d f) = f := by
  apply ScalarFiniteSchwartzSequence.ext
  intro n
  change reflectScalarSchwartzTestFunction d
    (reverseConjugateScalarSchwartz d
      (reflectScalarSchwartzTestFunction d
        (reverseConjugateScalarSchwartz d (f.component n)))) = f.component n
  rw [reflect_reverseConjugate_commute]
  rw [reflectScalarSchwartzTestFunction_involutive,
    reverseConjugateScalarSchwartz_involutive]

end YangMills
