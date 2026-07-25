/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Euclidean.SchwingerSymmetry

/-!
# Reverse-conjugate involution on scalar Schwinger tests

Osterwalder–Schrader I defines
`fₙ*(x₁,…,xₙ) = overline{fₙ(xₙ,…,x₁)}`. This module constructs complex conjugation as real-linear
postcomposition on Mathlib Schwartz space, composes it with exact argument reversal, and proves the
resulting operation involutive and conjugate-linear.

This is the sequence-star ingredient only. Euclidean time reflection `Θ` remains a separate
operation, as required by `(E2)`.
-/

namespace YangMills

/-- Pointwise complex conjugation as a continuous real-linear operation on scalar Schwartz tests. -/
noncomputable def conjugateScalarSchwartz
    {d : EuclideanDimension} {n : ℕ} :
    ScalarSchwartzTestFunction d n →L[ℝ] ScalarSchwartzTestFunction d n :=
  SchwartzMap.postcompCLM Complex.conjCLE

@[simp] theorem conjugateScalarSchwartz_apply
    {d : EuclideanDimension} {n : ℕ} (f : ScalarSchwartzTestFunction d n)
    (x : EuclideanNPointSpace d n) :
    conjugateScalarSchwartz f x = star (f x) :=
  rfl

/-- Reverse point arguments and then complex-conjugate the scalar value. -/
noncomputable def reverseConjugateScalarSchwartz
    (d : EuclideanDimension) {n : ℕ} (f : ScalarSchwartzTestFunction d n) :
    ScalarSchwartzTestFunction d n :=
  conjugateScalarSchwartz (permuteScalarSchwartzTestFunction d Fin.revPerm f)

/-- Exact pointwise formula for the reverse-conjugate operation. -/
@[simp] theorem reverseConjugateScalarSchwartz_apply
    (d : EuclideanDimension) {n : ℕ} (f : ScalarSchwartzTestFunction d n)
    (x : EuclideanNPointSpace d n) :
    reverseConjugateScalarSchwartz d f x =
      star (f (fun i => x (Fin.rev i))) := by
  simp only [reverseConjugateScalarSchwartz, conjugateScalarSchwartz_apply,
    permuteScalarSchwartzTestFunction_apply]
  congr 2
  funext i
  change (Equiv.piCongrLeft (fun _ : Fin n => d.Spacetime) Fin.revPerm) x i = x (Fin.rev i)
  rw [Equiv.piCongrLeft_apply]
  simp [Fin.revPerm_symm, Fin.revPerm_apply]

/-- Reverse-conjugation is involutive on the exact Schwartz carrier. -/
theorem reverseConjugateScalarSchwartz_involutive
    (d : EuclideanDimension) {n : ℕ} (f : ScalarSchwartzTestFunction d n) :
    reverseConjugateScalarSchwartz d (reverseConjugateScalarSchwartz d f) = f := by
  ext x
  simp only [reverseConjugateScalarSchwartz_apply, star_star]
  apply congrArg f
  funext i
  simp

/-- Reverse-conjugation is additive. -/
@[simp] theorem reverseConjugateScalarSchwartz_add
    (d : EuclideanDimension) {n : ℕ}
    (f g : ScalarSchwartzTestFunction d n) :
    reverseConjugateScalarSchwartz d (f + g) =
      reverseConjugateScalarSchwartz d f + reverseConjugateScalarSchwartz d g := by
  ext x
  simp

/-- Reverse-conjugation conjugates complex scalars. -/
@[simp] theorem reverseConjugateScalarSchwartz_smul
    (d : EuclideanDimension) {n : ℕ} (c : ℂ)
    (f : ScalarSchwartzTestFunction d n) :
    reverseConjugateScalarSchwartz d (c • f) =
      star c • reverseConjugateScalarSchwartz d f := by
  ext x
  simp [smul_eq_mul]

@[simp] theorem reverseConjugateScalarSchwartz_zero
    (d : EuclideanDimension) {n : ℕ} :
    reverseConjugateScalarSchwartz d (0 : ScalarSchwartzTestFunction d n) = 0 := by
  ext x
  simp

/-- Reverse-conjugation preserves and reflects nonvanishing. -/
@[simp] theorem reverseConjugateScalarSchwartz_eq_zero_iff
    (d : EuclideanDimension) {n : ℕ} (f : ScalarSchwartzTestFunction d n) :
    reverseConjugateScalarSchwartz d f = 0 ↔ f = 0 := by
  constructor
  · intro h
    have h' := congrArg (reverseConjugateScalarSchwartz d) h
    rw [reverseConjugateScalarSchwartz_involutive,
      reverseConjugateScalarSchwartz_zero] at h'
    exact h'
  · rintro rfl
    exact reverseConjugateScalarSchwartz_zero d

end YangMills
