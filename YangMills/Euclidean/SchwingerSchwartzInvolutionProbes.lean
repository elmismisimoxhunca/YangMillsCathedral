/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Euclidean.SchwingerSchwartzInvolution
import YangMills.Euclidean.PositiveTimeSchwartzBump

/-!
# Hostile probes for reverse-conjugate Schwinger tests

The probes expose nonidentity two-point reversal, nontrivial complex conjugation, exact
involutivity, and nonvanishing preservation. Time reflection is deliberately not conflated with this
operation.
-/

namespace YangMills.Euclidean.SchwingerSchwartzInvolution.Probes

/-- Two-point reversal exchanges point labels zero and one. -/
theorem two_point_reversal_zero
    {α : Type*} (x : Fin 2 → α) : (fun i => x (Fin.rev i)) (0 : Fin 2) = x 1 := by
  rfl

/-- Two-point reversal also sends point label one to zero. -/
theorem two_point_reversal_one
    {α : Type*} (x : Fin 2 → α) : (fun i => x (Fin.rev i)) (1 : Fin 2) = x 0 := by
  rfl

/-- Reverse-conjugation has the exact source-facing pointwise formula. -/
theorem exact_reverse_conjugate_evaluation
    (d : EuclideanDimension) {n : ℕ} (f : ScalarSchwartzTestFunction d n)
    (x : EuclideanNPointSpace d n) :
    reverseConjugateScalarSchwartz d f x =
      star (f (fun i => x (Fin.rev i))) :=
  reverseConjugateScalarSchwartz_apply d f x

/-- Conjugation is genuine: multiplying the real arity-one bump by `i` produces value `-i` after
reverse-conjugation at its center. -/
theorem imaginary_bump_reverseConjugate_at_center
    (d : EuclideanDimension) :
    reverseConjugateScalarSchwartz d (Complex.I • positiveTimeBumpSchwartz d)
        (positiveTimeBumpCenter d) = -Complex.I := by
  rw [reverseConjugateScalarSchwartz_apply]
  have hconfig :
      (fun i => positiveTimeBumpCenter d (Fin.rev i)) = positiveTimeBumpCenter d := by
    funext i
    exact congrArg (positiveTimeBumpCenter d) (Subsingleton.elim _ _)
  rw [hconfig]
  rw [smul_apply, positiveTimeBumpSchwartz_center]
  norm_num

/-- Applying the exact operation twice restores the original Schwartz test. -/
theorem exact_reverse_conjugate_involution
    (d : EuclideanDimension) {n : ℕ} (f : ScalarSchwartzTestFunction d n) :
    reverseConjugateScalarSchwartz d (reverseConjugateScalarSchwartz d f) = f :=
  reverseConjugateScalarSchwartz_involutive d f

/-- A nonzero test cannot become zero under the exact involution. -/
theorem nonzero_reverse_conjugate
    (d : EuclideanDimension) {n : ℕ} (f : ScalarSchwartzTestFunction d n)
    (hnonzero : f ≠ 0) : reverseConjugateScalarSchwartz d f ≠ 0 := by
  intro hzero
  exact hnonzero ((reverseConjugateScalarSchwartz_eq_zero_iff d f).mp hzero)

/-- Complex scalar compatibility is conjugate-linear, not complex-linear. -/
theorem exact_reverse_conjugate_smul
    (d : EuclideanDimension) {n : ℕ} (c : ℂ)
    (f : ScalarSchwartzTestFunction d n) :
    reverseConjugateScalarSchwartz d (c • f) =
      star c • reverseConjugateScalarSchwartz d f :=
  reverseConjugateScalarSchwartz_smul d c f

end YangMills.Euclidean.SchwingerSchwartzInvolution.Probes
