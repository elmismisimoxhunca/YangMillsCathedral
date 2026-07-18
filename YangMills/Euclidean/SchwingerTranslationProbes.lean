/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Euclidean.SchwingerTranslation
import YangMills.Euclidean.PositiveTimeSchwartzBump
import YangMills.Euclidean.SchwingerFiniteSequenceProbes

/-!
# Hostile probes for scalar Schwinger translations

The probes expose the exact `x + a` convention, a genuinely wired nonzero bump translation,
invertibility, zero-arity stability, and preservation of exact finite support.
-/

namespace YangMills.Euclidean.SchwingerTranslation.Probes

/-- The translation convention is exactly simultaneous addition of the named displacement. -/
theorem exact_translation_evaluation
    (d : EuclideanDimension) {n : ℕ} (a : d.Spacetime)
    (f : ScalarSchwartzTestFunction d n) (x : EuclideanNPointSpace d n) :
    translateScalarSchwartzTestFunction d a f x = f (fun i => x i + a) :=
  translateScalarSchwartzTestFunction_apply d a f x

/-- Translating the positive-time bump by its center makes its value at the zero configuration
exactly one, preventing an ignored displacement parameter. -/
theorem translated_bump_at_zero
    (d : EuclideanDimension) :
    translateScalarSchwartzTestFunction d (positiveTimeBumpCenter d 0)
        (positiveTimeBumpSchwartz d) (fun _ => 0) = 1 := by
  rw [translateScalarSchwartzTestFunction_apply]
  have hconfig :
      (fun i : Fin 1 => (0 : d.Spacetime) + positiveTimeBumpCenter d 0) =
        positiveTimeBumpCenter d := by
    funext i
    rw [zero_add]
    exact congrArg (positiveTimeBumpCenter d) (Subsingleton.elim _ _)
  rw [hconfig]
  exact positiveTimeBumpSchwartz_center d

/-- The explicitly translated bump remains nonzero. -/
theorem translated_bump_ne_zero
    (d : EuclideanDimension) :
    translateScalarSchwartzTestFunction d (positiveTimeBumpCenter d 0)
      (positiveTimeBumpSchwartz d) ≠ 0 := by
  intro hzero
  have atZero := congrArg
    (fun f : ScalarSchwartzTestFunction d 1 => f (fun _ => 0)) hzero
  rw [translated_bump_at_zero] at atZero
  simp at atZero

/-- Translation followed by the opposite displacement restores every exact test. -/
theorem exact_translation_inverse
    (d : EuclideanDimension) {n : ℕ} (a : d.Spacetime)
    (f : ScalarSchwartzTestFunction d n) :
    translateScalarSchwartzTestFunction d (-a)
      (translateScalarSchwartzTestFunction d a f) = f :=
  translateScalarSchwartzTestFunction_inverse d a f

/-- Every zero-arity test is fixed by every displacement. -/
theorem zero_arity_translation_is_identity
    (d : EuclideanDimension) (a : d.Spacetime)
    (f : ScalarSchwartzTestFunction d 0) :
    translateScalarSchwartzTestFunction d a f = f :=
  translateScalarSchwartzTestFunction_zero_arity d a f

/-- Componentwise sequence translation preserves exact support definitionally. -/
theorem sequence_translation_exact_support
    (d : EuclideanDimension) (a : d.Spacetime)
    (f : ScalarFiniteSchwartzSequence d) :
    (translateScalarFiniteSchwartzSequence d a f).support = f.support :=
  rfl

/-- The singleton bump's arity-one support survives arbitrary simultaneous translation. -/
theorem translated_singleton_bump_one_mem_support
    (d : EuclideanDimension) (a : d.Spacetime) :
    1 ∈ (translateScalarFiniteSchwartzSequence d a
      (singletonPositiveTimeBumpSequence d).toFiniteSchwartzSequence).support := by
  rw [translateScalarFiniteSchwartzSequence_support]
  rw [_root_.YangMills.Euclidean.SchwingerFiniteSequence.Probes.forgotten_singleton_bump_support]
  simp

/-- Omitting the translated bump's exact arity-one support is impossible. -/
theorem omitted_translated_bump_support_blocked
    (d : EuclideanDimension) (a : d.Spacetime)
    (homitted : 1 ∉ (translateScalarFiniteSchwartzSequence d a
      (singletonPositiveTimeBumpSequence d).toFiniteSchwartzSequence).support) : False :=
  homitted (translated_singleton_bump_one_mem_support d a)

/-- Opposite sequence translation restores every exact component and support. -/
theorem exact_sequence_translation_inverse
    (d : EuclideanDimension) (a : d.Spacetime)
    (f : ScalarFiniteSchwartzSequence d) :
    translateScalarFiniteSchwartzSequence d (-a)
      (translateScalarFiniteSchwartzSequence d a f) = f :=
  translateScalarFiniteSchwartzSequence_inverse d a f

end YangMills.Euclidean.SchwingerTranslation.Probes
