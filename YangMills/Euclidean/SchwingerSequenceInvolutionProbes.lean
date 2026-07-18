/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Euclidean.SchwingerSequenceInvolution
import YangMills.Euclidean.SchwingerSchwartzInvolutionProbes
import YangMills.Euclidean.SchwingerFiniteSequenceProbes

/-!
# Hostile probes for finite-sequence involutions

The probes ensure exact support and component wiring survive star, time reflection, and their
ordered composition `Θ f*`. No positivity inequality is asserted.
-/

namespace YangMills.Euclidean.SchwingerSequenceInvolution.Probes

/-- Sequence star cannot change or disconnect exact finite support. -/
theorem star_exact_support
    (d : EuclideanDimension) (f : ScalarFiniteSchwartzSequence d) :
    (finiteSchwartzSequenceStar d f).support = f.support :=
  finiteSchwartzSequenceStar_support d f

/-- Sequence star acts by the exact reverse-conjugate operation on the same arity component. -/
theorem star_exact_component
    (d : EuclideanDimension) (f : ScalarFiniteSchwartzSequence d) (n : ℕ) :
    (finiteSchwartzSequenceStar d f).component n =
      reverseConjugateScalarSchwartz d (f.component n) :=
  rfl

/-- Sequence star is genuinely involutive. -/
theorem star_exact_involution
    (d : EuclideanDimension) (f : ScalarFiniteSchwartzSequence d) :
    finiteSchwartzSequenceStar d (finiteSchwartzSequenceStar d f) = f :=
  finiteSchwartzSequenceStar_involutive d f

/-- Time reflection preserves the same exact support rather than introducing a disconnected one. -/
theorem timeReflection_exact_support
    (d : EuclideanDimension) (f : ScalarFiniteSchwartzSequence d) :
    (finiteSchwartzSequenceTimeReflection d f).support = f.support :=
  rfl

/-- Time reflection acts on the exact same arity component. -/
theorem timeReflection_exact_component
    (d : EuclideanDimension) (f : ScalarFiniteSchwartzSequence d) (n : ℕ) :
    (finiteSchwartzSequenceTimeReflection d f).component n =
      reflectScalarSchwartzTestFunction d (f.component n) :=
  rfl

/-- Time reflection is genuinely involutive on the finite sequence carrier. -/
theorem timeReflection_exact_involution
    (d : EuclideanDimension) (f : ScalarFiniteSchwartzSequence d) :
    finiteSchwartzSequenceTimeReflection d
      (finiteSchwartzSequenceTimeReflection d f) = f :=
  finiteSchwartzSequenceTimeReflection_involutive d f

/-- The component time-reflection operation reflects zero exactly. -/
theorem timeReflection_exact_zero_iff
    (d : EuclideanDimension) {n : ℕ} (f : ScalarSchwartzTestFunction d n) :
    reflectScalarSchwartzTestFunction d f = 0 ↔ f = 0 :=
  reflectScalarSchwartzTestFunction_eq_zero_iff d f

/-- Time reflection commutes with the exact reverse-conjugate operation. -/
theorem timeReflection_reverseConjugate_commute
    (d : EuclideanDimension) {n : ℕ} (f : ScalarSchwartzTestFunction d n) :
    reflectScalarSchwartzTestFunction d (reverseConjugateScalarSchwartz d f) =
      reverseConjugateScalarSchwartz d (reflectScalarSchwartzTestFunction d f) :=
  reflect_reverseConjugate_commute d f

/-- The combined operation has the exact order `Θ` after reverse-conjugate star. -/
theorem reflectedStar_exact_component
    (d : EuclideanDimension) (f : ScalarFiniteSchwartzSequence d) (n : ℕ) :
    (finiteSchwartzSequenceReflectedStar d f).component n =
      reflectScalarSchwartzTestFunction d
        (reverseConjugateScalarSchwartz d (f.component n)) :=
  rfl

/-- The combined reflected-star operation is involutive. -/
theorem reflectedStar_exact_involution
    (d : EuclideanDimension) (f : ScalarFiniteSchwartzSequence d) :
    finiteSchwartzSequenceReflectedStar d
      (finiteSchwartzSequenceReflectedStar d f) = f :=
  finiteSchwartzSequenceReflectedStar_involutive d f

/-- The nonzero singleton bump remains at arity one after reverse-conjugate star. -/
theorem starred_singleton_bump_one_mem_support
    (d : EuclideanDimension) :
    1 ∈ (finiteSchwartzSequenceStar d
      (singletonPositiveTimeBumpSequence d).toFiniteSchwartzSequence).support := by
  rw [finiteSchwartzSequenceStar_support]
  rw [_root_.YangMills.Euclidean.SchwingerFiniteSequence.Probes.forgotten_singleton_bump_support]
  simp

/-- Omitting the arity-one component after combined reflection and star contradicts exact support. -/
theorem reflectedStar_omitted_bump_support_blocked
    (d : EuclideanDimension)
    (homitted : 1 ∉ (finiteSchwartzSequenceReflectedStar d
      (singletonPositiveTimeBumpSequence d).toFiniteSchwartzSequence).support) : False := by
  rw [finiteSchwartzSequenceReflectedStar_support] at homitted
  exact _root_.YangMills.Euclidean.SchwingerFiniteSequence.Probes.omitted_forgotten_bump_support_blocked d homitted

end YangMills.Euclidean.SchwingerSequenceInvolution.Probes
