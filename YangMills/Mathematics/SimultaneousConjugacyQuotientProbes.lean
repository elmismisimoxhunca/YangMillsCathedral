/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Mathematics.SimultaneousConjugacyQuotient

/-!
# Hostile probes for simultaneous conjugacy quotients
-/

namespace YangMills.Mathematics.SimultaneousConjugacyQuotient.Probes

universe uIndex uG

/-- Equality requires one common conjugator for every coordinate, not a coordinate-dependent family. -/
theorem exact_common_conjugator
    {Index : Type uIndex} {G : Type uG} [Group G]
    (family₁ family₂ : Index → G) :
    simultaneousConjugacyClass family₁ = simultaneousConjugacyClass family₂ ↔
      ∃ conjugator : G, ∀ index,
        family₂ index = conjugator⁻¹ * family₁ index * conjugator :=
  simultaneousConjugacyClass_eq_iff family₁ family₂

/-- A common diagonal conjugation preserves the exact family class. -/
theorem exact_diagonal_invariance
    {Index : Type uIndex} {G : Type uG} [Group G]
    (family : Index → G) (conjugator : G) :
    simultaneousConjugacyClass
        (fun index => conjugator⁻¹ * family index * conjugator) =
      simultaneousConjugacyClass family :=
  simultaneousConjugacyClass_conjugate family conjugator

/-- The quotient projection is measurable for its exact final measurable space. -/
theorem exact_projection_measurable
    {Index : Type uIndex} {G : Type uG} [Group G] [MeasurableSpace G] :
    Measurable (simultaneousConjugacyClass :
      (Index → G) → SimultaneousConjugacyQuotient Index G) :=
  simultaneousConjugacyClass_measurable

/-- Coordinatewise conjugacy does not imply simultaneous conjugacy. Any supplied family pair with
coordinatewise witnesses but no common witness has distinct simultaneous classes, even though every
one-coordinate class agrees. -/
theorem coordinatewise_substitution_blocked
    {Index : Type uIndex} {G : Type uG} [Group G]
    (family₁ family₂ : Index → G)
    (coordinatewise : ∀ index, ∃ conjugator : G,
      family₂ index = conjugator⁻¹ * family₁ index * conjugator)
    (noCommon : ¬ ∃ conjugator : G, ∀ index,
      family₂ index = conjugator⁻¹ * family₁ index * conjugator) :
    simultaneousConjugacyClass family₁ ≠ simultaneousConjugacyClass family₂ ∧
      ∀ index,
        simultaneousConjugacyClass (fun _ : Unit => family₁ index) =
          simultaneousConjugacyClass (fun _ : Unit => family₂ index) := by
  constructor
  · intro equality
    exact noCommon ((simultaneousConjugacyClass_eq_iff family₁ family₂).mp equality)
  · intro index
    obtain ⟨conjugator, equality⟩ := coordinatewise index
    apply Quotient.sound
    exact ⟨conjugator, fun _ => equality⟩

/-- An empty family has no holonomy information and its simultaneous quotient is subsingleton. A
source-facing finite-family observation layer must separately prevent empty-family vacuity where the
source requires a genuine loop observation. -/
theorem empty_index_quotient_subsingleton
    (G : Type uG) [Group G] :
    Subsingleton (SimultaneousConjugacyQuotient Empty G) := by
  constructor
  intro first second
  refine Quotient.inductionOn₂ first second ?_
  intro family₁ family₂
  apply Quotient.sound
  refine ⟨1, ?_⟩
  intro index
  exact index.elim

end YangMills.Mathematics.SimultaneousConjugacyQuotient.Probes
