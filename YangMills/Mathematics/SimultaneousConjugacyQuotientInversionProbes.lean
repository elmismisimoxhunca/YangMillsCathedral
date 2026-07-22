/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Mathematics.SimultaneousConjugacyQuotientInversion

/-!
# Probes for inversion on simultaneous-conjugacy quotients
-/

namespace YangMills.Mathematics.SimultaneousConjugacyQuotientInversion.Probes

universe uIndex uG

/-- Inversion acts on every coordinate of the same exact representative family. -/
theorem exact_class_inverse {Index : Type uIndex} {G : Type uG} [Group G]
    (family : Index → G) :
    simultaneousConjugacyInverse (simultaneousConjugacyClass family) =
      simultaneousConjugacyClass (fun index => (family index)⁻¹) :=
  simultaneousConjugacyInverse_class family

/-- Boundary-orientation reversal is an involution and hence cannot collapse distinct classes. -/
theorem exact_inverse_involutive_bijective
    {Index : Type uIndex} {G : Type uG} [Group G] :
    Function.Involutive
        (simultaneousConjugacyInverse : SimultaneousConjugacyQuotient Index G →
          SimultaneousConjugacyQuotient Index G) ∧
      Function.Bijective
        (simultaneousConjugacyInverse : SimultaneousConjugacyQuotient Index G →
          SimultaneousConjugacyQuotient Index G) :=
  ⟨simultaneousConjugacyInverse_involutive,
    simultaneousConjugacyInverse_bijective⟩

/-- The descended inverse is continuous for the genuine quotient topology. -/
theorem exact_inverse_continuous
    {Index : Type uIndex} {G : Type uG} [TopologicalSpace G]
    [Group G] [ContinuousInv G] :
    Continuous
      (simultaneousConjugacyInverse : SimultaneousConjugacyQuotient Index G →
        SimultaneousConjugacyQuotient Index G) :=
  simultaneousConjugacyInverse_continuous

/-- The descended inverse is measurable for the final quotient sigma field without requiring a
Borel-topology comparison. -/
theorem exact_inverse_measurable
    {Index : Type uIndex} {G : Type uG} [Group G] [MeasurableSpace G]
    [MeasurableInv G] :
    Measurable
      (simultaneousConjugacyInverse : SimultaneousConjugacyQuotient Index G →
        SimultaneousConjugacyQuotient Index G) :=
  simultaneousConjugacyInverse_measurable

/-- Inverting after one common conjugation gives the unchanged inverse class, so reversal does not
silently switch to coordinatewise unrelated conjugators. -/
theorem exact_inverse_common_conjugation
    {Index : Type uIndex} {G : Type uG} [Group G]
    (family : Index → G) (conjugator : G) :
    simultaneousConjugacyInverse
        (simultaneousConjugacyClass
          (fun index => conjugator⁻¹ * family index * conjugator)) =
      simultaneousConjugacyInverse (simultaneousConjugacyClass family) := by
  rw [simultaneousConjugacyClass_conjugate]

end YangMills.Mathematics.SimultaneousConjugacyQuotientInversion.Probes
