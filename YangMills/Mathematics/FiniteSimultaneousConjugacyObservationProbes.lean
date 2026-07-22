/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Mathematics.FiniteSimultaneousConjugacyObservation

/-!
# Hostile probes for finite simultaneous-conjugacy observations
-/

namespace YangMills.Mathematics.FiniteSimultaneousConjugacyObservation.Probes

universe uBasedLoop uG uΩ

/-- Every admitted family has strictly positive cardinality. -/
theorem exact_family_card_positive
    {BasedLoop : Type uBasedLoop} (family : NonemptyFiniteFamily BasedLoop) :
    0 < family.card := by
  simp [NonemptyFiniteFamily.card]

/-- The singleton constructor has one exact entry. -/
theorem exact_singleton_first {BasedLoop : Type uBasedLoop} (basedLoop : BasedLoop) :
    (singletonNonemptyFiniteFamily basedLoop).first = basedLoop :=
  rfl

/-- Nonempty finite-family observations exist exactly when the underlying fixed-base loop carrier is nonempty. -/
theorem exact_family_nonempty_iff {BasedLoop : Type uBasedLoop} :
    Nonempty (NonemptyFiniteFamily BasedLoop) ↔ Nonempty BasedLoop :=
  nonempty_nonemptyFiniteFamily_iff

/-- An empty fixed-base loop carrier cannot supply even an empty-tuple surrogate, because tuple arity is
positive by construction. -/
theorem empty_fixedBaseLoop_family_blocked : ¬ Nonempty (NonemptyFiniteFamily Empty) := by
  rw [nonempty_nonemptyFiniteFamily_iff]
  exact not_nonempty_iff.mpr inferInstance

/-- Every exact finite joint class is measurable on the sigma field it helps generate. -/
theorem exact_generated_observation_measurable
    {BasedLoop : Type uBasedLoop} {G : Type uG} {Ω : Type uΩ}
    [Group G] [MeasurableSpace G]
    (holonomy : BasedLoop → Ω → G) (family : NonemptyFiniteFamily BasedLoop) :
    @Measurable Ω (finiteSimultaneousConjugacyObservationValue (G := G) family)
      (finiteSimultaneousConjugacyGeneratedMeasurableSpace holonomy)
      inferInstance (finiteSimultaneousConjugacyObservation holonomy family) :=
  finiteSimultaneousConjugacyObservation_measurable_generated holonomy family

/-- Measurable one-loop holonomies make every nonempty finite joint observation measurable on the
same ambient sample carrier. -/
theorem exact_ambient_observation_measurable
    {BasedLoop : Type uBasedLoop} {G : Type uG} {Ω : Type uΩ}
    [Group G] [MeasurableSpace G] [MeasurableSpace Ω]
    (holonomy : BasedLoop → Ω → G) (holonomy_measurable : ∀ basedLoop, Measurable (holonomy basedLoop))
    (family : NonemptyFiniteFamily BasedLoop) :
    Measurable (finiteSimultaneousConjugacyObservation holonomy family) :=
  finiteSimultaneousConjugacyObservation_measurable holonomy holonomy_measurable family

/-- A sample-dependent common gauge conjugation leaves the entire joint class unchanged. -/
theorem exact_common_conjugation_invariance
    {BasedLoop : Type uBasedLoop} {G : Type uG} {Ω : Type uΩ} [Group G]
    (holonomy : BasedLoop → Ω → G) (conjugator : Ω → G)
    (family : NonemptyFiniteFamily BasedLoop) (sample : Ω) :
    finiteSimultaneousConjugacyObservation
        (fun basedLoop samplePoint =>
          (conjugator samplePoint)⁻¹ * holonomy basedLoop samplePoint * conjugator samplePoint)
        family sample =
      finiteSimultaneousConjugacyObservation holonomy family sample :=
  finiteSimultaneousConjugacyObservation_common_conjugation
    holonomy conjugator family sample

/-- Exact generated-field equality needs the converse coverage inclusion; measurability alone gives
only one direction. -/
theorem exact_ambient_generated_recognition
    {BasedLoop : Type uBasedLoop} {G : Type uG} {Ω : Type uΩ}
    [Group G] [MeasurableSpace G] [MeasurableSpace Ω]
    (holonomy : BasedLoop → Ω → G) (holonomy_measurable : ∀ basedLoop, Measurable (holonomy basedLoop))
    (generated_covers : (inferInstance : MeasurableSpace Ω) ≤
      finiteSimultaneousConjugacyGeneratedMeasurableSpace holonomy) :
    (inferInstance : MeasurableSpace Ω) =
      finiteSimultaneousConjugacyGeneratedMeasurableSpace holonomy :=
  ambient_eq_finiteSimultaneousConjugacyGeneratedMeasurableSpace
    holonomy holonomy_measurable generated_covers

end YangMills.Mathematics.FiniteSimultaneousConjugacyObservation.Probes
