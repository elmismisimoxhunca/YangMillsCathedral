/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Mathematics.PartitionedFixedBaseConjugacyObservation

/-!
# Hostile probes for base-point-partitioned joint holonomy fields
-/

namespace YangMills.Mathematics.PartitionedFixedBaseConjugacyObservation.Probes

universe uBase uLoop uG uΩ

variable {Base : Type uBase} {LoopAt : Base → Type uLoop}
    {G : Type uG} {Ω : Type uΩ} [Group G] [MeasurableSpace G]

/-- Every observation carries one exact base and a genuinely positive family at that base. -/
theorem exact_single_base_positive_family
    (family : PartitionedFixedBaseFiniteFamily LoopAt) :
    Nonempty (LoopAt family.1) ∧ 0 < family.2.card :=
  ⟨⟨family.2.first⟩, Nat.zero_lt_succ family.2.1⟩

/-- The generated field makes every exact partitioned observation measurable. -/
theorem exact_partitioned_observation_generated
    (holonomy : ∀ base, LoopAt base → Ω → G)
    (family : PartitionedFixedBaseFiniteFamily LoopAt) :
    @Measurable Ω (partitionedFixedBaseConjugacyObservationValue (G := G) family)
      (partitionedFixedBaseConjugacyGeneratedMeasurableSpace holonomy)
      inferInstance (partitionedFixedBaseConjugacyObservation holonomy family) :=
  partitionedFixedBaseConjugacyObservation_measurable_generated holonomy family

omit [MeasurableSpace G] in
/-- Different base points receive independently selectable conjugators; the theorem only applies the
conjugator belonging to the one base carried by the current family. -/
theorem exact_basewise_common_conjugation
    (holonomy : ∀ base, LoopAt base → Ω → G) (conjugator : Base → Ω → G)
    (family : PartitionedFixedBaseFiniteFamily LoopAt) (sample : Ω) :
    partitionedFixedBaseConjugacyObservation
        (fun base loop samplePoint =>
          (conjugator base samplePoint)⁻¹ * holonomy base loop samplePoint *
            conjugator base samplePoint)
        family sample =
      partitionedFixedBaseConjugacyObservation holonomy family sample :=
  partitionedFixedBaseConjugacyObservation_common_conjugation
    holonomy conjugator family sample

/-- Exact recognition of an ambient field still requires a converse coverage witness. -/
theorem exact_ambient_recognition [MeasurableSpace Ω]
    (holonomy : ∀ base, LoopAt base → Ω → G)
    (holonomy_measurable : ∀ base loop, Measurable (holonomy base loop))
    (generated_covers : (inferInstance : MeasurableSpace Ω) ≤
      partitionedFixedBaseConjugacyGeneratedMeasurableSpace holonomy) :
    (inferInstance : MeasurableSpace Ω) =
      partitionedFixedBaseConjugacyGeneratedMeasurableSpace holonomy :=
  ambient_eq_partitionedFixedBaseConjugacyGeneratedMeasurableSpace
    holonomy holonomy_measurable generated_covers

/-- If there is no base point, no empty-family observation can be fabricated. -/
theorem empty_base_blocks_observation [IsEmpty Base] :
    IsEmpty (PartitionedFixedBaseFiniteFamily LoopAt) := by
  constructor
  intro family
  exact isEmptyElim family.1

end YangMills.Mathematics.PartitionedFixedBaseConjugacyObservation.Probes
