/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Mathematics.ObservationGeneratedMeasurableSpace

/-!
# Hostile probes for observation-generated measurable spaces
-/

namespace YangMills.Mathematics.ObservationGeneratedMeasurableSpace.Probes

universe uΩ uObservation uValue

/-- Every exact dependent observation is measurable on the generated carrier. -/
theorem exact_observation_measurable
    {Ω : Type uΩ} {Observation : Type uObservation}
    (Value : Observation → Type uValue)
    (target : ∀ observation, MeasurableSpace (Value observation))
    (observe : ∀ observation, Ω → Value observation)
    (observation : Observation) :
    @Measurable Ω (Value observation)
      (observationGeneratedMeasurableSpace Value target observe)
      (target observation) (observe observation) :=
  observation_measurable Value target observe observation

/-- A proposed ambient sigma field is accepted only when it contains every observation comap. -/
theorem exact_generated_minimality
    {Ω : Type uΩ} {Observation : Type uObservation}
    (Value : Observation → Type uValue)
    (target : ∀ observation, MeasurableSpace (Value observation))
    (observe : ∀ observation, Ω → Value observation)
    (ambient : MeasurableSpace Ω)
    (each : ∀ observation,
      MeasurableSpace.comap (observe observation) (target observation) ≤ ambient) :
    observationGeneratedMeasurableSpace Value target observe ≤ ambient :=
  observationGeneratedMeasurableSpace_le Value target observe ambient each

/-- A constant observation generates only the trivial sigma field; the construction cannot silently
replace a holonomy-generated field by the full measurable space. -/
theorem constant_unit_observation_is_trivial :
    observationGeneratedMeasurableSpace
        (fun _ : Unit => Unit)
        (fun _ => ⊤)
        (fun (_ : Unit) (_ : Bool) => ()) = ⊥ := by
  apply le_antisymm
  · apply observationGeneratedMeasurableSpace_le
    intro observation
    simp
  · exact bot_le

/-- Conversely, one exact identity observation recovers its designated target measurable space. -/
theorem identity_observation_recovers_target
    (Ω : Type uΩ) (target : MeasurableSpace Ω) :
    observationGeneratedMeasurableSpace
        (fun _ : Unit => Ω)
        (fun _ => target)
        (fun _ => id) = target := by
  simp [observationGeneratedMeasurableSpace]

/-- Surjective reindexing cannot discard one of the generating observations. -/
theorem exact_surjective_reindexing
    {Ω : Type uΩ} {Observation : Type uObservation} {Observation' : Type*}
    (Value : Observation → Type uValue)
    (target : ∀ observation, MeasurableSpace (Value observation))
    (observe : ∀ observation, Ω → Value observation)
    (index : Observation' → Observation) (surjective : Function.Surjective index) :
    observationGeneratedMeasurableSpace (fun observation' => Value (index observation'))
        (fun observation' => target (index observation'))
        (fun observation' => observe (index observation')) =
      observationGeneratedMeasurableSpace Value target observe :=
  observationGeneratedMeasurableSpace_comp_surjective
    Value target observe index surjective

end YangMills.Mathematics.ObservationGeneratedMeasurableSpace.Probes
