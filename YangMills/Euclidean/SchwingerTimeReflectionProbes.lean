/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Euclidean.SchwingerTimeReflection

/-!
# Hostile probes for Euclidean time reflection

These probes verify the selected coordinate flip, involutivity, nonempty positive-time configuration
sets, and incompatibility of strict positive time with its reflection. They deliberately record that
the zero Schwartz test has positive-time support; a future `(E2)` record must therefore prove a
nonzero positive-time test exists, bridge to OS-I's time-ordered/diagonal-flat source spaces, and
construct the finite test-sequence product rather than relying on subtype inhabitation alone.
-/

namespace YangMills.Euclidean.SchwingerTimeReflection.Probes

/-- A point one unit along the selected positive Euclidean-time coordinate. -/
noncomputable def positiveTimeUnitPoint (d : EuclideanDimension) : d.Spacetime :=
  EuclideanSpace.single (euclideanTimeCoordinate d) 1

/-- The constant configuration at positive time one. -/
noncomputable def positiveTimeUnitConfiguration
    (d : EuclideanDimension) (n : ℕ) : EuclideanNPointSpace d n :=
  fun _ => positiveTimeUnitPoint d

/-- Every arity's strict-positive-time configuration set is nonempty. -/
theorem positiveTimeUnitConfiguration_mem
    (d : EuclideanDimension) (n : ℕ) :
    positiveTimeUnitConfiguration d n ∈ strictPositiveTimeConfigurationSet d n := by
  intro i
  simp [positiveTimeUnitConfiguration, positiveTimeUnitPoint]

/-- The reflected selected time coordinate is exactly negated. -/
theorem exact_time_coordinate_flip
    (d : EuclideanDimension) (x : d.Spacetime) :
    euclideanTimeReflection d x (euclideanTimeCoordinate d) =
      -x (euclideanTimeCoordinate d) :=
  euclideanTimeReflection_time d x

/-- Reflection pullback is genuinely involutive on the exact Schwartz carrier. -/
theorem exact_schwartz_reflection_involutive
    (d : EuclideanDimension) {n : ℕ} (f : ScalarSchwartzTestFunction d n) :
    reflectScalarSchwartzTestFunction d (reflectScalarSchwartzTestFunction d f) = f :=
  reflectScalarSchwartzTestFunction_involutive d f

/-- At positive arity, a strict-positive-time configuration and its reflected configuration cannot
both have strict positive time. -/
theorem positive_and_reflected_positive_time_blocked
    (d : EuclideanDimension) (n : PositiveArity) (x : EuclideanNPointSpace d n.value)
    (hpositive : x ∈ strictPositiveTimeConfigurationSet d n.value)
    (hreflected : (fun i => euclideanTimeReflection d (x i)) ∈
      strictPositiveTimeConfigurationSet d n.value) : False := by
  let i : Fin n.value := ⟨0, n.positive⟩
  have hp := hpositive i
  have hr := hreflected i
  rw [euclideanTimeReflection_time] at hr
  linarith

/-- The zero Schwartz test has strict-positive-time support vacuously. Subtype nonemptiness alone is
therefore not acceptable evidence that the future reflection-positivity test domain is nontrivial. -/
theorem zero_has_strictPositiveTimeSupport
    (d : EuclideanDimension) (n : ℕ) :
    HasStrictPositiveTimeSupport d (0 : ScalarSchwartzTestFunction d n) := by
  change tsupport (0 : EuclideanNPointSpace d n → ℂ) ⊆ _
  rw [tsupport_zero]
  exact Set.empty_subset _

end YangMills.Euclidean.SchwingerTimeReflection.Probes
