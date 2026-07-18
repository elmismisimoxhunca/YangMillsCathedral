/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Euclidean.SchwingerCoordinateInjection
import YangMills.Euclidean.PositiveTimeSchwartzBump

/-!
# Hostile probes for Schwinger coordinate injections

The probes force exact source-coordinate retention, off-coordinate vanishing, injectivity,
continuity for the named topology, and exact singleton versus empty support.
-/

namespace YangMills.Euclidean.SchwingerCoordinateInjection.Probes

/-- The source test appears unchanged at the injected natural arity. -/
theorem exact_coordinate_component
    (d : EuclideanDimension) (n : ℕ) (f : ScalarSchwartzTestFunction d n) :
    (scalarSchwartzCoordinateInjectionContinuousLinearMap d n f).component n = f :=
  scalarSchwartzCoordinateInjection_component_self d n f

/-- Every distinct coordinate is exactly zero. -/
theorem distinct_coordinate_component_zero
    (d : EuclideanDimension) (n : ℕ) (f : ScalarSchwartzTestFunction d n)
    (m : ℕ) (h : m ≠ n) :
    (scalarSchwartzCoordinateInjectionContinuousLinearMap d n f).component m = 0 :=
  scalarSchwartzCoordinateInjection_component_ne d n f m h

/-- The coordinate injection cannot collapse two different Schwartz tests. -/
theorem coordinate_injection_is_injective
    (d : EuclideanDimension) (n : ℕ) :
    Function.Injective (scalarSchwartzCoordinateInjectionContinuousLinearMap d n) :=
  scalarSchwartzCoordinateInjection_injective d n

/-- The coordinate map is genuinely continuous into the explicit named preliminary topology. -/
theorem coordinate_injection_is_continuous
    (d : EuclideanDimension) (n : ℕ) :
    @Continuous (ScalarSchwartzTestFunction d n) (ScalarFiniteSchwartzSequence d)
      inferInstance (scalarFiniteSchwartzFiniteStageFinalTopology d)
      (scalarSchwartzCoordinateInjectionContinuousLinearMap d n) := by
  letI : TopologicalSpace (ScalarFiniteSchwartzSequence d) :=
    scalarFiniteSchwartzFiniteStageFinalTopology d
  letI : AddCommGroup (ScalarFiniteSchwartzSequence d) :=
    scalarFiniteSchwartzSequenceAddCommGroup d
  letI : Module ℂ (ScalarFiniteSchwartzSequence d) :=
    scalarFiniteSchwartzSequenceModule d
  exact (scalarSchwartzCoordinateInjectionContinuousLinearMap d n).continuous

/-- A nonzero test obtains exactly singleton support, with no disconnected support witness. -/
theorem nonzero_coordinate_exact_support
    (d : EuclideanDimension) (n : ℕ) (f : ScalarSchwartzTestFunction d n)
    (hnonzero : f ≠ 0) :
    (scalarSchwartzCoordinateInjectionContinuousLinearMap d n f).support = {n} :=
  scalarSchwartzCoordinateInjection_support_eq_singleton d n f hnonzero

/-- A zero test obtains empty rather than fake singleton support. -/
theorem zero_coordinate_empty_support
    (d : EuclideanDimension) (n : ℕ) :
    (scalarSchwartzCoordinateInjectionContinuousLinearMap d n
      (0 : ScalarSchwartzTestFunction d n)).support = ∅ :=
  scalarSchwartzCoordinateInjection_zero_support d n

/-- Injecting the explicit positive-time bump at arity one produces exact support `{1}`. -/
theorem positive_bump_coordinate_support
    (d : EuclideanDimension) :
    (scalarSchwartzCoordinateInjectionContinuousLinearMap d 1
      (positiveTimeBumpSchwartz d)).support = {1} :=
  scalarSchwartzCoordinateInjection_support_eq_singleton d 1
    (positiveTimeBumpSchwartz d) (positiveTimeBumpSchwartz_ne_zero d)

/-- Replacing a distinct zero coordinate by a nonzero source test is impossible. -/
theorem nonzero_wrong_coordinate_blocked
    (d : EuclideanDimension) (n m : ℕ) (h : m ≠ n)
    (g : ScalarSchwartzTestFunction d n)
    (f : ScalarSchwartzTestFunction d m) (hnonzero : f ≠ 0)
    (hwrong : (scalarSchwartzCoordinateInjectionContinuousLinearMap d n g).component m = f) :
    False := by
  rw [scalarSchwartzCoordinateInjection_component_ne d n g m h] at hwrong
  exact hnonzero hwrong.symm

end YangMills.Euclidean.SchwingerCoordinateInjection.Probes
