/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Euclidean.SchwingerOrderedTestSpace

/-!
# Hostile probes for ordered and coincidence-flat Schwinger tests

The probes show that all-positive support does not imply time ordering, expose the exact derivative
flatness field, and retain the nonzero arity-one witness. They do not claim equivalence with OS-I's
printed source space or reflection positivity.
-/

namespace YangMills.Euclidean.SchwingerOrderedTestSpace.Probes

/-- A two-point configuration with positive but decreasing selected times. -/
noncomputable def reversedPositiveTimes (d : EuclideanDimension) :
    EuclideanNPointSpace d 2 :=
  fun i => if i = 0 then EuclideanSpace.single (euclideanTimeCoordinate d) 2
    else EuclideanSpace.single (euclideanTimeCoordinate d) 1

/-- Both times in the reversed configuration are strictly positive. -/
theorem reversedPositiveTimes_all_positive
    (d : EuclideanDimension) :
    ∀ i, 0 < reversedPositiveTimes d i (euclideanTimeCoordinate d) := by
  intro i
  fin_cases i <;> simp [reversedPositiveTimes]

/-- Merely requiring all times positive cannot replace the strict ordering field. -/
theorem positive_but_reversed_order_blocked
    (d : EuclideanDimension) :
    reversedPositiveTimes d ∉ strictPositiveTimeOrderedConfigurationSet d 2 := by
  intro hordered
  have h := hordered.2 (0 : Fin 2) (1 : Fin 2) (by decide)
  simp [reversedPositiveTimes] at h

/-- The packaged ordered-flat arity-one witness retains the previously proved nonzero test. -/
theorem positiveTimeBumpOrderedFlatTest_ne_zero
    (d : EuclideanDimension) :
    (positiveTimeBumpOrderedFlatTest d).toSchwartz ≠ 0 :=
  positiveTimeBumpSchwartz_ne_zero d

/-- The ordered-support projection is tied to the exact underlying Schwartz test. -/
theorem exact_ordered_support
    (d : EuclideanDimension) (n : ℕ)
    (f : MathlibPositiveTimeOrderedFlatTestFunction d n) :
    HasStrictPositiveTimeOrderedSupport d f.toSchwartz :=
  f.ordered_support

/-- Coincidence flatness is derived from the exact strict ordered-support field in the current
strong subspace, so it cannot be disconnected from the carrier geometry. -/
theorem strict_ordered_support_derives_flatness
    (d : EuclideanDimension) (n : ℕ) (f : ScalarSchwartzTestFunction d n)
    (hsupport : HasStrictPositiveTimeOrderedSupport d f) :
    IsFlatAtPointCoincidences f :=
  strictOrderedSupport_implies_coincidenceFlat f hsupport

/-- The coincidence-flatness projection controls every derivative order of the exact underlying
Schwartz test at the exact coincident configuration. -/
theorem exact_coincidence_flatness
    (d : EuclideanDimension) (n k : ℕ)
    (f : MathlibPositiveTimeOrderedFlatTestFunction d n)
    (x : EuclideanNPointSpace d n) (hcoin : HasPointCoincidence x) :
    iteratedFDeriv ℝ k
        (f.toSchwartz : EuclideanNPointSpace d n → ℂ) x = 0 :=
  f.coincidence_flat k x hcoin

end YangMills.Euclidean.SchwingerOrderedTestSpace.Probes
