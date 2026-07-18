/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Reconstruction.StrictOrderedWickContinuation

/-!
# Hostile probes for strict ordered Wick continuation

The probes expose genuine integrability, exact Euclidean/Wightman value coherence, the explicit
nonzero arity-one ordered bump, and rejection of a disconnected continuation value. No datum is
constructed.
-/

namespace YangMills.Reconstruction.StrictOrderedWickContinuation.Probes

open MeasureTheory
open Minkowski

variable
    {d : EuclideanDimension} {G : Type*}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {lift : ProperOrthochronousPoincareLiftData d G}
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H]
    {U : StronglyContinuousUnitaryPoincareRepresentation lift H}
    {vacuumData : PoincareInvariantVacuumData U}
    {D : CommonInvariantDomainData vacuumData}
    {fieldData : ScalarWightmanFieldOnCommonDomainData D}
    {full : ScalarWightmanJointTemperedCorrelatorData fieldData}
    {euclidean : ScalarSchwingerDistributionFamily d}
    {minkowski : ScalarWightmanRelativeAnalyticCorrelatorData full}

/-- Every exact strict ordered continuation integrand is genuinely integrable. -/
theorem exact_ordered_integrability
    (C : MathlibStrictOrderedScalarWickContinuationData euclidean minkowski)
    (n : ℕ) (test : MathlibPositiveTimeOrderedFlatTestFunction d (n + 1)) :
    Integrable (fun x : EuclideanNPointSpace d (n + 1) =>
      (minkowski.analyticBoundary n).tubeFunction
          (reverseWickRotatedRelativeCoordinates d n x) * test.toSchwartz x) :=
  C.ordered_integrable n test

/-- Euclidean and analytic Wightman values agree exactly on every strict ordered test. -/
theorem exact_ordered_wick_coherence
    (C : MathlibStrictOrderedScalarWickContinuationData euclidean minkowski)
    (n : ℕ) (test : MathlibPositiveTimeOrderedFlatTestFunction d (n + 1)) :
    euclidean.positivePoint ⟨n + 1, Nat.zero_lt_succ n⟩ test.toSchwartz =
      ∫ x : EuclideanNPointSpace d (n + 1),
        (minkowski.analyticBoundary n).tubeFunction
            (reverseWickRotatedRelativeCoordinates d n x) * test.toSchwartz x :=
  C.ordered_coherent n test

/-- The explicit nonzero positive-time bump exercises the arity-one continuation surface. -/
theorem explicit_bump_wick_coherence
    (C : MathlibStrictOrderedScalarWickContinuationData euclidean minkowski) :
    euclidean.positivePoint ⟨1, Nat.zero_lt_succ 0⟩
      (positiveTimeBumpOrderedFlatTest d).toSchwartz =
      ∫ x : EuclideanNPointSpace d 1,
        (minkowski.analyticBoundary 0).tubeFunction
            (reverseWickRotatedRelativeCoordinates d 0 x) *
          (positiveTimeBumpOrderedFlatTest d).toSchwartz x := by
  simpa using C.ordered_coherent 0 (positiveTimeBumpOrderedFlatTest d)

/-- The explicit test carrier in the continuation probe is genuinely nonzero. -/
theorem explicit_bump_test_ne_zero :
    (positiveTimeBumpOrderedFlatTest d).toSchwartz ≠ 0 :=
  positiveTimeBumpSchwartz_ne_zero d

/-- Every nonzero strict-test value is evaluated inside the exact holomorphy tube. -/
theorem nonzero_test_value_maps_into_tube
    (n : ℕ) (test : MathlibPositiveTimeOrderedFlatTestFunction d (n + 1))
    (x : EuclideanNPointSpace d (n + 1)) (hx : test.toSchwartz x ≠ 0) :
    reverseWickRotatedRelativeCoordinates d n x ∈ wightmanBackwardTube d n :=
  strictOrderedTest_nonzero_maps_backwardTube test x hx

/-- Outside the tube preimage, the exact continuation integrand vanishes through the strict test. -/
theorem outside_tube_integrand_zero
    (n : ℕ) (test : MathlibPositiveTimeOrderedFlatTestFunction d (n + 1))
    (x : EuclideanNPointSpace d (n + 1))
    (hnot : reverseWickRotatedRelativeCoordinates d n x ∉ wightmanBackwardTube d n) :
    (minkowski.analyticBoundary n).tubeFunction
        (reverseWickRotatedRelativeCoordinates d n x) * test.toSchwartz x = 0 :=
  strictOrderedWickIntegrand_eq_zero_of_not_mem_backwardTube test _ x hnot

/-- A disconnected proposed continuation value is rejected against the exact Euclidean
Schwinger-distribution value. -/
theorem disconnected_continuation_value_blocked
    (C : MathlibStrictOrderedScalarWickContinuationData euclidean minkowski)
    (n : ℕ) (test : MathlibPositiveTimeOrderedFlatTestFunction d (n + 1)) (z : ℂ)
    (hmismatch : z ≠ euclidean.positivePoint
      ⟨n + 1, Nat.zero_lt_succ n⟩ test.toSchwartz) :
    (∫ x : EuclideanNPointSpace d (n + 1),
      (minkowski.analyticBoundary n).tubeFunction
          (reverseWickRotatedRelativeCoordinates d n x) * test.toSchwartz x) ≠ z := by
  rw [← C.ordered_coherent n test]
  exact fun h => hmismatch h.symm

end YangMills.Reconstruction.StrictOrderedWickContinuation.Probes
