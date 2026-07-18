/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Reconstruction.ReverseWickRotationGeometry
import YangMills.Minkowski.WightmanRelativeAnalyticCorrelators

/-!
# Strict-ordered smeared Wick-continuation coherence

OS-I printed p. 98, equation `(5.1)`, obtains Euclidean Green functions by evaluating Wightman
analytic functions at `(-iτ, x⃗)`, and equation `(5.2)` gives the initial compact-support smeared
integral. The source writes unreversed arguments; the explicit reversal here uses the analytic
permutation symmetry stated immediately before `(5.1)` so increasing project order lands in the
chosen backward-tube convention. This interface states the corresponding smeared equality on the
project's current strict positive-time ordered Schwartz subspace.

This is deliberately named `MathlibStrictOrderedScalarWickContinuationData`: the strict
support/flat test carrier is stronger than OS-I's printed derivative-vanishing carrier, and no
source-space comparison, density, full-distribution equality, or reconstruction theorem is claimed.
Requiring coordinate-Lebesgue integrability for every possibly noncompact strict Schwartz test is
an explicit strengthening of the source's initial compact-support integral. No continuation datum
or theory is constructed.
-/

namespace YangMills.Reconstruction

open MeasureTheory
open Minkowski

/-- Exact smeared Wick-continuation coherence on the current strict ordered Mathlib test domain. -/
structure MathlibStrictOrderedScalarWickContinuationData
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
    (euclidean : ScalarSchwingerDistributionFamily d)
    (minkowski : ScalarWightmanRelativeAnalyticCorrelatorData full) where
  /-- The analytically continued integrand is genuinely integrable for every strict ordered test. -/
  ordered_integrable : ∀ (n : ℕ)
    (test : MathlibPositiveTimeOrderedFlatTestFunction d (n + 1)),
    Integrable (fun x : EuclideanNPointSpace d (n + 1) =>
      (minkowski.analyticBoundary n).tubeFunction
          (reverseWickRotatedRelativeCoordinates d n x) * test.toSchwartz x)
  /-- Exact equality between the Euclidean distribution and the same analytic Wightman function on
  every strict ordered test. -/
  ordered_coherent : ∀ (n : ℕ)
    (test : MathlibPositiveTimeOrderedFlatTestFunction d (n + 1)),
    euclidean.positivePoint ⟨n + 1, Nat.zero_lt_succ n⟩ test.toSchwartz =
      ∫ x : EuclideanNPointSpace d (n + 1),
        (minkowski.analyticBoundary n).tubeFunction
            (reverseWickRotatedRelativeCoordinates d n x) * test.toSchwartz x

/-- Every configuration where a strict ordered test is nonzero maps into the exact backward tube. -/
theorem strictOrderedTest_nonzero_maps_backwardTube
    {d : EuclideanDimension} {n : ℕ}
    (test : MathlibPositiveTimeOrderedFlatTestFunction d (n + 1))
    (x : EuclideanNPointSpace d (n + 1)) (hx : test.toSchwartz x ≠ 0) :
    reverseWickRotatedRelativeCoordinates d n x ∈ wightmanBackwardTube d n := by
  have hxSupport : x ∈ tsupport
      (test.toSchwartz : EuclideanNPointSpace d (n + 1) → ℂ) :=
    subset_tsupport test.toSchwartz hx
  exact reverseWickRotatedRelativeCoordinates_mem_backwardTube d n x
    (test.ordered_support hxSupport)

/-- Outside the exact backward-tube preimage, the strict-test continuation integrand is zero. -/
theorem strictOrderedWickIntegrand_eq_zero_of_not_mem_backwardTube
    {d : EuclideanDimension} {n : ℕ}
    (test : MathlibPositiveTimeOrderedFlatTestFunction d (n + 1))
    (F : (Fin n → ComplexifiedSpacetime d) → ℂ)
    (x : EuclideanNPointSpace d (n + 1))
    (hnot : reverseWickRotatedRelativeCoordinates d n x ∉ wightmanBackwardTube d n) :
    F (reverseWickRotatedRelativeCoordinates d n x) * test.toSchwartz x = 0 := by
  have htest : test.toSchwartz x = 0 := by
    by_contra hx
    exact hnot (strictOrderedTest_nonzero_maps_backwardTube test x hx)
  rw [htest, mul_zero]

end YangMills.Reconstruction
