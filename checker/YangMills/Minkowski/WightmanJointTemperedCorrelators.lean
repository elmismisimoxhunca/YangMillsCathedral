/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Minkowski.WightmanVacuumCorrelators
import YangMills.Mathematics.FiniteConfigurationSchwartzTensor

/-!
# Jointly tempered scalar Wightman correlator interface

Wightman 1956 treats each ordered `n`-point vacuum expectation value as one distribution on the
full product spacetime, and Streater–Wightman printed p. 106, equations `(3-19)`–`(3-21)`, gives the
full-product tempered formulation rather than merely a function of separately smeared tests. This module requires
an actual Mathlib tempered distribution on `Fin n → Spacetime d` for every arity and ties its value
on every exact pure Schwartz tensor to the algebraic ordered field-word expectation.

The pure-tensor map is signature-neutral reusable mathematics. This interface does not assert tube
analyticity, boundary-value theorems, Euclidean continuation, reconstruction, or existence of any
correlator family.
-/

namespace YangMills.Minkowski

open scoped SchwartzMap

/-- Actual full-product Minkowski Schwartz carrier at arity `n`. -/
abbrev ScalarMinkowskiNPointSchwartzTestFunction
    (d : EuclideanDimension) (n : ℕ) :=
  𝓢(Mathematics.FiniteConfiguration (Spacetime d) n, ℂ)

/-- Jointly tempered ordered scalar vacuum correlators coherent with exact finite field words. -/
structure ScalarWightmanJointTemperedCorrelatorData
    {d : EuclideanDimension} {G : Type*}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {lift : ProperOrthochronousPoincareLiftData d G}
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H]
    {U : StronglyContinuousUnitaryPoincareRepresentation lift H}
    {vacuumData : PoincareInvariantVacuumData U}
    {D : CommonInvariantDomainData vacuumData}
    (fieldData : ScalarWightmanFieldOnCommonDomainData D) where
  /-- One actual tempered distribution on the full `n`-point Minkowski Schwartz space. -/
  nPointDistribution : ∀ n : ℕ,
    TemperedDistribution (Mathematics.FiniteConfiguration (Spacetime d) n) ℂ
  /-- Exact coherence on every finite pure tensor, preserving coordinate/operator order. -/
  pureTensor_coherent : ∀ (n : ℕ)
    (tests : Fin n → ScalarMinkowskiSchwartzTestFunction d),
    nPointDistribution n (Mathematics.scalarSchwartzPureTensor (Spacetime d) n tests) =
      scalarWightmanVacuumExpectation fieldData (List.ofFn tests)

/-- Arity zero evaluates the exact scalar-unit test to one. -/
theorem ScalarWightmanJointTemperedCorrelatorData.zeroPoint_unit
    {d : EuclideanDimension} {G : Type*}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {lift : ProperOrthochronousPoincareLiftData d G}
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H]
    {U : StronglyContinuousUnitaryPoincareRepresentation lift H}
    {vacuumData : PoincareInvariantVacuumData U}
    {D : CommonInvariantDomainData vacuumData}
    {fieldData : ScalarWightmanFieldOnCommonDomainData D}
    (correlators : ScalarWightmanJointTemperedCorrelatorData fieldData) :
    correlators.nPointDistribution 0
      (Mathematics.scalarZeroConfigurationSchwartz (Spacetime d) 1) = 1 := by
  simpa using correlators.pureTensor_coherent 0
    (fun i : Fin 0 => Fin.elim0 i)

end YangMills.Minkowski
