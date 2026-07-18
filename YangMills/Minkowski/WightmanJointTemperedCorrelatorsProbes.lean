/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Minkowski.WightmanJointTemperedCorrelators

/-!
# Hostile probes for jointly tempered Wightman correlators

The probes expose full-product carriers, zero normalization, exact pure-tensor coherence, one- and
two-point operator order, and rejection of a disconnected distribution value. No correlator datum
is constructed.
-/

namespace YangMills.Minkowski.WightmanJointTemperedCorrelators.Probes

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
    (correlators : ScalarWightmanJointTemperedCorrelatorData fieldData)

/-- Every arity is an actual Mathlib tempered distribution on the full product carrier. -/
def exact_full_product_distribution (n : ℕ) :
    TemperedDistribution (Mathematics.FiniteConfiguration (Spacetime d) n) ℂ :=
  correlators.nPointDistribution n

/-- Pure tensor coherence is exact at every arity. -/
theorem exact_pure_tensor_coherence
    (n : ℕ) (tests : Fin n → ScalarMinkowskiSchwartzTestFunction d) :
    correlators.nPointDistribution n
      (Mathematics.scalarSchwartzPureTensor (Spacetime d) n tests) =
      scalarWightmanVacuumExpectation fieldData (List.ofFn tests) :=
  correlators.pureTensor_coherent n tests

/-- The full-product zero-point distribution evaluates its exact unit to one. -/
theorem exact_zero_point_unit :
    correlators.nPointDistribution 0
      (Mathematics.scalarZeroConfigurationSchwartz (Spacetime d) 1) = 1 :=
  correlators.zeroPoint_unit

/-- Therefore the jointly tempered family cannot be identically zero. -/
theorem zero_point_distribution_ne_zero :
    correlators.nPointDistribution 0 ≠ 0 := by
  intro hzero
  have happly := congrArg
    (fun T : TemperedDistribution (Mathematics.FiniteConfiguration (Spacetime d) 0) ℂ =>
      T (Mathematics.scalarZeroConfigurationSchwartz (Spacetime d) 1)) hzero
  rw [correlators.zeroPoint_unit] at happly
  simp at happly

/-- Arity one recovers the exact coherent one-field vacuum matrix element. -/
theorem exact_one_point_pure_tensor
    (f : ScalarMinkowskiSchwartzTestFunction d) :
    correlators.nPointDistribution 1
      (Mathematics.scalarSchwartzPureTensor (Spacetime d) 1 (fun _ => f)) =
      fieldData.matrixElement D.vacuumInDomain D.vacuumInDomain f := by
  rw [correlators.pureTensor_coherent]
  simpa using scalarWightmanVacuumExpectation_singleton_eq_matrixElement fieldData f

/-- Arity two preserves exact `Φ(f) Φ(g) Ω` order. -/
theorem exact_two_point_pure_tensor
    (f g : ScalarMinkowskiSchwartzTestFunction d) :
    correlators.nPointDistribution 2
      (Mathematics.scalarSchwartzPureTensor (Spacetime d) 2
        (fun i => Fin.cases f (fun _ => g) i)) =
      inner ℂ vacuumData.vacuum
        ((fieldData.field f (fieldData.field g D.vacuumInDomain) : D.domain) : H) := by
  rw [correlators.pureTensor_coherent]
  simpa using scalarWightmanVacuumExpectation_pair fieldData f g

/-- A disconnected tempered distribution cannot replace an exact pure-tensor value when it differs
from the field-word expectation. -/
theorem disconnected_distribution_value_blocked
    (n : ℕ) (tests : Fin n → ScalarMinkowskiSchwartzTestFunction d)
    (T : TemperedDistribution (Mathematics.FiniteConfiguration (Spacetime d) n) ℂ)
    (hmismatch : T (Mathematics.scalarSchwartzPureTensor (Spacetime d) n tests) ≠
      scalarWightmanVacuumExpectation fieldData (List.ofFn tests)) :
    T (Mathematics.scalarSchwartzPureTensor (Spacetime d) n tests) ≠
      correlators.nPointDistribution n
        (Mathematics.scalarSchwartzPureTensor (Spacetime d) n tests) := by
  rw [correlators.pureTensor_coherent]
  exact hmismatch

end YangMills.Minkowski.WightmanJointTemperedCorrelators.Probes
