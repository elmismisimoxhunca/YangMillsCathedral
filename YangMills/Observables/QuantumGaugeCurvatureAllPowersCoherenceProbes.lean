/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Observables.QuantumGaugeCurvatureAllPowersCoherence

namespace YangMills.Observables.QuantumGaugeCurvatureAllPowersCoherence.Probes

open Bundle
open scoped Bundle ContDiff Manifold Topology

universe uEG uHG uEB uHB uEP uHP uG uB uP uH

noncomputable section

variable
    {d : EuclideanDimension}
    {EG : Type uEG} {HG : Type uHG}
    [NormedAddCommGroup EG] [NormedSpace ℝ EG] [TopologicalSpace HG]
    {EB : Type uEB} {HB : Type uHB}
    [NormedAddCommGroup EB] [NormedSpace ℝ EB] [TopologicalSpace HB]
    {EP : Type uEP} {HP : Type uHP}
    [NormedAddCommGroup EP] [NormedSpace ℝ EP] [TopologicalSpace HP]
    {G : Type uG} {B : Type uB} {P : Type uP}
    [Group G] [TopologicalSpace G] [TopologicalSpace B] [TopologicalSpace P]
    [IsTopologicalGroup G]
    {IG : ModelWithCorners ℝ EG HG}
    {IB : ModelWithCorners ℝ EB HB}
    {IP : ModelWithCorners ℝ EP HP}
    [ChartedSpace HG G] [LieGroup IG ∞ G]
    [ChartedSpace HB B] [IsManifold IB ∞ B]
    [ChartedSpace HP P] [IsManifold IP ∞ P]
    {torsor : Geometry.PrincipalBundleTorsorData G B P}
    {bundle : Geometry.TopologicalPrincipalBundleData torsor}
    {smoothBundle : Geometry.SmoothPrincipalBundleData IB IG IP torsor bundle}
    [FiniteDimensional ℝ EG] [FiniteDimensional ℝ EB]
    {liftGroup : Type*} [Group liftGroup] [TopologicalSpace liftGroup]
    [IsTopologicalGroup liftGroup]
    {lift : Minkowski.ProperOrthochronousPoincareLiftData d liftGroup}
    {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H]
    {U : Minkowski.StronglyContinuousUnitaryPoincareRepresentation lift H}
    {vacuumData : Minkowski.PoincareInvariantVacuumData U}
    {D : Minkowski.CommonInvariantDomainData vacuumData}
    {family : Minkowski.TemperedLocalObservableFamilyData D}
    {GaugeGroup : Type*} [Group GaugeGroup]
    {action : QuantumGaugeObservableActionData GaugeGroup family}
    {geometry : Classical.EuclideanMetricData (IB := IB) (B := B)}
    {inner : Geometry.InvariantInnerProductData (I := IG) (G := G)}
    {connection : Geometry.PrincipalConnectionData smoothBundle}
    {exterior : Geometry.PrincipalConnectionExteriorDerivativeData connection}
    {certificate : Geometry.PrincipalCurvatureStructureCertificate
      smoothBundle connection exterior}
    {basic : CurvatureSquaredLocalObservableInterpretationData
      geometry inner connection exterior certificate family}
    {finitePowers : ScalarCurvaturePowerLocalObservableInterpretationData
      geometry inner connection exterior certificate family basic}

/-- Arbitrary powers use the exact designated action and exact observable family. -/
theorem exact_all_power_invariance
    (invariance : GaugeInvariantQuantumObservableFamilyData action)
    (allPowers : ScalarCurvatureAllPowersLocalObservableInterpretationData
      geometry inner connection exterior certificate family basic finitePowers)
    (g : GaugeGroup) (n : ℕ)
    (f : Minkowski.ScalarMinkowskiSchwartzTestFunction d) :
    action.operatorAction g (allPowers.quantumLabel n) f =
      family.operator (allPowers.quantumLabel n) f :=
  quantumGauge_invariant_curvatureAllPowers invariance allPowers g n f

/-- The old zero, one, and two labels are explicitly covered by the same law. -/
theorem exact_zero_one_two_invariance
    (invariance : GaugeInvariantQuantumObservableFamilyData action)
    (allPowers : ScalarCurvatureAllPowersLocalObservableInterpretationData
      geometry inner connection exterior certificate family basic finitePowers)
    (g : GaugeGroup) (f : Minkowski.ScalarMinkowskiSchwartzTestFunction d) :
    (action.operatorAction g (allPowers.quantumLabel 0) f =
        family.operator (allPowers.quantumLabel 0) f) ∧
      (action.operatorAction g (allPowers.quantumLabel 1) f =
        family.operator (allPowers.quantumLabel 1) f) ∧
      (action.operatorAction g (allPowers.quantumLabel 2) f =
        family.operator (allPowers.quantumLabel 2) f) :=
  ⟨quantumGauge_invariant_curvatureAllPowers_zero invariance allPowers g f,
    quantumGauge_invariant_curvatureAllPowers_one invariance allPowers g f,
    quantumGauge_invariant_curvatureAllPowers_two invariance allPowers g f⟩

/-- Changing any power operator contradicts the exact-action invariance certificate. -/
theorem changed_all_power_operator_blocked
    (invariance : GaugeInvariantQuantumObservableFamilyData action)
    (allPowers : ScalarCurvatureAllPowersLocalObservableInterpretationData
      geometry inner connection exterior certificate family basic finitePowers)
    (g : GaugeGroup) (n : ℕ)
    (f : Minkowski.ScalarMinkowskiSchwartzTestFunction d)
    (changed : action.operatorAction g (allPowers.quantumLabel n) f ≠
      family.operator (allPowers.quantumLabel n) f) : False :=
  changed (quantumGauge_invariant_curvatureAllPowers invariance allPowers g n f)

/-- A different action at any power cannot borrow the exact designated-action certificate. -/
theorem unrelated_action_substitution_blocked
    (invariance : GaugeInvariantQuantumObservableFamilyData action)
    (allPowers : ScalarCurvatureAllPowersLocalObservableInterpretationData
      geometry inner connection exterior certificate family basic finitePowers)
    (other : QuantumGaugeObservableActionData GaugeGroup family)
    (g : GaugeGroup) (n : ℕ)
    (f : Minkowski.ScalarMinkowskiSchwartzTestFunction d)
    (different : other.operatorAction g (allPowers.quantumLabel n) f ≠
      action.operatorAction g (allPowers.quantumLabel n) f) :
    other.operatorAction g (allPowers.quantumLabel n) f ≠
      family.operator (allPowers.quantumLabel n) f := by
  intro otherInvariant
  apply different
  rw [otherInvariant]
  symm
  exact quantumGauge_invariant_curvatureAllPowers invariance allPowers g n f

end

end YangMills.Observables.QuantumGaugeCurvatureAllPowersCoherence.Probes
