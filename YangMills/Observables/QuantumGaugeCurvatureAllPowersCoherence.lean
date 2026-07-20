/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Observables.QuantumGaugeObservableAction
import YangMills.Observables.CurvatureAllPowersInterpretation

/-!
# Quantum gauge coherence for all natural curvature-density powers

An all-label invariance certificate for one exact independently designated quantum gauge action
specializes to every label interpreting `(F²)ⁿ`. This one-way bridge constructs no action and does
not replace the designated action or observable family.
-/

namespace YangMills.Observables

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

/-- Every natural-power label is fixed by the exact designated action. -/
theorem quantumGauge_invariant_curvatureAllPowers
    (invariance : GaugeInvariantQuantumObservableFamilyData action)
    (allPowers : ScalarCurvatureAllPowersLocalObservableInterpretationData
      geometry inner connection exterior certificate family basic finitePowers)
    (g : GaugeGroup) (n : ℕ)
    (f : Minkowski.ScalarMinkowskiSchwartzTestFunction d) :
    action.operatorAction g (allPowers.quantumLabel n) f =
      family.operator (allPowers.quantumLabel n) f :=
  invariance.operator_invariant g _ f

/-- Power zero inherits invariance from the same exact action. -/
theorem quantumGauge_invariant_curvatureAllPowers_zero
    (invariance : GaugeInvariantQuantumObservableFamilyData action)
    (allPowers : ScalarCurvatureAllPowersLocalObservableInterpretationData
      geometry inner connection exterior certificate family basic finitePowers)
    (g : GaugeGroup) (f : Minkowski.ScalarMinkowskiSchwartzTestFunction d) :
    action.operatorAction g (allPowers.quantumLabel 0) f =
      family.operator (allPowers.quantumLabel 0) f :=
  quantumGauge_invariant_curvatureAllPowers invariance allPowers g 0 f

/-- Power one inherits invariance from the same exact action. -/
theorem quantumGauge_invariant_curvatureAllPowers_one
    (invariance : GaugeInvariantQuantumObservableFamilyData action)
    (allPowers : ScalarCurvatureAllPowersLocalObservableInterpretationData
      geometry inner connection exterior certificate family basic finitePowers)
    (g : GaugeGroup) (f : Minkowski.ScalarMinkowskiSchwartzTestFunction d) :
    action.operatorAction g (allPowers.quantumLabel 1) f =
      family.operator (allPowers.quantumLabel 1) f :=
  quantumGauge_invariant_curvatureAllPowers invariance allPowers g 1 f

/-- Power two inherits invariance from the same exact action. -/
theorem quantumGauge_invariant_curvatureAllPowers_two
    (invariance : GaugeInvariantQuantumObservableFamilyData action)
    (allPowers : ScalarCurvatureAllPowersLocalObservableInterpretationData
      geometry inner connection exterior certificate family basic finitePowers)
    (g : GaugeGroup) (f : Minkowski.ScalarMinkowskiSchwartzTestFunction d) :
    action.operatorAction g (allPowers.quantumLabel 2) f =
      family.operator (allPowers.quantumLabel 2) f :=
  quantumGauge_invariant_curvatureAllPowers invariance allPowers g 2 f

end

end YangMills.Observables
