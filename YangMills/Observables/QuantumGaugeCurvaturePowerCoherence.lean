/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Observables.QuantumGaugeObservableAction
import YangMills.Observables.CurvaturePowerInterpretation

/-!
# Quantum gauge coherence for the finite curvature-power interpretation

An all-label invariance certificate for one exact independently designated quantum gauge action
specializes to the labels interpreting `1`, `F²`, and `(F²)²`. This is a one-way coherence bridge: it
does not construct an action or reuse classical same-family gauge transport.
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
    (basic : CurvatureSquaredLocalObservableInterpretationData
      geometry inner connection exterior certificate family)

omit [FiniteDimensional ℝ EB] in
/-- The interpreted basic unit label is fixed by the exact designated quantum gauge action. -/
theorem quantumGauge_invariant_basic_unit
    (invariance : GaugeInvariantQuantumObservableFamilyData action)
    (g : GaugeGroup) (f : Minkowski.ScalarMinkowskiSchwartzTestFunction d) :
    action.operatorAction g (basic.quantumLabel .unit) f =
      family.operator (basic.quantumLabel .unit) f :=
  invariance.operator_invariant g _ f

omit [FiniteDimensional ℝ EB] in
/-- The interpreted basic `F²` label is fixed by the exact designated quantum gauge action. -/
theorem quantumGauge_invariant_basic_curvatureSquared
    (invariance : GaugeInvariantQuantumObservableFamilyData action)
    (g : GaugeGroup) (f : Minkowski.ScalarMinkowskiSchwartzTestFunction d) :
    action.operatorAction g (basic.quantumLabel .curvatureSquared) f =
      family.operator (basic.quantumLabel .curvatureSquared) f :=
  invariance.operator_invariant g _ f

/-- Every label selected by the finite curvature-power interpretation inherits all-label quantum
gauge invariance. -/
theorem quantumGauge_invariant_curvaturePower
    (invariance : GaugeInvariantQuantumObservableFamilyData action)
    (powers : ScalarCurvaturePowerLocalObservableInterpretationData
      geometry inner connection exterior certificate family basic)
    (g : GaugeGroup) (tag : ScalarCurvaturePowerTag)
    (f : Minkowski.ScalarMinkowskiSchwartzTestFunction d) :
    action.operatorAction g (powers.quantumLabel tag) f =
      family.operator (powers.quantumLabel tag) f :=
  invariance.operator_invariant g _ f

/-- The finite interpretation's `1` label is invariant. -/
theorem quantumGauge_invariant_power_unit
    (invariance : GaugeInvariantQuantumObservableFamilyData action)
    (powers : ScalarCurvaturePowerLocalObservableInterpretationData
      geometry inner connection exterior certificate family basic)
    (g : GaugeGroup) (f : Minkowski.ScalarMinkowskiSchwartzTestFunction d) :
    action.operatorAction g (powers.quantumLabel .unit) f =
      family.operator (powers.quantumLabel .unit) f :=
  quantumGauge_invariant_curvaturePower (basic := basic) invariance powers g .unit f

/-- The finite interpretation's `F²` label is invariant. -/
theorem quantumGauge_invariant_power_curvatureSquared
    (invariance : GaugeInvariantQuantumObservableFamilyData action)
    (powers : ScalarCurvaturePowerLocalObservableInterpretationData
      geometry inner connection exterior certificate family basic)
    (g : GaugeGroup) (f : Minkowski.ScalarMinkowskiSchwartzTestFunction d) :
    action.operatorAction g (powers.quantumLabel .curvatureSquared) f =
      family.operator (powers.quantumLabel .curvatureSquared) f :=
  quantumGauge_invariant_curvaturePower (basic := basic) invariance powers g .curvatureSquared f

/-- The finite interpretation's `(F²)²` label is invariant. -/
theorem quantumGauge_invariant_power_curvatureQuartic
    (invariance : GaugeInvariantQuantumObservableFamilyData action)
    (powers : ScalarCurvaturePowerLocalObservableInterpretationData
      geometry inner connection exterior certificate family basic)
    (g : GaugeGroup) (f : Minkowski.ScalarMinkowskiSchwartzTestFunction d) :
    action.operatorAction g (powers.quantumLabel .curvatureQuartic) f =
      family.operator (powers.quantumLabel .curvatureQuartic) f :=
  quantumGauge_invariant_curvaturePower (basic := basic) invariance powers g .curvatureQuartic f

end

end YangMills.Observables
