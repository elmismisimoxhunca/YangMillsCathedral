/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Observables.QuantumGaugeCurvaturePowerCoherence

namespace YangMills.Observables.QuantumGaugeCurvaturePowerCoherence.Probes

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

omit [FiniteDimensional ℝ EB] in
/-- The exact interpreted basic `F²` label is covered, not an unrelated family label. -/
theorem exact_basic_curvatureSquared
    (invariance : GaugeInvariantQuantumObservableFamilyData action)
    (g : GaugeGroup) (f : Minkowski.ScalarMinkowskiSchwartzTestFunction d) :
    action.operatorAction g (basic.quantumLabel .curvatureSquared) f =
      family.operator (basic.quantumLabel .curvatureSquared) f :=
  quantumGauge_invariant_basic_curvatureSquared basic invariance g f

/-- Every member of the exact finite interpretation is covered. -/
theorem exact_finite_fragment
    (invariance : GaugeInvariantQuantumObservableFamilyData action)
    (powers : ScalarCurvaturePowerLocalObservableInterpretationData
      geometry inner connection exterior certificate family basic)
    (g : GaugeGroup) (tag : ScalarCurvaturePowerTag)
    (f : Minkowski.ScalarMinkowskiSchwartzTestFunction d) :
    action.operatorAction g (powers.quantumLabel tag) f =
      family.operator (powers.quantumLabel tag) f :=
  quantumGauge_invariant_curvaturePower (basic := basic) invariance powers g tag f

/-- The new quartic label is explicitly connected to the designated quantum action. -/
theorem exact_curvatureQuartic
    (invariance : GaugeInvariantQuantumObservableFamilyData action)
    (powers : ScalarCurvaturePowerLocalObservableInterpretationData
      geometry inner connection exterior certificate family basic)
    (g : GaugeGroup) (f : Minkowski.ScalarMinkowskiSchwartzTestFunction d) :
    action.operatorAction g (powers.quantumLabel .curvatureQuartic) f =
      family.operator (powers.quantumLabel .curvatureQuartic) f :=
  quantumGauge_invariant_power_curvatureQuartic (basic := basic) invariance powers g f

/-- Changing the quartic operator contradicts exact-action invariance. -/
theorem changed_curvatureQuartic_blocked
    (invariance : GaugeInvariantQuantumObservableFamilyData action)
    (powers : ScalarCurvaturePowerLocalObservableInterpretationData
      geometry inner connection exterior certificate family basic)
    (g : GaugeGroup) (f : Minkowski.ScalarMinkowskiSchwartzTestFunction d)
    (changed : action.operatorAction g (powers.quantumLabel .curvatureQuartic) f ≠
      family.operator (powers.quantumLabel .curvatureQuartic) f) : False :=
  changed (quantumGauge_invariant_power_curvatureQuartic
    (basic := basic) invariance powers g f)

/-- A different action at the interpreted quartic operator cannot use this exact-action certificate. -/
theorem unrelated_action_substitution_blocked
    (invariance : GaugeInvariantQuantumObservableFamilyData action)
    (powers : ScalarCurvaturePowerLocalObservableInterpretationData
      geometry inner connection exterior certificate family basic)
    (other : QuantumGaugeObservableActionData GaugeGroup family)
    (g : GaugeGroup) (f : Minkowski.ScalarMinkowskiSchwartzTestFunction d)
    (different : other.operatorAction g (powers.quantumLabel .curvatureQuartic) f ≠
      action.operatorAction g (powers.quantumLabel .curvatureQuartic) f) :
    other.operatorAction g (powers.quantumLabel .curvatureQuartic) f ≠
      family.operator (powers.quantumLabel .curvatureQuartic) f := by
  intro otherInvariant
  apply different
  rw [otherInvariant]
  symm
  exact quantumGauge_invariant_power_curvatureQuartic
    (basic := basic) invariance powers g f

end

end YangMills.Observables.QuantumGaugeCurvaturePowerCoherence.Probes
