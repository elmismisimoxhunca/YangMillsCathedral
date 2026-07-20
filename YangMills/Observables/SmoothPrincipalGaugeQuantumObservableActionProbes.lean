/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Observables.SmoothPrincipalGaugeQuantumObservableAction

namespace YangMills.Observables.SmoothPrincipalGaugeQuantumObservableAction.Probes

open YangMills.Minkowski
open scoped Manifold ContDiff

universe uEG uHG uEB uHB uEP uHP uG uB uP

variable
    {EG : Type uEG} {HG : Type uHG}
    [NormedAddCommGroup EG] [NormedSpace ℝ EG] [TopologicalSpace HG]
    {EB : Type uEB} {HB : Type uHB}
    [NormedAddCommGroup EB] [NormedSpace ℝ EB] [TopologicalSpace HB]
    {EP : Type uEP} {HP : Type uHP}
    [NormedAddCommGroup EP] [NormedSpace ℝ EP] [TopologicalSpace HP]
    {G : Type uG} {B : Type uB} {P : Type uP}
    [Group G] [TopologicalSpace G] [TopologicalSpace B] [TopologicalSpace P]
    [IsTopologicalGroup G]
    {IB : ModelWithCorners ℝ EB HB} {IG : ModelWithCorners ℝ EG HG}
    {IP : ModelWithCorners ℝ EP HP}
    [ChartedSpace HB B] [IsManifold IB ∞ B]
    [ChartedSpace HG G] [LieGroup IG ∞ G]
    [ChartedSpace HP P] [IsManifold IP ∞ P]
    {torsor : Geometry.PrincipalBundleTorsorData G B P}
    {bundle : Geometry.TopologicalPrincipalBundleData torsor}
    (smoothBundle : Geometry.SmoothPrincipalBundleData IB IG IP torsor bundle)
    {d : EuclideanDimension} {PoincareGroup : Type*}
    [Group PoincareGroup] [TopologicalSpace PoincareGroup] [IsTopologicalGroup PoincareGroup]
    {lift : ProperOrthochronousPoincareLiftData d PoincareGroup}
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H]
    {U : StronglyContinuousUnitaryPoincareRepresentation lift H}
    {vacuumData : PoincareInvariantVacuumData U}
    {D : CommonInvariantDomainData vacuumData}
    (family : TemperedLocalObservableFamilyData D)

/-- The operator action is indexed by an actual smooth automorphism of the exact bundle. -/
theorem exact_smooth_principal_gauge_action
    (action : SmoothPrincipalGaugeQuantumObservableActionData smoothBundle family)
    (g : Geometry.SmoothGaugeTransformation smoothBundle) (A : family.Label)
    (f : ScalarMinkowskiSchwartzTestFunction d) (ψ : D.domain) :
    action.operatorAction g A f ψ =
      action.domainAction g (family.operator A f (action.domainAction g⁻¹ ψ)) :=
  action.operatorAction_apply g A f ψ

/-- A changed operator is rejected under the exact designated smooth-gauge action. -/
theorem changed_smooth_principal_gauge_operator_blocked
    (action : SmoothPrincipalGaugeQuantumObservableActionData smoothBundle family)
    (invariance : SmoothPrincipalGaugeInvariantQuantumObservableFamilyData
      smoothBundle family action)
    (g : Geometry.SmoothGaugeTransformation smoothBundle) (A : family.Label)
    (f : ScalarMinkowskiSchwartzTestFunction d)
    (changed : action.operatorAction g A f ≠ family.operator A f) : False :=
  changed (invariance.operator_invariant g A f)

end YangMills.Observables.SmoothPrincipalGaugeQuantumObservableAction.Probes
