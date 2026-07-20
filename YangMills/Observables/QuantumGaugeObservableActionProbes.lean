/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Observables.QuantumGaugeObservableAction

namespace YangMills.Observables.QuantumGaugeObservableAction.Probes

open YangMills.Minkowski

variable
    {d : EuclideanDimension} {PoincareGroup : Type*}
    [Group PoincareGroup] [TopologicalSpace PoincareGroup] [IsTopologicalGroup PoincareGroup]
    {lift : ProperOrthochronousPoincareLiftData d PoincareGroup}
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H]
    {U : StronglyContinuousUnitaryPoincareRepresentation lift H}
    {vacuumData : PoincareInvariantVacuumData U}
    {D : CommonInvariantDomainData vacuumData}
    {GaugeGroup : Type*} [Group GaugeGroup]
    {family : TemperedLocalObservableFamilyData D}
    {action : QuantumGaugeObservableActionData GaugeGroup family}

/-- The independent action is exact conjugation on the common domain. -/
theorem exact_operator_action
    (data : QuantumGaugeObservableActionData GaugeGroup family)
    (g : GaugeGroup) (A : family.Label)
    (f : ScalarMinkowskiSchwartzTestFunction d) (ψ : D.domain) :
    data.operatorAction g A f ψ =
      data.domainAction g (family.operator A f (data.domainAction g⁻¹ ψ)) :=
  data.operatorAction_apply g A f ψ

/-- Identity acts as the unchanged operator. -/
theorem exact_action_identity
    (data : QuantumGaugeObservableActionData GaugeGroup family)
    (A : family.Label) (f : ScalarMinkowskiSchwartzTestFunction d) :
    data.operatorAction 1 A f = family.operator A f :=
  data.operatorAction_one A f

/-- Multiplication order is fixed by nested conjugation. -/
theorem exact_action_composition
    (data : QuantumGaugeObservableActionData GaugeGroup family)
    (first second : GaugeGroup) (A : family.Label)
    (f : ScalarMinkowskiSchwartzTestFunction d) :
    data.operatorAction (first * second) A f =
      data.conjugate first (data.operatorAction second A f) :=
  data.operatorAction_mul first second A f

/-- Invariance ranges over every label, not merely the unit or interpreted fragment. -/
theorem every_label_gauge_invariant
    (data : GaugeInvariantQuantumObservableFamilyData action)
    (g : GaugeGroup) (A : family.Label)
    (f : ScalarMinkowskiSchwartzTestFunction d) :
    action.operatorAction g A f = family.operator A f :=
  data.operator_invariant g A f

/-- A changed operator contradicts invariance under the exact designated action. -/
theorem changed_operator_blocked
    (data : GaugeInvariantQuantumObservableFamilyData action)
    (g : GaugeGroup) (A : family.Label)
    (f : ScalarMinkowskiSchwartzTestFunction d)
    (changed : action.operatorAction g A f ≠ family.operator A f) : False :=
  changed (data.operator_invariant g A f)

/-- The explicitly nontrivial label remains connected to the same invariance law. -/
theorem nontrivial_label_connected
    (data : GaugeInvariantQuantumObservableFamilyData action)
    (g : GaugeGroup) (f : ScalarMinkowskiSchwartzTestFunction d) :
    action.operatorAction g family.nontrivialLabel f =
      family.operator family.nontrivialLabel f :=
  data.nontrivial_operator_invariant g f

end YangMills.Observables.QuantumGaugeObservableAction.Probes
