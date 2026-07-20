/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Minkowski.TemperedLocalObservableProducts

/-!
# Independent quantum gauge action on local observables

Clay/Jaffe--Witten §4 requires local quantum observables corresponding to gauge-invariant local
polynomials. This module makes the quantum gauge action independent of classical same-family
interpretation transport: a gauge group acts algebraically on the exact common invariant domain,
and hence by conjugation on its endomorphisms. Gauge invariance is then an explicit strengthening
for every label and every smearing test.

No action is constructed, and no unitarity, continuity, nontrivial gauge element, quantum theory, or
mass gap is asserted. The algebraic domain representation and conjugation carrier are project
formalization choices supporting the source-facing invariance requirement.
-/

namespace YangMills.Observables

open YangMills.Minkowski

/-- An algebraic gauge-group representation on the exact common invariant domain. -/
structure QuantumGaugeObservableActionData
    {d : EuclideanDimension} {PoincareGroup : Type*}
    [Group PoincareGroup] [TopologicalSpace PoincareGroup] [IsTopologicalGroup PoincareGroup]
    {lift : ProperOrthochronousPoincareLiftData d PoincareGroup}
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H]
    {U : StronglyContinuousUnitaryPoincareRepresentation lift H}
    {vacuumData : PoincareInvariantVacuumData U}
    {D : CommonInvariantDomainData vacuumData}
    (GaugeGroup : Type*) [Group GaugeGroup]
    (_family : TemperedLocalObservableFamilyData D) where
  /-- Exact algebraic action on the common domain; no unitarity or continuity is implied. -/
  domainAction : GaugeGroup →* (D.domain ≃ₗ[ℂ] D.domain)

namespace QuantumGaugeObservableActionData

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

/-- Conjugation action on arbitrary endomorphisms of the exact domain. -/
noncomputable def conjugate
    (data : QuantumGaugeObservableActionData GaugeGroup family)
    (g : GaugeGroup) (operator : Module.End ℂ D.domain) : Module.End ℂ D.domain :=
  (data.domainAction g).toLinearMap.comp
    (operator.comp (data.domainAction g⁻¹).toLinearMap)

/-- Quantum gauge action on a smeared member of the observable family. -/
noncomputable def operatorAction
    (data : QuantumGaugeObservableActionData GaugeGroup family)
    (g : GaugeGroup) (A : family.Label)
    (f : ScalarMinkowskiSchwartzTestFunction d) : Module.End ℂ D.domain :=
  data.conjugate g (family.operator A f)

@[simp] theorem conjugate_one
    (data : QuantumGaugeObservableActionData GaugeGroup family)
    (operator : Module.End ℂ D.domain) :
    data.conjugate 1 operator = operator := by
  ext ψ
  simp [conjugate]

@[simp] theorem conjugate_mul
    (data : QuantumGaugeObservableActionData GaugeGroup family)
    (first second : GaugeGroup) (operator : Module.End ℂ D.domain) :
    data.conjugate (first * second) operator =
      data.conjugate first (data.conjugate second operator) := by
  ext ψ
  simp [conjugate]

/-- Group multiplication acts by nested conjugation in the same order. -/
theorem operatorAction_mul
    (data : QuantumGaugeObservableActionData GaugeGroup family)
    (first second : GaugeGroup) (A : family.Label)
    (f : ScalarMinkowskiSchwartzTestFunction d) :
    data.operatorAction (first * second) A f =
      data.conjugate first (data.operatorAction second A f) :=
  data.conjugate_mul first second _

@[simp] theorem operatorAction_one
    (data : QuantumGaugeObservableActionData GaugeGroup family)
    (A : family.Label) (f : ScalarMinkowskiSchwartzTestFunction d) :
    data.operatorAction 1 A f = family.operator A f :=
  data.conjugate_one _

/-- Explicit pointwise conjugation formula, retaining the inverse on the input state. -/
theorem operatorAction_apply
    (data : QuantumGaugeObservableActionData GaugeGroup family)
    (g : GaugeGroup) (A : family.Label)
    (f : ScalarMinkowskiSchwartzTestFunction d) (ψ : D.domain) :
    data.operatorAction g A f ψ =
      data.domainAction g (family.operator A f (data.domainAction g⁻¹ ψ)) := rfl

end QuantumGaugeObservableActionData

/-- Gauge invariance of every smeared operator under one exact, independently designated quantum
gauge action. Taking the action as a parameter prevents this certificate from silently replacing it
with a disconnected convenient action. -/
structure GaugeInvariantQuantumObservableFamilyData
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
    (action : QuantumGaugeObservableActionData GaugeGroup family) where
  /-- Every label and smearing is fixed by the exact designated quantum gauge action. -/
  operator_invariant : ∀ g A f,
    action.operatorAction g A f = family.operator A f

namespace GaugeInvariantQuantumObservableFamilyData

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

/-- Pointwise invariance on the exact common domain. -/
theorem operator_invariant_apply
    (data : GaugeInvariantQuantumObservableFamilyData action)
    (g : GaugeGroup) (A : family.Label)
    (f : ScalarMinkowskiSchwartzTestFunction d) (ψ : D.domain) :
    action.domainAction g
      (family.operator A f (action.domainAction g⁻¹ ψ)) =
      family.operator A f ψ := by
  exact LinearMap.congr_fun (data.operator_invariant g A f) ψ

/-- The distinguished unit operator is invariant as a consequence of all-label invariance. -/
theorem unit_operator_invariant
    (data : GaugeInvariantQuantumObservableFamilyData action)
    (g : GaugeGroup) (f : ScalarMinkowskiSchwartzTestFunction d) :
    action.operatorAction g family.unitLabel f =
      family.operator family.unitLabel f :=
  data.operator_invariant g family.unitLabel f

/-- The required nontrivial label is connected to the same all-label invariance law. -/
theorem nontrivial_operator_invariant
    (data : GaugeInvariantQuantumObservableFamilyData action)
    (g : GaugeGroup) (f : ScalarMinkowskiSchwartzTestFunction d) :
    action.operatorAction g family.nontrivialLabel f =
      family.operator family.nontrivialLabel f :=
  data.operator_invariant g family.nontrivialLabel f

end GaugeInvariantQuantumObservableFamilyData

end YangMills.Observables
