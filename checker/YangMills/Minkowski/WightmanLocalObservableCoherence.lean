/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Minkowski.CovariantLocalObservableFamily

/-!
# Coherence between one Wightman field and a local-observable family

A scalar Wightman field and a covariant local-observable family can share a representation, vacuum,
and common invariant domain while still describing disconnected operator sectors. This module
prevents that gap: the Wightman field is required to be exactly the family's already nontrivial
label, and its adjoint is exactly the operator at the corresponding adjoint label.

The coherence record adds no field, operator, matrix element, covariance, locality, theory, or mass
gap. It only identifies objects already indexed by one exact physical chain.
-/

namespace YangMills.Minkowski

/-- Exact operator-level identification of a scalar Wightman field with the distinguished nontrivial
label of one covariant local-observable family on the same common domain. -/
structure ScalarWightmanFieldLocalObservableCoherenceData
    {d : EuclideanDimension} {PoincareLiftGroup : Type*}
    [Group PoincareLiftGroup] [TopologicalSpace PoincareLiftGroup]
    [IsTopologicalGroup PoincareLiftGroup]
    {lift : ProperOrthochronousPoincareLiftData d PoincareLiftGroup}
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H]
    {U : StronglyContinuousUnitaryPoincareRepresentation lift H}
    {vacuumData : PoincareInvariantVacuumData U}
    {D : CommonInvariantDomainData vacuumData}
    (fieldData : ScalarWightmanFieldOnCommonDomainData D)
    (family : TemperedLocalObservableFamilyData D)
    (covariantFamily : CovariantLocalObservableFamilyData family) : Prop where
  /-- The exact Wightman field is the family's existing nontrivial operator label. -/
  field_operator : family.operator family.nontrivialLabel = fieldData.field
  /-- The exact Wightman adjoint is the operator at the same family's adjoint label. -/
  adjoint_operator :
    family.operator (covariantFamily.adjointLabel family.nontrivialLabel) =
      fieldData.adjointField

namespace ScalarWightmanFieldLocalObservableCoherenceData

variable
    {d : EuclideanDimension} {PoincareLiftGroup : Type*}
    [Group PoincareLiftGroup] [TopologicalSpace PoincareLiftGroup]
    [IsTopologicalGroup PoincareLiftGroup]
    {lift : ProperOrthochronousPoincareLiftData d PoincareLiftGroup}
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H]
    {U : StronglyContinuousUnitaryPoincareRepresentation lift H}
    {vacuumData : PoincareInvariantVacuumData U}
    {D : CommonInvariantDomainData vacuumData}
    {fieldData : ScalarWightmanFieldOnCommonDomainData D}
    {family : TemperedLocalObservableFamilyData D}
    {covariantFamily : CovariantLocalObservableFamilyData family}

/-- Pointwise field action is exactly the selected local-observable action. -/
theorem field_apply
    (coherence : ScalarWightmanFieldLocalObservableCoherenceData
      fieldData family covariantFamily)
    (test : ScalarMinkowskiSchwartzTestFunction d) (vector : D.domain) :
    family.operator family.nontrivialLabel test vector = fieldData.field test vector := by
  rw [coherence.field_operator]

/-- Pointwise adjoint action is exactly the action at the selected adjoint label. -/
theorem adjoint_apply
    (coherence : ScalarWightmanFieldLocalObservableCoherenceData
      fieldData family covariantFamily)
    (test : ScalarMinkowskiSchwartzTestFunction d) (vector : D.domain) :
    family.operator (covariantFamily.adjointLabel family.nontrivialLabel) test vector =
      fieldData.adjointField test vector := by
  rw [coherence.adjoint_operator]

/-- The selected adjoint label cannot be the unit label. This follows from involutivity and the
existing nontrivial-label separation, rather than a label-injectivity assumption. -/
theorem adjointLabel_nontrivial_ne_unit
    (_coherence : ScalarWightmanFieldLocalObservableCoherenceData
      fieldData family covariantFamily) :
    covariantFamily.adjointLabel family.nontrivialLabel ≠ family.unitLabel := by
  intro equality
  have after_adjoint := congrArg covariantFamily.adjointLabel equality
  rw [covariantFamily.adjointLabel_involutive,
    covariantFamily.adjointLabel_unit] at after_adjoint
  exact family.nontrivialLabel_ne_unit after_adjoint

/-- Family matrix elements at the selected label are the exact Wightman-field matrix elements. -/
theorem matrixElement_eq
    (coherence : ScalarWightmanFieldLocalObservableCoherenceData
      fieldData family covariantFamily)
    (bra ket : D.domain) :
    family.matrixElement family.nontrivialLabel bra ket = fieldData.matrixElement bra ket := by
  ext test
  rw [family.matrixElement_coherent, fieldData.matrixElement_coherent,
    coherence.field_apply]

/-- Family matrix elements at the adjoint label are the exact Wightman-adjoint matrix elements. -/
theorem adjointMatrixElement_eq
    (coherence : ScalarWightmanFieldLocalObservableCoherenceData
      fieldData family covariantFamily)
    (bra ket : D.domain) :
    family.matrixElement (covariantFamily.adjointLabel family.nontrivialLabel) bra ket =
      fieldData.adjointMatrixElement bra ket := by
  ext test
  rw [family.matrixElement_coherent, fieldData.adjointMatrixElement_coherent,
    coherence.adjoint_apply]

/-- Existing family anti-vacuity transfers to the exact Wightman field: at one test/vector it is
nonzero and differs from the smeared unit. -/
theorem field_nontrivial_witness
    (coherence : ScalarWightmanFieldLocalObservableCoherenceData
      fieldData family covariantFamily) :
    ∃ (test : ScalarMinkowskiSchwartzTestFunction d) (vector : D.domain),
      fieldData.field test vector ≠ 0 ∧
      fieldData.field test vector ≠ family.operator family.unitLabel test vector := by
  rcases family.nontrivial_operator_witness with ⟨test, vector, nonzero, nonunit⟩
  refine ⟨test, vector, ?_, ?_⟩
  · rwa [← coherence.field_apply]
  · rwa [← coherence.field_apply]

end ScalarWightmanFieldLocalObservableCoherenceData

end YangMills.Minkowski
