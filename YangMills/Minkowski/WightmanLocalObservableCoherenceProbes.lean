/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Minkowski.WightmanLocalObservableCoherence

/-! Hostile probes for exact Wightman/local-observable operator coherence. -/

namespace YangMills.Minkowski.WightmanLocalObservableCoherence.Probes

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

/-- The Wightman field is the exact existing nontrivial family operator. -/
theorem exact_field_operator
    (coherence : ScalarWightmanFieldLocalObservableCoherenceData
      fieldData family covariantFamily) :
    family.operator family.nontrivialLabel = fieldData.field :=
  coherence.field_operator

/-- The Wightman adjoint uses the exact adjoint label in the same family. -/
theorem exact_adjoint_operator
    (coherence : ScalarWightmanFieldLocalObservableCoherenceData
      fieldData family covariantFamily) :
    family.operator (covariantFamily.adjointLabel family.nontrivialLabel) =
      fieldData.adjointField :=
  coherence.adjoint_operator

/-- The selected field and adjoint labels are both separated from the unit label. -/
theorem exact_nonunit_labels
    (coherence : ScalarWightmanFieldLocalObservableCoherenceData
      fieldData family covariantFamily) :
    family.nontrivialLabel ≠ family.unitLabel ∧
      covariantFamily.adjointLabel family.nontrivialLabel ≠ family.unitLabel :=
  ⟨family.nontrivialLabel_ne_unit, coherence.adjointLabel_nontrivial_ne_unit⟩

/-- Exact operator coherence propagates to the already-tempered matrix-element distributions. -/
theorem exact_matrix_elements
    (coherence : ScalarWightmanFieldLocalObservableCoherenceData
      fieldData family covariantFamily)
    (bra ket : D.domain) :
    family.matrixElement family.nontrivialLabel bra ket = fieldData.matrixElement bra ket ∧
      family.matrixElement (covariantFamily.adjointLabel family.nontrivialLabel) bra ket =
        fieldData.adjointMatrixElement bra ket :=
  ⟨coherence.matrixElement_eq bra ket, coherence.adjointMatrixElement_eq bra ket⟩

/-- Family anti-vacuity forces the coherently selected Wightman field itself to act nontrivially. -/
theorem exact_nontrivial_field
    (coherence : ScalarWightmanFieldLocalObservableCoherenceData
      fieldData family covariantFamily) :
    ∃ (test : ScalarMinkowskiSchwartzTestFunction d) (vector : D.domain),
      fieldData.field test vector ≠ 0 ∧
      fieldData.field test vector ≠ family.operator family.unitLabel test vector :=
  coherence.field_nontrivial_witness

/-- A disconnected field operator cannot be substituted for the selected family operator. -/
theorem disconnected_field_blocked
    (coherence : ScalarWightmanFieldLocalObservableCoherenceData
      fieldData family covariantFamily)
    (wrong : ScalarMinkowskiSchwartzTestFunction d →ₗ[ℂ] Module.End ℂ D.domain)
    (different : wrong ≠ family.operator family.nontrivialLabel)
    (claimed : wrong = fieldData.field) : False := by
  apply different
  rw [claimed, ← coherence.field_operator]

/-- A disconnected adjoint operator cannot be substituted for the exact adjoint-family label. -/
theorem disconnected_adjoint_blocked
    (coherence : ScalarWightmanFieldLocalObservableCoherenceData
      fieldData family covariantFamily)
    (wrong : ScalarMinkowskiSchwartzTestFunction d →ₗ[ℂ] Module.End ℂ D.domain)
    (different : wrong ≠
      family.operator (covariantFamily.adjointLabel family.nontrivialLabel))
    (claimed : wrong = fieldData.adjointField) : False := by
  apply different
  rw [claimed, ← coherence.adjoint_operator]

end YangMills.Minkowski.WightmanLocalObservableCoherence.Probes
