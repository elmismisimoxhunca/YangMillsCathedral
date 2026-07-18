/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Minkowski.WightmanField

/-!
# Hostile probes for scalar Wightman fields on the common domain

The probes force a nonzero Minkowski test, exact common-domain preservation, coherent tempered
matrix elements, and the conjugated-test adjoint relation. Every field datum remains hypothetical.
-/

namespace YangMills.Minkowski.WightmanField.Probes

variable
    {d : EuclideanDimension} {G : Type*}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {lift : ProperOrthochronousPoincareLiftData d G}
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H]
    {U : StronglyContinuousUnitaryPoincareRepresentation lift H}
    {vacuumData : PoincareInvariantVacuumData U}
    {D : CommonInvariantDomainData vacuumData}

/-- The Minkowski scalar test carrier contains an explicit function with value one at zero. -/
theorem explicit_test_value_one : scalarMinkowskiSchwartzBump d 0 = 1 :=
  scalarMinkowskiSchwartzBump_zero d

/-- The explicit Minkowski scalar test is genuinely nonzero. -/
theorem explicit_test_ne_zero : scalarMinkowskiSchwartzBump d ≠ 0 :=
  scalarMinkowskiSchwartzBump_ne_zero d

/-- Field application remains in the exact same common domain. -/
theorem field_preserves_exact_domain
    (fieldData : ScalarWightmanFieldOnCommonDomainData D)
    (f : ScalarMinkowskiSchwartzTestFunction d) (ψ : D.domain) :
    (fieldData.field f ψ).val ∈ D.domain :=
  (fieldData.field f ψ).property

/-- Adjoint-field application also remains in that exact domain. -/
theorem adjointField_preserves_exact_domain
    (fieldData : ScalarWightmanFieldOnCommonDomainData D)
    (f : ScalarMinkowskiSchwartzTestFunction d) (ψ : D.domain) :
    (fieldData.adjointField f ψ).val ∈ D.domain :=
  (fieldData.adjointField f ψ).property

/-- The tempered matrix element at the explicit nonzero test is tied to the exact field operator. -/
theorem bump_matrixElement_exact
    (fieldData : ScalarWightmanFieldOnCommonDomainData D) (ψ φ : D.domain) :
    fieldData.matrixElement ψ φ (scalarMinkowskiSchwartzBump d) =
      @inner ℂ H _ ψ.val (fieldData.field (scalarMinkowskiSchwartzBump d) φ).val :=
  fieldData.matrixElement_coherent ψ φ (scalarMinkowskiSchwartzBump d)

/-- The adjoint matrix element is tied to the exact adjoint operator. -/
theorem bump_adjointMatrixElement_exact
    (fieldData : ScalarWightmanFieldOnCommonDomainData D) (ψ φ : D.domain) :
    fieldData.adjointMatrixElement ψ φ (scalarMinkowskiSchwartzBump d) =
      @inner ℂ H _ ψ.val
        (fieldData.adjointField (scalarMinkowskiSchwartzBump d) φ).val :=
  fieldData.adjointMatrixElement_coherent ψ φ (scalarMinkowskiSchwartzBump d)

/-- The exact conjugated-test adjoint relation is exposed on every common-domain pair. -/
theorem exact_adjoint_relation
    (fieldData : ScalarWightmanFieldOnCommonDomainData D)
    (ψ φ : D.domain) (f : ScalarMinkowskiSchwartzTestFunction d) :
    @inner ℂ H _ ψ.val (fieldData.adjointField f φ).val =
      @inner ℂ H _
        (fieldData.field (conjugateScalarMinkowskiSchwartzTestFunction f) ψ).val φ.val :=
  fieldData.adjoint_relation ψ φ f

/-- Replacing a coherent matrix element by a different scalar is impossible. -/
theorem disconnected_matrixElement_blocked
    (fieldData : ScalarWightmanFieldOnCommonDomainData D)
    (ψ φ : D.domain) (f : ScalarMinkowskiSchwartzTestFunction d) (z : ℂ)
    (hreplacement : fieldData.matrixElement ψ φ f = z)
    (hmismatch : z ≠ @inner ℂ H _ ψ.val (fieldData.field f φ).val) : False := by
  apply hmismatch
  rw [← fieldData.matrixElement_coherent ψ φ f]
  exact hreplacement.symm

/-- Conjugation is genuinely involutive on the exact Minkowski Schwartz carrier. -/
theorem exact_test_conjugation_involution
    (f : ScalarMinkowskiSchwartzTestFunction d) :
    conjugateScalarMinkowskiSchwartzTestFunction
      (conjugateScalarMinkowskiSchwartzTestFunction f) = f :=
  conjugateScalarMinkowskiSchwartzTestFunction_involutive f

end YangMills.Minkowski.WightmanField.Probes
