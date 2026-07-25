/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Minkowski.WightmanField

/-!
# Vacuum cyclicity for scalar Wightman fields

Streater–Wightman, printed pp. 100–101, explains that trivial constant fields satisfy the preceding
field axioms and requires a field theory to have a vacuum cyclic for polynomials in smeared fields.
This module constructs exact finite words from the field and adjoint on the common domain, applies
them to the same domain vacuum, takes their complex linear span in the physical Hilbert space, and
requires its topological closure to be all of that Hilbert space.

No cyclic field datum or Wightman theory inhabitant is constructed.
-/

namespace YangMills.Minkowski

/-- One letter in a polynomial word: either the field or its adjoint, smeared by one exact Minkowski
Schwartz test. -/
inductive ScalarWightmanFieldLetter (d : EuclideanDimension) where
  | field (test : ScalarMinkowskiSchwartzTestFunction d)
  | adjoint (test : ScalarMinkowskiSchwartzTestFunction d)

/-- Apply one field/adjoint letter to an exact common-domain vector. -/
noncomputable def ScalarWightmanFieldLetter.apply
    {d : EuclideanDimension} {G : Type*}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {lift : ProperOrthochronousPoincareLiftData d G}
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H]
    {U : StronglyContinuousUnitaryPoincareRepresentation lift H}
    {vacuumData : PoincareInvariantVacuumData U}
    {D : CommonInvariantDomainData vacuumData}
    (fieldData : ScalarWightmanFieldOnCommonDomainData D)
    (letter : ScalarWightmanFieldLetter d) (ψ : D.domain) : D.domain :=
  match letter with
  | .field f => fieldData.field f ψ
  | .adjoint f => fieldData.adjointField f ψ

/-- Apply a finite field word to the same selected domain vacuum. The list head acts after the tail,
matching ordinary operator-product notation. -/
noncomputable def scalarWightmanFieldWordOnVacuum
    {d : EuclideanDimension} {G : Type*}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {lift : ProperOrthochronousPoincareLiftData d G}
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H]
    {U : StronglyContinuousUnitaryPoincareRepresentation lift H}
    {vacuumData : PoincareInvariantVacuumData U}
    {D : CommonInvariantDomainData vacuumData}
    (fieldData : ScalarWightmanFieldOnCommonDomainData D) :
    List (ScalarWightmanFieldLetter d) → D.domain
  | [] => D.vacuumInDomain
  | letter :: word => letter.apply fieldData (scalarWightmanFieldWordOnVacuum fieldData word)

@[simp] theorem scalarWightmanFieldWordOnVacuum_nil
    {d : EuclideanDimension} {G : Type*}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {lift : ProperOrthochronousPoincareLiftData d G}
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H]
    {U : StronglyContinuousUnitaryPoincareRepresentation lift H}
    {vacuumData : PoincareInvariantVacuumData U}
    {D : CommonInvariantDomainData vacuumData}
    (fieldData : ScalarWightmanFieldOnCommonDomainData D) :
    scalarWightmanFieldWordOnVacuum fieldData [] = D.vacuumInDomain :=
  rfl

/-- The Hilbert-space submodule spanned by all finite field/adjoint words on the selected vacuum. -/
noncomputable def scalarWightmanFieldPolynomialVacuumSubmodule
    {d : EuclideanDimension} {G : Type*}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {lift : ProperOrthochronousPoincareLiftData d G}
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H]
    {U : StronglyContinuousUnitaryPoincareRepresentation lift H}
    {vacuumData : PoincareInvariantVacuumData U}
    {D : CommonInvariantDomainData vacuumData}
    (fieldData : ScalarWightmanFieldOnCommonDomainData D) : Submodule ℂ H :=
  Submodule.span ℂ (Set.range (fun word =>
    (scalarWightmanFieldWordOnVacuum fieldData word).val))

/-- The selected vacuum belongs to the exact polynomial-vacuum span via the empty word. -/
theorem vacuum_mem_scalarWightmanFieldPolynomialVacuumSubmodule
    {d : EuclideanDimension} {G : Type*}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {lift : ProperOrthochronousPoincareLiftData d G}
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H]
    {U : StronglyContinuousUnitaryPoincareRepresentation lift H}
    {vacuumData : PoincareInvariantVacuumData U}
    {D : CommonInvariantDomainData vacuumData}
    (fieldData : ScalarWightmanFieldOnCommonDomainData D) :
    vacuumData.vacuum ∈ scalarWightmanFieldPolynomialVacuumSubmodule fieldData := by
  apply Submodule.subset_span
  exact ⟨[], rfl⟩

/-- Vacuum cyclicity: the closure of the exact polynomial-vacuum submodule is the whole physical
Hilbert space. -/
def ScalarWightmanVacuumCyclicity
    {d : EuclideanDimension} {G : Type*}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {lift : ProperOrthochronousPoincareLiftData d G}
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H]
    {U : StronglyContinuousUnitaryPoincareRepresentation lift H}
    {vacuumData : PoincareInvariantVacuumData U}
    {D : CommonInvariantDomainData vacuumData}
    (fieldData : ScalarWightmanFieldOnCommonDomainData D) : Prop :=
  (scalarWightmanFieldPolynomialVacuumSubmodule fieldData).topologicalClosure = ⊤

end YangMills.Minkowski
