/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Mathematics.CompactRepresentationExplicitUnitarization
import YangMills.Mathematics.UnitaryMatrixDual

/-!
# Unitary-coordinate realization of continuous irreducible matrix representations

Explicit Haar unitarization applies to every continuous finite complex matrix representation, but
the coordinate unitary dual additionally requires irreducibility. This file proves, as reusable
representation theory, that an exact `Representation.Equiv` induces a group-algebra module linear
equivalence and therefore preserves irreducibility.

It then defines a positive-dimensional continuous irreducible matrix representation without an
assumed unitary law and constructs from it an equivalent bundled continuous irreducible unitary
matrix representation. Thus every representation in this explicit matrix class determines a
coordinate-unitary-dual class. This does not realize arbitrary non-coordinate abstract
representations and does not prove Peter–Weyl completeness.
-/

namespace YangMills
namespace Mathematics

open scoped MonoidAlgebra

noncomputable section

universe uG

/-- An exact representation equivalence induces an exact linear equivalence between the associated
group-algebra modules. -/
noncomputable def representationEquivAsModuleLinearEquiv
    {G k V W : Type*} [Monoid G] [Field k]
    [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
    {ρ : Representation k G V} {σ : Representation k G W}
    (equivalence : Representation.Equiv ρ σ) :
    ρ.asModule ≃ₗ[k[G]] σ.asModule :=
  LinearEquiv.ofBijective
    (Representation.IntertwiningMap.equivLinearMapAsModule
      ρ σ equivalence.toIntertwiningMap)
    equivalence.toLinearEquiv.bijective

/-- Irreducibility is invariant under an exact representation equivalence. -/
theorem representation_isIrreducible_iff_of_equiv
    {G k V W : Type*} [Monoid G] [Field k]
    [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
    {ρ : Representation k G V} {σ : Representation k G W}
    (equivalence : Representation.Equiv ρ σ) :
    Representation.IsIrreducible ρ ↔ Representation.IsIrreducible σ := by
  rw [Representation.irreducible_iff_isSimpleModule_asModule,
    Representation.irreducible_iff_isSimpleModule_asModule]
  exact (representationEquivAsModuleLinearEquiv equivalence).isSimpleModule_iff

/-- A positive-dimensional continuous irreducible complex matrix representation, without an
assumed unitary coordinate law. -/
structure ContinuousIrreducibleMatrixRepresentation
    (G : Type uG) [Group G] [TopologicalSpace G] where
  dimension : ℕ
  dimension_pos : 0 < dimension
  representation : G →* Matrix (Fin dimension) (Fin dimension) ℂ
  continuous_representation : Continuous representation
  irreducible_representation : Representation.IsIrreducible
    (matrixRepresentation representation)

/-- Haar averaging and the selected orthonormal coordinates construct an equivalent continuous
irreducible unitary matrix representation from every explicit continuous irreducible matrix
representation. -/
noncomputable def ContinuousIrreducibleMatrixRepresentation.toUnitary
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    (ρ : ContinuousIrreducibleMatrixRepresentation G) :
    ContinuousUnitaryIrreducibleMatrixRepresentation G where
  dimension := ρ.dimension
  dimension_pos := ρ.dimension_pos
  representation := compactRepresentationUnitarizedRepresentation
    ρ.representation ρ.continuous_representation
  continuous_representation := continuous_compactRepresentationUnitarizedRepresentation
    ρ.representation ρ.continuous_representation
  unitary_representation := compactRepresentationUnitarizedRepresentation_unitary
    ρ.representation ρ.continuous_representation
  irreducible_representation := by
    exact (representation_isIrreducible_iff_of_equiv
      (compactRepresentationUnitarizingRepresentationEquiv
        ρ.representation ρ.continuous_representation)).mp
      ρ.irreducible_representation

/-- The constructed unitary-coordinate realization is exactly equivalent to the original
representation. -/
theorem ContinuousIrreducibleMatrixRepresentation.equivalent_toUnitary
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    (ρ : ContinuousIrreducibleMatrixRepresentation G) :
    Nonempty (Representation.Equiv (matrixRepresentation ρ.representation)
      (matrixRepresentation ρ.toUnitary.representation)) :=
  ⟨compactRepresentationUnitarizingRepresentationEquiv
    ρ.representation ρ.continuous_representation⟩

/-- Every explicit continuous irreducible matrix representation therefore determines a class in the
coordinate unitary dual. -/
noncomputable def ContinuousIrreducibleMatrixRepresentation.unitaryDualClass
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    (ρ : ContinuousIrreducibleMatrixRepresentation G) : UnitaryMatrixDual G :=
  unitaryMatrixDualClass ρ.toUnitary

/-- Forgetting the unitary law from an already bundled unitary irreducible representation retains
the same representation, continuity, dimension, and irreducibility data. -/
def ContinuousUnitaryIrreducibleMatrixRepresentation.toContinuousIrreducible
    {G : Type uG} [Group G] [TopologicalSpace G]
    (ρ : ContinuousUnitaryIrreducibleMatrixRepresentation G) :
    ContinuousIrreducibleMatrixRepresentation G where
  dimension := ρ.dimension
  dimension_pos := ρ.dimension_pos
  representation := ρ.representation
  continuous_representation := ρ.continuous_representation
  irreducible_representation := ρ.irreducible_representation

/-- Re-unitarizing an already unitary bundle may select new orthonormal coordinates, but it yields
exactly the same coordinate-unitary-dual class. -/
theorem ContinuousUnitaryIrreducibleMatrixRepresentation.unitaryDualClass_toContinuousIrreducible
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    (ρ : ContinuousUnitaryIrreducibleMatrixRepresentation G) :
    ρ.toContinuousIrreducible.unitaryDualClass = unitaryMatrixDualClass ρ := by
  apply (unitaryMatrixDualClass_eq_iff
    ρ.toContinuousIrreducible.toUnitary ρ).mpr
  exact ⟨(compactRepresentationUnitarizingRepresentationEquiv
    ρ.representation ρ.continuous_representation).symm⟩

end

end Mathematics
end YangMills
