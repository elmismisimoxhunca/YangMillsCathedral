/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Minkowski.ScalarWightmanAxiomSurface

/-!
# Algebraic smeared Wightman vacuum correlators

Wightman 1956 and Streater–Wightman formulate the theory through vacuum expectation values of
ordered products of smeared fields. This module extracts the algebraic smeared correlators from the
exact common-domain field words already defined. The list head remains the leftmost/outermost
operator, and the exact selected normalized vacuum appears in both slots.

These are not yet asserted to be jointly tempered `n`-point distributions, boundary values of tube
analytic functions, or analytic continuations of Schwinger functions. Those are explicit later
bridge obligations. No field or correlator inhabitant is constructed.
-/

namespace YangMills.Minkowski

/-- Vacuum expectation of one exact finite field/adjoint word. -/
noncomputable def scalarWightmanVacuumWordExpectation
    {d : EuclideanDimension} {G : Type*}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {lift : ProperOrthochronousPoincareLiftData d G}
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H]
    {U : StronglyContinuousUnitaryPoincareRepresentation lift H}
    {vacuumData : PoincareInvariantVacuumData U}
    {D : CommonInvariantDomainData vacuumData}
    (fieldData : ScalarWightmanFieldOnCommonDomainData D)
    (word : List (ScalarWightmanFieldLetter d)) : ℂ :=
  inner ℂ vacuumData.vacuum
    ((scalarWightmanFieldWordOnVacuum fieldData word : D.domain) : H)

/-- Ordered field-only smeared vacuum correlator. -/
noncomputable def scalarWightmanVacuumExpectation
    {d : EuclideanDimension} {G : Type*}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {lift : ProperOrthochronousPoincareLiftData d G}
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H]
    {U : StronglyContinuousUnitaryPoincareRepresentation lift H}
    {vacuumData : PoincareInvariantVacuumData U}
    {D : CommonInvariantDomainData vacuumData}
    (fieldData : ScalarWightmanFieldOnCommonDomainData D)
    (tests : List (ScalarMinkowskiSchwartzTestFunction d)) : ℂ :=
  scalarWightmanVacuumWordExpectation fieldData
    (tests.map ScalarWightmanFieldLetter.field)

/-- The empty correlator is the normalized vacuum expectation `1`. -/
@[simp] theorem scalarWightmanVacuumExpectation_nil
    {d : EuclideanDimension} {G : Type*}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {lift : ProperOrthochronousPoincareLiftData d G}
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H]
    {U : StronglyContinuousUnitaryPoincareRepresentation lift H}
    {vacuumData : PoincareInvariantVacuumData U}
    {D : CommonInvariantDomainData vacuumData}
    (fieldData : ScalarWightmanFieldOnCommonDomainData D) :
    scalarWightmanVacuumExpectation fieldData [] = 1 := by
  rw [scalarWightmanVacuumExpectation, scalarWightmanVacuumWordExpectation]
  simp only [List.map_nil, scalarWightmanFieldWordOnVacuum_nil]
  rw [show ((D.vacuumInDomain : D.domain) : H) = vacuumData.vacuum from rfl]
  rw [inner_self_eq_norm_sq_to_K, vacuumData.norm_eq_one]
  norm_num

/-- A singleton correlator is the exact vacuum matrix element of the exact field. -/
theorem scalarWightmanVacuumExpectation_singleton
    {d : EuclideanDimension} {G : Type*}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {lift : ProperOrthochronousPoincareLiftData d G}
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H]
    {U : StronglyContinuousUnitaryPoincareRepresentation lift H}
    {vacuumData : PoincareInvariantVacuumData U}
    {D : CommonInvariantDomainData vacuumData}
    (fieldData : ScalarWightmanFieldOnCommonDomainData D)
    (f : ScalarMinkowskiSchwartzTestFunction d) :
    scalarWightmanVacuumExpectation fieldData [f] =
      inner ℂ vacuumData.vacuum
        ((fieldData.field f D.vacuumInDomain : D.domain) : H) :=
  rfl

/-- A two-point correlator locks the operator order `Φ(f) Φ(g) Ω`. -/
theorem scalarWightmanVacuumExpectation_pair
    {d : EuclideanDimension} {G : Type*}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {lift : ProperOrthochronousPoincareLiftData d G}
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H]
    {U : StronglyContinuousUnitaryPoincareRepresentation lift H}
    {vacuumData : PoincareInvariantVacuumData U}
    {D : CommonInvariantDomainData vacuumData}
    (fieldData : ScalarWightmanFieldOnCommonDomainData D)
    (f g : ScalarMinkowskiSchwartzTestFunction d) :
    scalarWightmanVacuumExpectation fieldData [f, g] =
      inner ℂ vacuumData.vacuum
        ((fieldData.field f (fieldData.field g D.vacuumInDomain) : D.domain) : H) :=
  rfl

/-- The singleton correlator is evaluated by the exact coherent tempered matrix element. -/
theorem scalarWightmanVacuumExpectation_singleton_eq_matrixElement
    {d : EuclideanDimension} {G : Type*}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {lift : ProperOrthochronousPoincareLiftData d G}
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H]
    {U : StronglyContinuousUnitaryPoincareRepresentation lift H}
    {vacuumData : PoincareInvariantVacuumData U}
    {D : CommonInvariantDomainData vacuumData}
    (fieldData : ScalarWightmanFieldOnCommonDomainData D)
    (f : ScalarMinkowskiSchwartzTestFunction d) :
    scalarWightmanVacuumExpectation fieldData [f] =
      fieldData.matrixElement D.vacuumInDomain D.vacuumInDomain f := by
  rw [scalarWightmanVacuumExpectation_singleton]
  exact (fieldData.matrixElement_coherent D.vacuumInDomain D.vacuumInDomain f).symm

end YangMills.Minkowski
