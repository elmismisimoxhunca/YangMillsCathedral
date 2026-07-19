/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Reconstruction.WightmanRealizationUnitaryEquivalence

/-!
# Hostile probes for Wightman-realization unitary equivalence

These probes lock lift projection, translations, representation, vacuum, domain, field, and adjoint
intertwining to the same Hilbert unitary. They construct no equivalence or realization.
-/

namespace YangMills.Reconstruction.WightmanRealizationUnitaryEquivalence.Probes

open YangMills
open YangMills.Minkowski

variable
    {d : EuclideanDimension}
    {G₁ G₂ : Type*}
    [Group G₁] [TopologicalSpace G₁] [IsTopologicalGroup G₁]
    [Group G₂] [TopologicalSpace G₂] [IsTopologicalGroup G₂]
    {lift₁ : ProperOrthochronousPoincareLiftData d G₁}
    {lift₂ : ProperOrthochronousPoincareLiftData d G₂}
    {H₁ H₂ : Type*}
    [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [CompleteSpace H₁]
    [TopologicalSpace.SeparableSpace H₁]
    [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] [CompleteSpace H₂]
    [TopologicalSpace.SeparableSpace H₂]
    {U₁ : StronglyContinuousUnitaryPoincareRepresentation lift₁ H₁}
    {U₂ : StronglyContinuousUnitaryPoincareRepresentation lift₂ H₂}
    {vacuum₁ : PoincareInvariantVacuumData U₁}
    {vacuum₂ : PoincareInvariantVacuumData U₂}
    {D₁ : CommonInvariantDomainData vacuum₁}
    {D₂ : CommonInvariantDomainData vacuum₂}
    {field₁ : ScalarWightmanFieldOnCommonDomainData D₁}
    {field₂ : ScalarWightmanFieldOnCommonDomainData D₂}
    (equiv : ScalarWightmanRealizationUnitaryEquivalence field₁ field₂)

/-- Both lift carriers project to the exact same affine transformation. -/
example (g : G₁) : lift₂.projection (equiv.liftEquiv g) = lift₁.projection g :=
  equiv.projection_coherent g

/-- Physical translations cannot switch to the other abstract cover sheet. -/
example (a : Spacetime d) :
    equiv.liftEquiv (lift₁.translation (Multiplicative.ofAdd a)) =
      lift₂.translation (Multiplicative.ofAdd a) :=
  equiv.translation_coherent a

/-- The same Hilbert unitary intertwines the exact Poincaré representations. -/
example (g : G₁) (ψ : H₁) :
    equiv.hilbertEquiv (U₁.unitary g ψ) =
      U₂.unitary (equiv.liftEquiv g) (equiv.hilbertEquiv ψ) :=
  equiv.representation_intertwines g ψ

/-- The exact normalized vacua correspond. -/
example : equiv.hilbertEquiv vacuum₁.vacuum = vacuum₂.vacuum :=
  equiv.vacuum_coherent

/-- Domain transport is the restriction of that same Hilbert unitary. -/
example (ψ : D₁.domain) :
    ((equiv.domainEquiv ψ : D₂.domain) : H₂) = equiv.hilbertEquiv (ψ : H₁) :=
  equiv.domain_coherent ψ

/-- The common-domain vacuum vectors correspond exactly. -/
example : equiv.domainEquiv D₁.vacuumInDomain = D₂.vacuumInDomain :=
  equiv.vacuumInDomain_coherent

/-- Fields and adjoints intertwine on the exact transported domain. -/
example (test : ScalarMinkowskiSchwartzTestFunction d) (ψ : D₁.domain) :
    equiv.domainEquiv (field₁.field test ψ) =
        field₂.field test (equiv.domainEquiv ψ) ∧
      equiv.domainEquiv (field₁.adjointField test ψ) =
        field₂.adjointField test (equiv.domainEquiv ψ) :=
  ⟨equiv.field_intertwines test ψ, equiv.adjoint_intertwines test ψ⟩

/-- Every field/adjoint word on the exact vacuum is transported, not just single fields. -/
example (word : List (ScalarWightmanFieldLetter d)) :
    equiv.domainEquiv (scalarWightmanFieldWordOnVacuum field₁ word) =
      scalarWightmanFieldWordOnVacuum field₂ word :=
  equiv.wordOnVacuum_intertwines word

/-- Every finite field/adjoint vacuum expectation agrees. -/
example (word : List (ScalarWightmanFieldLetter d)) :
    scalarWightmanVacuumWordExpectation field₁ word =
      scalarWightmanVacuumWordExpectation field₂ word :=
  equiv.vacuumWordExpectation_eq word

/-- Every finite ordered field-only smeared vacuum correlator agrees. -/
example (tests : List (ScalarMinkowskiSchwartzTestFunction d)) :
    scalarWightmanVacuumExpectation field₁ tests =
      scalarWightmanVacuumExpectation field₂ tests :=
  equiv.vacuumExpectation_eq tests

/-- The singleton statement remains available as an explicit hostile specialization. -/
example (test : ScalarMinkowskiSchwartzTestFunction d) :
    scalarWightmanVacuumExpectation field₁ [test] =
      scalarWightmanVacuumExpectation field₂ [test] :=
  equiv.singleton_vacuumExpectation_eq test

/-- The source-facing specialization fixes the lift transport to the identity and therefore
intertwines representations at the exact same group element. -/
example
    {U₂same : StronglyContinuousUnitaryPoincareRepresentation lift₁ H₂}
    {vacuum₂same : PoincareInvariantVacuumData U₂same}
    {D₂same : CommonInvariantDomainData vacuum₂same}
    {field₂same : ScalarWightmanFieldOnCommonDomainData D₂same}
    (fixed : ScalarWightmanFixedLiftUnitaryEquivalence field₁ field₂same)
    (g : G₁) (ψ : H₁) :
    fixed.liftEquiv = ContinuousMulEquiv.refl G₁ ∧
      fixed.hilbertEquiv (U₁.unitary g ψ) =
        U₂same.unitary g (fixed.hilbertEquiv ψ) :=
  ⟨fixed.liftEquiv_eq_refl, fixed.representation_intertwines_same g ψ⟩

end YangMills.Reconstruction.WightmanRealizationUnitaryEquivalence.Probes
