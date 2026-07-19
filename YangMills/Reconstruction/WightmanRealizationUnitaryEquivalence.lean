/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Minkowski.ScalarWightmanAxiomSurface
import YangMills.Minkowski.WightmanVacuumCorrelators

/-!
# Unitary equivalence of scalar Wightman realizations

Streater–Wightman printed p. 118 states the reconstruction uniqueness conclusion: every other field
theory with the same vacuum expectation values is related by a unitary transformation intertwining
the vacuum, Poincaré representation, field, and common domain.

This module formalizes that equivalence relation between two already supplied scalar Wightman
realizations. Potentially different lift-group carriers are connected by a continuous multiplicative
equivalence compatible with the exact affine projection and physical translations. No equivalence
or Wightman realization is constructed.
-/

namespace YangMills.Reconstruction

open YangMills
open Minkowski

/-- Exact unitary equivalence between two scalar Wightman field realizations. -/
structure ScalarWightmanRealizationUnitaryEquivalence
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
    (field₁ : ScalarWightmanFieldOnCommonDomainData D₁)
    (field₂ : ScalarWightmanFieldOnCommonDomainData D₂) where
  /-- Equivalence of the potentially different lift-group carriers. -/
  liftEquiv : G₁ ≃ₜ* G₂
  /-- Both lift groups project to the exact same affine Poincaré transformation. -/
  projection_coherent : ∀ g, lift₂.projection (liftEquiv g) = lift₁.projection g
  /-- Physical translations are transported exactly, excluding a sheet-switching surrogate. -/
  translation_coherent : ∀ a : Spacetime d,
    liftEquiv (lift₁.translation (Multiplicative.ofAdd a)) =
      lift₂.translation (Multiplicative.ofAdd a)
  /-- Unitary equivalence of the physical Hilbert carriers. -/
  hilbertEquiv : H₁ ≃ₗᵢ[ℂ] H₂
  /-- The exact Poincaré representations intertwine through the same lift equivalence. -/
  representation_intertwines : ∀ g ψ,
    hilbertEquiv (U₁.unitary g ψ) = U₂.unitary (liftEquiv g) (hilbertEquiv ψ)
  /-- The normalized vacua correspond exactly. -/
  vacuum_coherent : hilbertEquiv vacuum₁.vacuum = vacuum₂.vacuum
  /-- The dense common invariant domains correspond as norm-preserving complex modules. -/
  domainEquiv : D₁.domain ≃ₗᵢ[ℂ] D₂.domain
  /-- Domain transport is the restriction of the same Hilbert unitary. -/
  domain_coherent : ∀ ψ : D₁.domain,
    ((domainEquiv ψ : D₂.domain) : H₂) = hilbertEquiv (ψ : H₁)
  /-- Every smeared scalar field intertwines on the exact transported common domain. -/
  field_intertwines : ∀ test ψ,
    domainEquiv (field₁.field test ψ) = field₂.field test (domainEquiv ψ)
  /-- The exact adjoint field intertwines as well. -/
  adjoint_intertwines : ∀ test ψ,
    domainEquiv (field₁.adjointField test ψ) =
      field₂.adjointField test (domainEquiv ψ)

/-- Source-facing unitary equivalence when both realizations use the same exact Poincaré lift.
Streater–Wightman p. 118 fixes the symmetry group; the identity condition prevents irrelevant
relabeling or invisible-kernel enlargement from entering corrected reconstruction uniqueness. -/
structure ScalarWightmanFixedLiftUnitaryEquivalence
    {d : EuclideanDimension}
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {lift : ProperOrthochronousPoincareLiftData d G}
    {H₁ H₂ : Type*}
    [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [CompleteSpace H₁]
    [TopologicalSpace.SeparableSpace H₁]
    [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] [CompleteSpace H₂]
    [TopologicalSpace.SeparableSpace H₂]
    {U₁ : StronglyContinuousUnitaryPoincareRepresentation lift H₁}
    {U₂ : StronglyContinuousUnitaryPoincareRepresentation lift H₂}
    {vacuum₁ : PoincareInvariantVacuumData U₁}
    {vacuum₂ : PoincareInvariantVacuumData U₂}
    {D₁ : CommonInvariantDomainData vacuum₁}
    {D₂ : CommonInvariantDomainData vacuum₂}
    (field₁ : ScalarWightmanFieldOnCommonDomainData D₁)
    (field₂ : ScalarWightmanFieldOnCommonDomainData D₂) extends
      ScalarWightmanRealizationUnitaryEquivalence field₁ field₂ where
  /-- The group transport is exactly the identity on the shared lift carrier. -/
  liftEquiv_eq_refl : toScalarWightmanRealizationUnitaryEquivalence.liftEquiv =
    ContinuousMulEquiv.refl G

namespace ScalarWightmanRealizationUnitaryEquivalence

/-- The common-domain vacuum vectors correspond exactly. -/
theorem vacuumInDomain_coherent
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
    (equiv : ScalarWightmanRealizationUnitaryEquivalence field₁ field₂) :
    equiv.domainEquiv D₁.vacuumInDomain = D₂.vacuumInDomain := by
  apply Subtype.ext
  rw [equiv.domain_coherent]
  change equiv.hilbertEquiv vacuum₁.vacuum = vacuum₂.vacuum
  exact equiv.vacuum_coherent

/-- Field intertwining also holds after coercion to the physical Hilbert carriers. -/
theorem field_intertwines_hilbert
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
    (test : ScalarMinkowskiSchwartzTestFunction d) (ψ : D₁.domain) :
    ((field₂.field test (equiv.domainEquiv ψ) : D₂.domain) : H₂) =
      equiv.hilbertEquiv ((field₁.field test ψ : D₁.domain) : H₁) := by
  rw [← equiv.field_intertwines]
  exact equiv.domain_coherent _

section WordCoherence

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

/-- One field-or-adjoint letter commutes with exact domain transport. -/
theorem letter_apply_intertwines
    (letter : ScalarWightmanFieldLetter d) (ψ : D₁.domain) :
    equiv.domainEquiv (letter.apply field₁ ψ) =
      letter.apply field₂ (equiv.domainEquiv ψ) := by
  cases letter with
  | field test => exact equiv.field_intertwines test ψ
  | adjoint test => exact equiv.adjoint_intertwines test ψ

/-- Every finite field/adjoint word on the vacuum commutes with exact domain transport. -/
theorem wordOnVacuum_intertwines
    (word : List (ScalarWightmanFieldLetter d)) :
    equiv.domainEquiv (scalarWightmanFieldWordOnVacuum field₁ word) =
      scalarWightmanFieldWordOnVacuum field₂ word := by
  induction word with
  | nil => exact equiv.vacuumInDomain_coherent
  | cons letter word ih =>
      change equiv.domainEquiv
          (letter.apply field₁ (scalarWightmanFieldWordOnVacuum field₁ word)) =
        letter.apply field₂ (scalarWightmanFieldWordOnVacuum field₂ word)
      rw [equiv.letter_apply_intertwines, ih]

include equiv

/-- Unitary-equivalent realizations have identical finite field/adjoint vacuum words. -/
theorem vacuumWordExpectation_eq
    (word : List (ScalarWightmanFieldLetter d)) :
    scalarWightmanVacuumWordExpectation field₁ word =
      scalarWightmanVacuumWordExpectation field₂ word := by
  rw [scalarWightmanVacuumWordExpectation, scalarWightmanVacuumWordExpectation]
  have word_hilbert :
      ((scalarWightmanFieldWordOnVacuum field₂ word : D₂.domain) : H₂) =
        equiv.hilbertEquiv
          ((scalarWightmanFieldWordOnVacuum field₁ word : D₁.domain) : H₁) := by
    rw [← equiv.wordOnVacuum_intertwines word]
    exact equiv.domain_coherent _
  calc
    inner ℂ vacuum₁.vacuum
        ((scalarWightmanFieldWordOnVacuum field₁ word : D₁.domain) : H₁) =
      inner ℂ (equiv.hilbertEquiv vacuum₁.vacuum)
        (equiv.hilbertEquiv
          ((scalarWightmanFieldWordOnVacuum field₁ word : D₁.domain) : H₁)) :=
      (equiv.hilbertEquiv.inner_map_map _ _).symm
    _ = inner ℂ vacuum₂.vacuum
        ((scalarWightmanFieldWordOnVacuum field₂ word : D₂.domain) : H₂) := by
      rw [equiv.vacuum_coherent, ← word_hilbert]

/-- In particular, all ordered field-only smeared vacuum correlators agree. -/
theorem vacuumExpectation_eq
    (tests : List (ScalarMinkowskiSchwartzTestFunction d)) :
    scalarWightmanVacuumExpectation field₁ tests =
      scalarWightmanVacuumExpectation field₂ tests :=
  equiv.vacuumWordExpectation_eq (tests.map ScalarWightmanFieldLetter.field)

end WordCoherence

/-- Unitary-equivalent realizations have the same one-point vacuum expectation value. -/
theorem singleton_vacuumExpectation_eq
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
    (test : ScalarMinkowskiSchwartzTestFunction d) :
    scalarWightmanVacuumExpectation field₁ [test] =
      scalarWightmanVacuumExpectation field₂ [test] := by
  rw [scalarWightmanVacuumExpectation_singleton,
    scalarWightmanVacuumExpectation_singleton]
  have field_hilbert := equiv.field_intertwines_hilbert test D₁.vacuumInDomain
  rw [equiv.vacuumInDomain_coherent] at field_hilbert
  calc
    inner ℂ vacuum₁.vacuum
        ((field₁.field test D₁.vacuumInDomain : D₁.domain) : H₁) =
      inner ℂ (equiv.hilbertEquiv vacuum₁.vacuum)
        (equiv.hilbertEquiv
          ((field₁.field test D₁.vacuumInDomain : D₁.domain) : H₁)) :=
      (equiv.hilbertEquiv.inner_map_map _ _).symm
    _ = inner ℂ vacuum₂.vacuum
        ((field₂.field test D₂.vacuumInDomain : D₂.domain) : H₂) := by
      rw [equiv.vacuum_coherent, ← field_hilbert]

end ScalarWightmanRealizationUnitaryEquivalence

namespace ScalarWightmanFixedLiftUnitaryEquivalence

/-- On the source-facing fixed lift, representation intertwining uses the exact same group element. -/
theorem representation_intertwines_same
    {d : EuclideanDimension}
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {lift : ProperOrthochronousPoincareLiftData d G}
    {H₁ H₂ : Type*}
    [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [CompleteSpace H₁]
    [TopologicalSpace.SeparableSpace H₁]
    [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] [CompleteSpace H₂]
    [TopologicalSpace.SeparableSpace H₂]
    {U₁ : StronglyContinuousUnitaryPoincareRepresentation lift H₁}
    {U₂ : StronglyContinuousUnitaryPoincareRepresentation lift H₂}
    {vacuum₁ : PoincareInvariantVacuumData U₁}
    {vacuum₂ : PoincareInvariantVacuumData U₂}
    {D₁ : CommonInvariantDomainData vacuum₁}
    {D₂ : CommonInvariantDomainData vacuum₂}
    {field₁ : ScalarWightmanFieldOnCommonDomainData D₁}
    {field₂ : ScalarWightmanFieldOnCommonDomainData D₂}
    (equiv : ScalarWightmanFixedLiftUnitaryEquivalence field₁ field₂)
    (g : G) (ψ : H₁) :
    equiv.hilbertEquiv (U₁.unitary g ψ) = U₂.unitary g (equiv.hilbertEquiv ψ) := by
  have h := equiv.representation_intertwines g ψ
  rw [equiv.liftEquiv_eq_refl] at h
  exact h

/-- Fixed-lift equivalence retains equality of every finite ordered smeared vacuum correlator. -/
theorem vacuumExpectation_eq
    {d : EuclideanDimension}
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {lift : ProperOrthochronousPoincareLiftData d G}
    {H₁ H₂ : Type*}
    [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [CompleteSpace H₁]
    [TopologicalSpace.SeparableSpace H₁]
    [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] [CompleteSpace H₂]
    [TopologicalSpace.SeparableSpace H₂]
    {U₁ : StronglyContinuousUnitaryPoincareRepresentation lift H₁}
    {U₂ : StronglyContinuousUnitaryPoincareRepresentation lift H₂}
    {vacuum₁ : PoincareInvariantVacuumData U₁}
    {vacuum₂ : PoincareInvariantVacuumData U₂}
    {D₁ : CommonInvariantDomainData vacuum₁}
    {D₂ : CommonInvariantDomainData vacuum₂}
    {field₁ : ScalarWightmanFieldOnCommonDomainData D₁}
    {field₂ : ScalarWightmanFieldOnCommonDomainData D₂}
    (equiv : ScalarWightmanFixedLiftUnitaryEquivalence field₁ field₂)
    (tests : List (ScalarMinkowskiSchwartzTestFunction d)) :
    scalarWightmanVacuumExpectation field₁ tests =
      scalarWightmanVacuumExpectation field₂ tests :=
  equiv.toScalarWightmanRealizationUnitaryEquivalence.vacuumExpectation_eq tests

end ScalarWightmanFixedLiftUnitaryEquivalence

end YangMills.Reconstruction
