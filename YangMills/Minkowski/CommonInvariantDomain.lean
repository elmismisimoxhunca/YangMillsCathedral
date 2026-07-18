/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Minkowski.Vacuum

/-!
# Common dense Poincaré-invariant domain

Streater–Wightman, printed p. 98, axiom `I`, requires all smeared fields and adjoints to share one
dense invariant domain containing the vacuum. This module packages the domain before introducing
fields: it is one complex submodule of the same Hilbert space, dense in that space, contains the
same selected vacuum, and is invariant under the same unitary Poincaré lift-group representation.

Each physical unitary therefore restricts to a linear isometric equivalence of this exact domain.
No field operator, adjoint, tempered matrix element, cyclicity claim, spectrum, or inhabitant is
introduced here.
-/

namespace YangMills.Minkowski

/-- One common dense subspace containing the selected vacuum and invariant under the same physical
Poincaré representation. -/
structure CommonInvariantDomainData
    {d : EuclideanDimension} {G : Type*}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {lift : ProperOrthochronousPoincareLiftData d G}
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H]
    {U : StronglyContinuousUnitaryPoincareRepresentation lift H}
    (vacuumData : PoincareInvariantVacuumData U) where
  /-- The exact common operator domain. -/
  domain : Submodule ℂ H
  /-- The common domain is dense in the physical Hilbert space. -/
  dense : Dense (domain : Set H)
  /-- The same selected vacuum lies in the common domain. -/
  vacuum_mem : vacuumData.vacuum ∈ domain
  /-- Every physical Poincaré unitary preserves the common domain. -/
  invariant : ∀ g : G, ∀ ψ : domain, U.unitary g ψ.val ∈ domain

/-- The selected vacuum as an actual vector of the common domain. -/
def CommonInvariantDomainData.vacuumInDomain
    {d : EuclideanDimension} {G : Type*}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {lift : ProperOrthochronousPoincareLiftData d G}
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H]
    {U : StronglyContinuousUnitaryPoincareRepresentation lift H}
    {vacuumData : PoincareInvariantVacuumData U}
    (D : CommonInvariantDomainData vacuumData) : D.domain :=
  ⟨vacuumData.vacuum, D.vacuum_mem⟩

/-- The vacuum remains nonzero inside the common domain. -/
theorem CommonInvariantDomainData.vacuumInDomain_ne_zero
    {d : EuclideanDimension} {G : Type*}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {lift : ProperOrthochronousPoincareLiftData d G}
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H]
    {U : StronglyContinuousUnitaryPoincareRepresentation lift H}
    {vacuumData : PoincareInvariantVacuumData U}
    (D : CommonInvariantDomainData vacuumData) : D.vacuumInDomain ≠ 0 := by
  intro hzero
  apply vacuumData.vacuum_ne_zero
  exact congrArg Subtype.val hzero

/-- Every physical Poincaré unitary restricts to a linear isometric equivalence of the exact common
domain. -/
noncomputable def CommonInvariantDomainData.domainUnitary
    {d : EuclideanDimension} {G : Type*}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {lift : ProperOrthochronousPoincareLiftData d G}
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H]
    {U : StronglyContinuousUnitaryPoincareRepresentation lift H}
    {vacuumData : PoincareInvariantVacuumData U}
    (D : CommonInvariantDomainData vacuumData) (g : G) :
    D.domain ≃ₗᵢ[ℂ] D.domain where
  toFun ψ := ⟨U.unitary g ψ.val, D.invariant g ψ⟩
  invFun ψ := ⟨U.unitary (g⁻¹) ψ.val, D.invariant (g⁻¹) ψ⟩
  left_inv ψ := by
    apply Subtype.ext
    change (U.unitary (g⁻¹) * U.unitary g) ψ.val = ψ.val
    rw [← U.unitary.map_mul]
    simp
  right_inv ψ := by
    apply Subtype.ext
    change (U.unitary g * U.unitary (g⁻¹)) ψ.val = ψ.val
    rw [← U.unitary.map_mul]
    simp
  map_add' x y := by ext; simp
  map_smul' c x := by ext; simp
  norm_map' x := (U.unitary g).norm_map x.val

/-- The restricted domain unitary fixes the selected vacuum in the domain. -/
@[simp] theorem CommonInvariantDomainData.domainUnitary_vacuum
    {d : EuclideanDimension} {G : Type*}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {lift : ProperOrthochronousPoincareLiftData d G}
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H]
    {U : StronglyContinuousUnitaryPoincareRepresentation lift H}
    {vacuumData : PoincareInvariantVacuumData U}
    (D : CommonInvariantDomainData vacuumData) (g : G) :
    D.domainUnitary g D.vacuumInDomain = D.vacuumInDomain := by
  apply Subtype.ext
  exact vacuumData.invariant g

end YangMills.Minkowski
