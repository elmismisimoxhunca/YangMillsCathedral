/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Minkowski.CommonInvariantDomain

/-!
# Hostile probes for the common invariant domain

The probes retain density, the same nonzero vacuum, exact restricted Poincaré action, invertibility,
and rejection of a physical unitary image outside the domain. No field is constructed.
-/

namespace YangMills.Minkowski.CommonInvariantDomain.Probes

variable
    {d : EuclideanDimension} {G : Type*}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {lift : ProperOrthochronousPoincareLiftData d G}
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H]
    {U : StronglyContinuousUnitaryPoincareRepresentation lift H}
    {vacuumData : PoincareInvariantVacuumData U}

/-- The domain contains the exact selected vacuum, not an unrelated witness. -/
theorem exact_vacuum_value
    (D : CommonInvariantDomainData vacuumData) :
    D.vacuumInDomain.val = vacuumData.vacuum :=
  rfl

/-- The selected vacuum remains nonzero after domain restriction. -/
theorem domain_vacuum_ne_zero
    (D : CommonInvariantDomainData vacuumData) : D.vacuumInDomain ≠ 0 :=
  D.vacuumInDomain_ne_zero

/-- The common domain cannot be the bottom submodule. -/
theorem bottom_domain_blocked
    (D : CommonInvariantDomainData vacuumData) (hbottom : D.domain = ⊥) : False := by
  have hvac : vacuumData.vacuum ∈ (⊥ : Submodule ℂ H) := by
    rw [← hbottom]
    exact D.vacuum_mem
  have hzero : vacuumData.vacuum = 0 := by
    simpa using hvac
  exact vacuumData.vacuum_ne_zero hzero

/-- The common domain is genuinely dense in the physical Hilbert carrier. -/
theorem exact_domain_density
    (D : CommonInvariantDomainData vacuumData) : Dense (D.domain : Set H) :=
  D.dense

/-- The restricted unitary has exactly the same underlying physical action. -/
theorem exact_restricted_unitary_value
    (D : CommonInvariantDomainData vacuumData) (g : G) (ψ : D.domain) :
    (D.domainUnitary g ψ).val = U.unitary g ψ.val :=
  rfl

/-- Restriction remains invertible on the same common domain. -/
theorem restricted_unitary_inverse
    (D : CommonInvariantDomainData vacuumData) (g : G) (ψ : D.domain) :
    D.domainUnitary (g⁻¹) (D.domainUnitary g ψ) = ψ := by
  apply Subtype.ext
  change (U.unitary (g⁻¹) * U.unitary g) ψ.val = ψ.val
  rw [← U.unitary.map_mul]
  simp

/-- The restricted action fixes the exact domain vacuum. -/
theorem restricted_unitary_fixes_vacuum
    (D : CommonInvariantDomainData vacuumData) (g : G) :
    D.domainUnitary g D.vacuumInDomain = D.vacuumInDomain :=
  D.domainUnitary_vacuum g

/-- A physical unitary image of a domain vector cannot be replaced by a vector outside the common
domain. -/
theorem unitary_image_outside_domain_blocked
    (D : CommonInvariantDomainData vacuumData) (g : G) (ψ : D.domain)
    (houtside : U.unitary g ψ.val ∉ D.domain) : False :=
  houtside (D.invariant g ψ)

end YangMills.Minkowski.CommonInvariantDomain.Probes
