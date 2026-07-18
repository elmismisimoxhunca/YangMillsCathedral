/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Minkowski.WightmanCyclicity

/-!
# Hostile probes for scalar Wightman vacuum cyclicity

The probes retain the empty word, exact field and adjoint singleton words, the nonzero selected
vacuum, and the full closure condition. No cyclic field datum is constructed.
-/

namespace YangMills.Minkowski.WightmanCyclicity.Probes

variable
    {d : EuclideanDimension} {G : Type*}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {lift : ProperOrthochronousPoincareLiftData d G}
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H]
    {U : StronglyContinuousUnitaryPoincareRepresentation lift H}
    {vacuumData : PoincareInvariantVacuumData U}
    {D : CommonInvariantDomainData vacuumData}
    {fieldData : ScalarWightmanFieldOnCommonDomainData D}

/-- The empty word is exactly the same selected domain vacuum. -/
theorem empty_word_is_vacuum :
    scalarWightmanFieldWordOnVacuum fieldData [] = D.vacuumInDomain :=
  rfl

/-- A singleton field word applies that exact smeared field to the vacuum. -/
theorem singleton_field_word_exact
    (f : ScalarMinkowskiSchwartzTestFunction d) :
    scalarWightmanFieldWordOnVacuum fieldData [.field f] =
      fieldData.field f D.vacuumInDomain :=
  rfl

/-- A singleton adjoint word applies that exact smeared adjoint to the vacuum. -/
theorem singleton_adjoint_word_exact
    (f : ScalarMinkowskiSchwartzTestFunction d) :
    scalarWightmanFieldWordOnVacuum fieldData [.adjoint f] =
      fieldData.adjointField f D.vacuumInDomain :=
  rfl

/-- A mixed two-letter word locks the documented order: the head field acts after the tail
adjoint has acted on the vacuum. -/
theorem mixed_two_letter_word_order
    (f g : ScalarMinkowskiSchwartzTestFunction d) :
    scalarWightmanFieldWordOnVacuum fieldData [.field f, .adjoint g] =
      fieldData.field f (fieldData.adjointField g D.vacuumInDomain) :=
  rfl

/-- Every finite field word remains in the exact common domain by construction. -/
theorem every_word_in_exact_domain
    (word : List (ScalarWightmanFieldLetter d)) :
    (scalarWightmanFieldWordOnVacuum fieldData word).val ∈ D.domain :=
  (scalarWightmanFieldWordOnVacuum fieldData word).property

/-- The selected nonzero vacuum belongs to the polynomial-vacuum span via the empty word. -/
theorem exact_vacuum_mem_polynomial_span :
    vacuumData.vacuum ∈ scalarWightmanFieldPolynomialVacuumSubmodule fieldData :=
  vacuum_mem_scalarWightmanFieldPolynomialVacuumSubmodule fieldData

/-- The span is nontrivial because it contains the nonzero selected vacuum. -/
theorem polynomial_span_ne_bot :
    scalarWightmanFieldPolynomialVacuumSubmodule fieldData ≠ ⊥ := by
  intro hbot
  have hvac : vacuumData.vacuum ∈ (⊥ : Submodule ℂ H) := by
    rw [← hbot]
    exact exact_vacuum_mem_polynomial_span
  have hzero : vacuumData.vacuum = 0 := by simpa using hvac
  exact vacuumData.vacuum_ne_zero hzero

/-- Cyclicity puts every Hilbert vector in the closure of the exact polynomial-vacuum span. -/
theorem cyclicity_reaches_every_vector
    (hcyclic : ScalarWightmanVacuumCyclicity fieldData) (ψ : H) :
    ψ ∈ (scalarWightmanFieldPolynomialVacuumSubmodule fieldData).topologicalClosure := by
  rw [hcyclic]
  trivial

/-- A vector claimed outside the polynomial closure contradicts cyclicity. -/
theorem disconnected_hilbert_vector_blocked
    (hcyclic : ScalarWightmanVacuumCyclicity fieldData) (ψ : H)
    (houtside : ψ ∉
      (scalarWightmanFieldPolynomialVacuumSubmodule fieldData).topologicalClosure) : False :=
  houtside (cyclicity_reaches_every_vector hcyclic ψ)

/-- The explicit nonzero Minkowski bump is wired into an actual singleton field word. -/
theorem bump_singleton_word_exact :
    scalarWightmanFieldWordOnVacuum fieldData
        [.field (scalarMinkowskiSchwartzBump d)] =
      fieldData.field (scalarMinkowskiSchwartzBump d) D.vacuumInDomain :=
  rfl

end YangMills.Minkowski.WightmanCyclicity.Probes
