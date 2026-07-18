/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Minkowski.TemperedLocalObservableProducts

/-!
# Hostile probes for tempered local-observable products

These probes reject empty/singleton labels, a zero unit, zero local operators, zero bilocal products,
reversed/disconnected product witnesses, and unrelated full-product distributions. No observable or
OPE datum is constructed.
-/

namespace YangMills.Minkowski.TemperedLocalObservableProducts.Probes

open YangMills.Mathematics

variable
    {d : EuclideanDimension} {G : Type*}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {lift : ProperOrthochronousPoincareLiftData d G}
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H]
    {U : StronglyContinuousUnitaryPoincareRepresentation lift H}
    {vacuumData : PoincareInvariantVacuumData U}
    {D : CommonInvariantDomainData vacuumData}

/-- The label carrier contains at least the distinct unit and nontrivial labels. -/
theorem singleton_label_carrier_blocked
    (family : TemperedLocalObservableFamilyData D) :
    ∃ A B : family.Label, A ≠ B :=
  ⟨family.nontrivialLabel, family.unitLabel, family.nontrivialLabel_ne_unit⟩

/-- The normalized unit field is not the zero operator family. -/
theorem zero_unit_operator_blocked
    (family : TemperedLocalObservableFamilyData D) :
    family.operator family.unitLabel family.normalizedUnitTest ≠ 0 := by
  intro hzero
  have happly := LinearMap.congr_fun hzero D.vacuumInDomain
  rw [family.unit_normalizedTest_apply] at happly
  simpa using D.vacuumInDomain_ne_zero happly

/-- The designated nontrivial field has an actual nonzero action on the same domain. -/
theorem zero_nontrivial_operator_blocked
    (family : TemperedLocalObservableFamilyData D) :
    ∃ (f : ScalarMinkowskiSchwartzTestFunction d) (φ : D.domain),
      family.operator family.nontrivialLabel f φ ≠ 0 := by
  rcases family.nontrivial_operator_witness with ⟨f, φ, hnonzero, _⟩
  exact ⟨f, φ, hnonzero⟩

/-- Distinct labels are witnessed by genuinely different actions, not names alone. -/
theorem duplicate_unit_operator_label_blocked
    (family : TemperedLocalObservableFamilyData D) :
    ∃ (f : ScalarMinkowskiSchwartzTestFunction d) (φ : D.domain),
      family.operator family.nontrivialLabel f φ ≠
        family.operator family.unitLabel f φ := by
  rcases family.nontrivial_operator_witness with ⟨f, φ, _, hdifferent⟩
  exact ⟨f, φ, hdifferent⟩

/-- Matrix-element distributions are tied to the exact same labeled operator and ordered vectors. -/
theorem exact_local_matrix_element
    (family : TemperedLocalObservableFamilyData D)
    (A : family.Label) (ψ φ : D.domain)
    (f : ScalarMinkowskiSchwartzTestFunction d) :
    family.matrixElement A ψ φ f =
      @inner ℂ H _ ψ.val (family.operator A f φ).val :=
  family.matrixElement_coherent A ψ φ f

/-- Pure tensors retain exact `A(f)` after `B(g)` operator order. -/
theorem exact_bilocal_operator_order
    {family : TemperedLocalObservableFamilyData D}
    (products : WeakTemperedBilocalObservableProductData family)
    (A B : family.Label) (ψ φ : D.domain)
    (f g : ScalarMinkowskiSchwartzTestFunction d) :
    products.bilocalMatrixElement A B ψ φ
        (scalarSchwartzPureTensor (Spacetime d) 2 ![f, g]) =
      @inner ℂ H _ ψ.val (family.operator A f (family.operator B g φ)).val :=
  products.pureTensor_coherent A B ψ φ f g

/-- The entire bilocal family cannot be the zero distribution family. -/
theorem zero_bilocal_family_blocked
    {family : TemperedLocalObservableFamilyData D}
    (products : WeakTemperedBilocalObservableProductData family) :
    ∃ (A B : family.Label) (ψ φ : D.domain),
      products.bilocalMatrixElement A B ψ φ ≠ 0 :=
  products.exists_nonzero_distribution

/-- A candidate full-product distribution disagreeing on one exact pure tensor is unrelated. -/
theorem unrelated_bilocal_distribution_blocked
    {family : TemperedLocalObservableFamilyData D}
    (products : WeakTemperedBilocalObservableProductData family)
    (A B : family.Label) (ψ φ : D.domain)
    (f g : ScalarMinkowskiSchwartzTestFunction d)
    (candidate : TemperedDistribution (FiniteConfiguration (Spacetime d) 2) ℂ)
    (hdisagree : candidate (scalarSchwartzPureTensor (Spacetime d) 2 ![f, g]) ≠
      @inner ℂ H _ ψ.val (family.operator A f (family.operator B g φ)).val) :
    candidate ≠ products.bilocalMatrixElement A B ψ φ := by
  intro heq
  apply hdisagree
  rw [heq, products.pureTensor_coherent]

end YangMills.Minkowski.TemperedLocalObservableProducts.Probes
