/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Minkowski.WightmanLocality

/-!
# Hostile probes for scalar Wightman locality

The probes expose a nonempty locality test domain in four dimensions, the dimension-one
obstruction, support-separation symmetry, all four field/adjoint commutators, and rejection of a
disconnected replacement operator value. No local field datum is constructed.
-/

namespace YangMills.Minkowski.WightmanLocality.Probes

/-- The spacelike point-pair relation is open. -/
theorem spacelike_pair_relation_open
    (d : EuclideanDimension) : IsOpen (spacelikeSeparatedPointPairSet d) :=
  isOpen_spacelikeSeparatedPointPairSet d

/-- Four-dimensional Minkowski spacetime has two explicit-existence nonzero Schwartz tests with
spacelike-separated topological supports. -/
theorem four_dimensional_nonzero_locality_tests_exist :
    ∃ f g : ScalarMinkowskiSchwartzTestFunction EuclideanDimension.four,
      f ≠ 0 ∧ g ≠ 0 ∧ HaveSpacelikeSeparatedTopologicalSupports f g :=
  exists_nonzero_spacelikeSeparated_scalarMinkowskiSchwartzTests
    EuclideanDimension.four (by decide)

/-- Two-dimensional spacetime already has a nonvacuous spatial locality test pair. -/
theorem two_dimensional_nonzero_locality_tests_exist :
    ∃ f g : ScalarMinkowskiSchwartzTestFunction EuclideanDimension.two,
      f ≠ 0 ∧ g ≠ 0 ∧ HaveSpacelikeSeparatedTopologicalSupports f g :=
  exists_nonzero_spacelikeSeparated_scalarMinkowskiSchwartzTests
    EuclideanDimension.two (by decide)

/-- Dimension one has no spacelike point pair after its sole coordinate is time. -/
theorem one_dimensional_spacelike_pairs_blocked :
    spacelikeSeparatedPointPairSet EuclideanDimension.one = ∅ :=
  oneDimensional_spacelikeSeparatedPointPairSet_eq_empty

/-- Dimension one cannot satisfy support separation using two nonzero tests. -/
theorem one_dimensional_nonzero_locality_tests_blocked
    {f g : ScalarMinkowskiSchwartzTestFunction EuclideanDimension.one}
    (hf : f ≠ 0) (hg : g ≠ 0) :
    ¬ HaveSpacelikeSeparatedTopologicalSupports f g :=
  oneDimensional_no_nonzero_spacelikeSeparated_schwartzTests hf hg

/-- Support separation is symmetric. -/
theorem exact_support_separation_symmetry
    {d : EuclideanDimension} {f g : ScalarMinkowskiSchwartzTestFunction d}
    (h : HaveSpacelikeSeparatedTopologicalSupports f g) :
    HaveSpacelikeSeparatedTopologicalSupports g f :=
  haveSpacelikeSeparatedTopologicalSupports_comm h

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

/-- Field-field commutation is exact on the same common domain. -/
theorem exact_field_field_locality
    (locality : ScalarWightmanLocalityData fieldData)
    (f g : ScalarMinkowskiSchwartzTestFunction d)
    (hsep : HaveSpacelikeSeparatedTopologicalSupports f g) (ψ : D.domain) :
    fieldData.field f (fieldData.field g ψ) =
      fieldData.field g (fieldData.field f ψ) :=
  locality.field_field f g hsep ψ

/-- Field-adjoint commutation is exact. -/
theorem exact_field_adjoint_locality
    (locality : ScalarWightmanLocalityData fieldData)
    (f g : ScalarMinkowskiSchwartzTestFunction d)
    (hsep : HaveSpacelikeSeparatedTopologicalSupports f g) (ψ : D.domain) :
    fieldData.field f (fieldData.adjointField g ψ) =
      fieldData.adjointField g (fieldData.field f ψ) :=
  locality.field_adjoint f g hsep ψ

/-- Adjoint-field commutation is exact. -/
theorem exact_adjoint_field_locality
    (locality : ScalarWightmanLocalityData fieldData)
    (f g : ScalarMinkowskiSchwartzTestFunction d)
    (hsep : HaveSpacelikeSeparatedTopologicalSupports f g) (ψ : D.domain) :
    fieldData.adjointField f (fieldData.field g ψ) =
      fieldData.field g (fieldData.adjointField f ψ) :=
  locality.adjoint_field f g hsep ψ

/-- Adjoint-adjoint commutation is exact. -/
theorem exact_adjoint_adjoint_locality
    (locality : ScalarWightmanLocalityData fieldData)
    (f g : ScalarMinkowskiSchwartzTestFunction d)
    (hsep : HaveSpacelikeSeparatedTopologicalSupports f g) (ψ : D.domain) :
    fieldData.adjointField f (fieldData.adjointField g ψ) =
      fieldData.adjointField g (fieldData.adjointField f ψ) :=
  locality.adjoint_adjoint f g hsep ψ

/-- Replacing the local field-field product by a mismatched domain vector is impossible. -/
theorem disconnected_local_product_blocked
    (locality : ScalarWightmanLocalityData fieldData)
    (f g : ScalarMinkowskiSchwartzTestFunction d)
    (hsep : HaveSpacelikeSeparatedTopologicalSupports f g) (ψ χ : D.domain)
    (hreplacement : fieldData.field f (fieldData.field g ψ) = χ)
    (hmismatch : χ ≠ fieldData.field g (fieldData.field f ψ)) : False := by
  apply hmismatch
  rw [← locality.field_field f g hsep ψ]
  exact hreplacement.symm

end YangMills.Minkowski.WightmanLocality.Probes
