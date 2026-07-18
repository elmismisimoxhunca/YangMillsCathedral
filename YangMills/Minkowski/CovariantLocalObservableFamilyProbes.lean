/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Minkowski.CovariantLocalObservableFamily

/-!
# Hostile probes for covariant local observable families

The probes expose nontrivial-label covariance, exact adjoint closure, and locality on explicit
nonzero spacelike tests in dimensions at least two. No family datum is constructed.
-/

namespace YangMills.Minkowski.CovariantLocalObservableFamily.Probes

variable
    {d : EuclideanDimension} {G : Type*}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {lift : ProperOrthochronousPoincareLiftData d G}
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H]
    {U : StronglyContinuousUnitaryPoincareRepresentation lift H}
    {vacuumData : PoincareInvariantVacuumData U}
    {D : CommonInvariantDomainData vacuumData}
    {family : TemperedLocalObservableFamilyData D}

/-- Covariance cannot be restricted to the unit label. -/
theorem exact_nontrivial_label_covariance
    (data : CovariantLocalObservableFamilyData family)
    (g : G) (f : ScalarMinkowskiSchwartzTestFunction d) (ψ : D.domain) :
    D.domainUnitary g
        (family.operator family.nontrivialLabel f ((D.domainUnitary g).symm ψ)) =
      family.operator family.nontrivialLabel
        (pullbackScalarMinkowskiSchwartzTestFunction d (lift.projection g) f) ψ :=
  data.nontrivial_operator_covariant g f ψ

/-- The unit label remains the unit under the exact adjoint involution. -/
theorem exact_unit_adjoint_label
    (data : CovariantLocalObservableFamilyData family) :
    data.adjointLabel family.unitLabel = family.unitLabel :=
  data.adjointLabel_unit

/-- A one-way label map cannot pass as adjoint closure. -/
theorem one_way_adjoint_label_blocked
    (data : CovariantLocalObservableFamilyData family) (A : family.Label) :
    data.adjointLabel (data.adjointLabel A) = A :=
  data.adjointLabel_adjointLabel A

/-- The adjoint relation remains on the same common domain and conjugated test. -/
theorem exact_family_adjoint_relation
    (data : CovariantLocalObservableFamilyData family)
    (A : family.Label) (ψ φ : D.domain)
    (f : ScalarMinkowskiSchwartzTestFunction d) :
    @inner ℂ H _ ψ.val (family.operator (data.adjointLabel A) f φ).val =
      @inner ℂ H _
        (family.operator A (conjugateScalarMinkowskiSchwartzTestFunction f) ψ).val φ.val :=
  data.adjoint_relation A ψ φ f

/-- Every pair of labels—not merely a disconnected distinguished field—obeys exact locality. -/
theorem exact_all_label_locality
    (data : CovariantLocalObservableFamilyData family)
    (A B : family.Label) (f g : ScalarMinkowskiSchwartzTestFunction d)
    (hspacelike : HaveSpacelikeSeparatedTopologicalSupports f g) (ψ : D.domain) :
    family.operator A f (family.operator B g ψ) =
      family.operator B g (family.operator A f ψ) :=
  data.operator_local A B f g hspacelike ψ

/-- From dimension two onward, locality is exercised by genuinely nonzero separated tests. -/
theorem nonzero_locality_tests_exist
    (data : CovariantLocalObservableFamilyData family)
    (h : 2 ≤ d.value) :
    ∃ (f g : ScalarMinkowskiSchwartzTestFunction d),
      f ≠ 0 ∧ g ≠ 0 ∧ HaveSpacelikeSeparatedTopologicalSupports f g ∧
      ∀ (A B : family.Label) (ψ : D.domain),
        family.operator A f (family.operator B g ψ) =
          family.operator B g (family.operator A f ψ) := by
  rcases exists_nonzero_spacelikeSeparated_scalarMinkowskiSchwartzTests d h with
    ⟨f, g, hf, hg, hspace⟩
  exact ⟨f, g, hf, hg, hspace, fun A B ψ => data.operator_local A B f g hspace ψ⟩

end YangMills.Minkowski.CovariantLocalObservableFamily.Probes
