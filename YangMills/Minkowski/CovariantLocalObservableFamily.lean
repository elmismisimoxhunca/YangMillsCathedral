/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Minkowski.TemperedLocalObservableProducts
import YangMills.Minkowski.WightmanCovariance
import YangMills.Minkowski.WightmanLocality

/-!
# Covariant local observable families on one Wightman chain

Clay/Jaffe–Witten, pp. 5–6, requires gauge-invariant local quantum fields to act on the physical
Hilbert space, transform covariantly under the same Poincaré representation, and commute at
spacelike separation. This module adds those family-wide obligations to the exact shared-domain
local-observable interface.

An explicit label involution and conjugated-test adjoint relation keep complex observable families
closed under adjoints. No label is interpreted as a curvature polynomial, no gauge-redundancy action
is introduced on the physical Hilbert space, and no family, OPE, theory, or mass gap is constructed.
-/

namespace YangMills.Minkowski

/-- Adjoint closure, exact scalar covariance on an explicit scalar-label sector, and bosonic
locality for one labeled local-observable family on the same Poincaré representation/common domain
chain. Labels outside the scalar sector are available to separate tensor/spin interfaces. -/
structure CovariantLocalObservableFamilyData
    {d : EuclideanDimension} {G : Type*}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {lift : ProperOrthochronousPoincareLiftData d G}
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H]
    {U : StronglyContinuousUnitaryPoincareRepresentation lift H}
    {vacuumData : PoincareInvariantVacuumData U}
    {D : CommonInvariantDomainData vacuumData}
    (family : TemperedLocalObservableFamilyData D) where
  /-- Label of the adjoint local observable. -/
  adjointLabel : family.Label → family.Label
  adjointLabel_involutive : Function.Involutive adjointLabel
  adjointLabel_unit : adjointLabel family.unitLabel = family.unitLabel
  /-- Labels designated to transform as Lorentz scalars. Tensor/spin labels remain in the same family
  but use separate source-facing covariance interfaces. -/
  scalarLabel : Set family.Label
  /-- The unit and distinguished scalar Wightman label belong to the scalar sector. -/
  unitLabel_mem_scalar : family.unitLabel ∈ scalarLabel
  nontrivialLabel_mem_scalar : family.nontrivialLabel ∈ scalarLabel
  /-- The scalar sector is closed under the exact label adjoint. -/
  adjointLabel_mem_scalar : ∀ A, A ∈ scalarLabel → adjointLabel A ∈ scalarLabel
  /-- Exact common-domain adjoint relation, with conjugation on the scalar Schwartz test. -/
  adjoint_relation : ∀ A ψ φ f,
    @inner ℂ H _ ψ.val (family.operator (adjointLabel A) f φ).val =
      @inner ℂ H _
        (family.operator A (conjugateScalarMinkowskiSchwartzTestFunction f) ψ).val φ.val
  /-- Every designated scalar label transforms under the same physical lift representation and
  scalar affine test pullback. No scalar law is imposed on tensor/spin labels. -/
  operator_covariant : ∀ A, A ∈ scalarLabel → ∀ g f ψ,
    D.domainUnitary g
        (family.operator A f ((D.domainUnitary g).symm ψ)) =
      family.operator A
        (pullbackScalarMinkowskiSchwartzTestFunction d (lift.projection g) f) ψ
  /-- Every ordered pair of labeled bosonic observables commutes on the exact common domain when the
  closed topological supports of the tests are spacelike separated. -/
  operator_local : ∀ A B f g,
    HaveSpacelikeSeparatedTopologicalSupports f g →
      ∀ ψ,
        family.operator A f (family.operator B g ψ) =
          family.operator B g (family.operator A f ψ)

/-- Covariance applies in particular to the exact nontrivial observable label. -/
theorem CovariantLocalObservableFamilyData.nontrivial_operator_covariant
    {d : EuclideanDimension} {G : Type*}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {lift : ProperOrthochronousPoincareLiftData d G}
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H]
    {U : StronglyContinuousUnitaryPoincareRepresentation lift H}
    {vacuumData : PoincareInvariantVacuumData U}
    {D : CommonInvariantDomainData vacuumData}
    {family : TemperedLocalObservableFamilyData D}
    (data : CovariantLocalObservableFamilyData family)
    (g : G) (f : ScalarMinkowskiSchwartzTestFunction d) (ψ : D.domain) :
    D.domainUnitary g
        (family.operator family.nontrivialLabel f ((D.domainUnitary g).symm ψ)) =
      family.operator family.nontrivialLabel
        (pullbackScalarMinkowskiSchwartzTestFunction d (lift.projection g) f) ψ :=
  data.operator_covariant family.nontrivialLabel data.nontrivialLabel_mem_scalar g f ψ

/-- Applying the label adjoint twice restores the exact original local operator label. -/
theorem CovariantLocalObservableFamilyData.adjointLabel_adjointLabel
    {d : EuclideanDimension} {G : Type*}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {lift : ProperOrthochronousPoincareLiftData d G}
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H]
    {U : StronglyContinuousUnitaryPoincareRepresentation lift H}
    {vacuumData : PoincareInvariantVacuumData U}
    {D : CommonInvariantDomainData vacuumData}
    {family : TemperedLocalObservableFamilyData D}
    (data : CovariantLocalObservableFamilyData family) (A : family.Label) :
    data.adjointLabel (data.adjointLabel A) = A :=
  data.adjointLabel_involutive A

end YangMills.Minkowski
