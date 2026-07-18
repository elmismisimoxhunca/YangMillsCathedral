/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Minkowski.WightmanCovariance

/-!
# Hostile probes for scalar Wightman covariance

The probes force the inverse-affine pullback convention, a wired nonzero translation, covariance of
both field and adjoint under the same unitary/domain data, and exact specialization to the derived
translation subgroup. No covariant field is constructed.
-/

namespace YangMills.Minkowski.WightmanCovariance.Probes

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

/-- The exact inverse-affine source convention is exposed pointwise. -/
theorem exact_affine_test_pullback
    (p : ProperOrthochronousPoincareTransformation d)
    (f : ScalarMinkowskiSchwartzTestFunction d) (x : Spacetime d) :
    pullbackScalarMinkowskiSchwartzTestFunction d p f x =
      f (p.lorentz.linear.symm (x - p.translation)) :=
  pullbackScalarMinkowskiSchwartzTestFunction_apply d p f x

/-- A pure translation sends a test to `f(x-a)`, not `f(x+a)`. -/
theorem exact_pure_translation_pullback
    (a : Spacetime d) (f : ScalarMinkowskiSchwartzTestFunction d) (x : Spacetime d) :
    pullbackScalarMinkowskiSchwartzTestFunction d
        (ProperOrthochronousPoincareTransformation.pureTranslation d a) f x =
      f (x - a) :=
  pullbackScalarMinkowskiSchwartzTestFunction_pureTranslation d a f x

/-- Translating the origin-centered bump by `a` gives value one at `x=a`, detecting both the
translation parameter and its sign. -/
theorem translated_bump_at_translation
    (a : Spacetime d) :
    pullbackScalarMinkowskiSchwartzTestFunction d
      (ProperOrthochronousPoincareTransformation.pureTranslation d a)
      (scalarMinkowskiSchwartzBump d) a = 1 := by
  rw [pullbackScalarMinkowskiSchwartzTestFunction_pureTranslation]
  rw [sub_self]
  exact scalarMinkowskiSchwartzBump_zero d

/-- Every affine pullback of the explicit bump remains nonzero. -/
theorem transformed_bump_ne_zero
    (p : ProperOrthochronousPoincareTransformation d) :
    pullbackScalarMinkowskiSchwartzTestFunction d p
      (scalarMinkowskiSchwartzBump d) ≠ 0 := by
  intro hzero
  exact scalarMinkowskiSchwartzBump_ne_zero d
    ((pullbackScalarMinkowskiSchwartzTestFunction_eq_zero_iff d p
      (scalarMinkowskiSchwartzBump d)).mp hzero)

/-- Scalar field covariance uses the exact same restricted physical unitary and domain. -/
theorem exact_field_covariance
    (covariance : ScalarWightmanFieldCovarianceData fieldData)
    (g : G) (f : ScalarMinkowskiSchwartzTestFunction d) (ψ : D.domain) :
    D.domainUnitary g (fieldData.field f ((D.domainUnitary g).symm ψ)) =
      fieldData.field
        (pullbackScalarMinkowskiSchwartzTestFunction d (lift.projection g) f) ψ :=
  covariance.field_covariant g f ψ

/-- Adjoint covariance is tied to those same data. -/
theorem exact_adjoint_covariance
    (covariance : ScalarWightmanFieldCovarianceData fieldData)
    (g : G) (f : ScalarMinkowskiSchwartzTestFunction d) (ψ : D.domain) :
    D.domainUnitary g (fieldData.adjointField f ((D.domainUnitary g).symm ψ)) =
      fieldData.adjointField
        (pullbackScalarMinkowskiSchwartzTestFunction d (lift.projection g) f) ψ :=
  covariance.adjoint_covariant g f ψ

/-- Covariance along physical translations is obtained from the same lift-group representation and
projects to the exact pure affine translation. -/
theorem exact_field_translation_covariance
    (covariance : ScalarWightmanFieldCovarianceData fieldData)
    (a : Spacetime d) (f : ScalarMinkowskiSchwartzTestFunction d) (ψ : D.domain) :
    D.domainUnitary (lift.translation (Multiplicative.ofAdd a))
        (fieldData.field f
          ((D.domainUnitary (lift.translation (Multiplicative.ofAdd a))).symm ψ)) =
      fieldData.field
        (pullbackScalarMinkowskiSchwartzTestFunction d
          (ProperOrthochronousPoincareTransformation.pureTranslation d a) f) ψ := by
  rw [← lift.projection_translation a]
  exact covariance.field_covariant
    (lift.translation (Multiplicative.ofAdd a)) f ψ

end YangMills.Minkowski.WightmanCovariance.Probes
