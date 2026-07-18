/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Minkowski.WightmanField

/-!
# Scalar Wightman field covariance

Streater–Wightman, printed p. 99, axiom `II`, equations `(3-4)`–`(3-5)`, requires covariance under
the same Poincaré representation and defines the transformed test by
`({a,Λ}f)(x) = f(Λ⁻¹(x-a))`. This module constructs that exact affine Schwartz pullback and requires
both the field and adjoint field on the common domain to transform by conjugation with the same
restricted physical unitary.

No covariance inhabitant, locality, cyclicity, spectrum, reconstruction, existence theorem, or mass
gap is introduced.
-/

namespace YangMills.Minkowski

/-- Pullback of a scalar Minkowski Schwartz test by the inverse affine Poincaré action,
`f(x) ↦ f(Λ⁻¹(x-a))`. -/
noncomputable def pullbackScalarMinkowskiSchwartzTestFunction
    (d : EuclideanDimension) (p : ProperOrthochronousPoincareTransformation d) :
    ScalarMinkowskiSchwartzTestFunction d →L[ℂ]
      ScalarMinkowskiSchwartzTestFunction d :=
  (SchwartzMap.compSubConstCLM ℂ p.translation).comp
    (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
      p.lorentz.linear.symm.toContinuousLinearEquiv)

/-- Exact source-facing pointwise affine pullback formula. -/
@[simp] theorem pullbackScalarMinkowskiSchwartzTestFunction_apply
    (d : EuclideanDimension) (p : ProperOrthochronousPoincareTransformation d)
    (f : ScalarMinkowskiSchwartzTestFunction d) (x : Spacetime d) :
    pullbackScalarMinkowskiSchwartzTestFunction d p f x =
      f (p.lorentz.linear.symm (x - p.translation)) := by
  simp [pullbackScalarMinkowskiSchwartzTestFunction]

/-- Identity Poincaré pullback fixes every exact Minkowski Schwartz test. -/
@[simp] theorem pullbackScalarMinkowskiSchwartzTestFunction_identity
    (d : EuclideanDimension) (f : ScalarMinkowskiSchwartzTestFunction d) :
    pullbackScalarMinkowskiSchwartzTestFunction d
      (ProperOrthochronousPoincareTransformation.identity d) f = f := by
  ext x
  simp [ProperOrthochronousPoincareTransformation.identity,
    ProperOrthochronousLorentzTransformation.identity]

/-- A pure translation has exact test pullback `f(x-a)`. -/
@[simp] theorem pullbackScalarMinkowskiSchwartzTestFunction_pureTranslation
    (d : EuclideanDimension) (a : Spacetime d)
    (f : ScalarMinkowskiSchwartzTestFunction d) (x : Spacetime d) :
    pullbackScalarMinkowskiSchwartzTestFunction d
        (ProperOrthochronousPoincareTransformation.pureTranslation d a) f x =
      f (x - a) := by
  simp [ProperOrthochronousPoincareTransformation.pureTranslation,
    ProperOrthochronousLorentzTransformation.identity]

/-- Affine pullback is injective and therefore preserves and reflects vanishing. -/
@[simp] theorem pullbackScalarMinkowskiSchwartzTestFunction_eq_zero_iff
    (d : EuclideanDimension) (p : ProperOrthochronousPoincareTransformation d)
    (f : ScalarMinkowskiSchwartzTestFunction d) :
    pullbackScalarMinkowskiSchwartzTestFunction d p f = 0 ↔ f = 0 := by
  constructor
  · intro hzero
    ext y
    have atPoint := congrArg
      (fun q : ScalarMinkowskiSchwartzTestFunction d =>
        q (p.lorentz.linear y + p.translation)) hzero
    rw [pullbackScalarMinkowskiSchwartzTestFunction_apply] at atPoint
    have harg :
        p.lorentz.linear.symm
          (p.lorentz.linear y + p.translation - p.translation) = y := by
      rw [add_sub_cancel_right]
      exact p.lorentz.linear.symm_apply_apply y
    rw [harg] at atPoint
    simpa using atPoint
  · rintro rfl
    simp

/-- Scalar field and adjoint covariance under the same lift element, projected affine
transformation, restricted domain unitary, and common domain. -/
structure ScalarWightmanFieldCovarianceData
    {d : EuclideanDimension} {G : Type*}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {lift : ProperOrthochronousPoincareLiftData d G}
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H]
    {U : StronglyContinuousUnitaryPoincareRepresentation lift H}
    {vacuumData : PoincareInvariantVacuumData U}
    {D : CommonInvariantDomainData vacuumData}
    (fieldData : ScalarWightmanFieldOnCommonDomainData D) : Prop where
  /-- Exact scalar field covariance `U(g) Φ(f) U(g)⁻¹ = Φ(g·f)` on the common domain. -/
  field_covariant : ∀ g f ψ,
    D.domainUnitary g (fieldData.field f ((D.domainUnitary g).symm ψ)) =
      fieldData.field
        (pullbackScalarMinkowskiSchwartzTestFunction d (lift.projection g) f) ψ
  /-- The adjoint field transforms under the same physical data and test pullback. -/
  adjoint_covariant : ∀ g f ψ,
    D.domainUnitary g (fieldData.adjointField f ((D.domainUnitary g).symm ψ)) =
      fieldData.adjointField
        (pullbackScalarMinkowskiSchwartzTestFunction d (lift.projection g) f) ψ

end YangMills.Minkowski
