/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Minkowski.ScalarWightmanKernelTriviality

/-!
# Hostile probes for scalar Wightman kernel triviality

The probes retain the exact projection, covariance, vacuum, cyclic word span, and Hilbert unitary.
No scalar surface or representation is constructed.
-/

namespace YangMills.Minkowski.ScalarWightmanKernelTriviality.Probes

noncomputable section

variable
    {d : EuclideanDimension}
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {cover : ProperOrthochronousPoincareLiftData d G}
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H]
    {U : StronglyContinuousUnitaryPoincareRepresentation cover H}
    {vacuumData : PoincareInvariantVacuumData U}
    {D : CommonInvariantDomainData vacuumData}
    {fieldData : ScalarWightmanFieldOnCommonDomainData D}
    (surface : ScalarWightmanAxiomSurfaceData fieldData)
    (g : G)
    (projection_eq : cover.projection g =
      ProperOrthochronousPoincareTransformation.identity d)

include surface projection_eq

/-- Identity-projecting elements commute with the exact scalar field on the common domain. -/
theorem exact_field_commutation
    (f : ScalarMinkowskiSchwartzTestFunction d) (ψ : D.domain) :
    D.domainUnitary g (fieldData.field f ψ) =
      fieldData.field f (D.domainUnitary g ψ) :=
  surface.covariance.field_commutes_of_projection_eq_identity g projection_eq f ψ

/-- The same statement holds for the exact adjoint, preventing field-only shortcutting. -/
theorem exact_adjoint_commutation
    (f : ScalarMinkowskiSchwartzTestFunction d) (ψ : D.domain) :
    D.domainUnitary g (fieldData.adjointField f ψ) =
      fieldData.adjointField f (D.domainUnitary g ψ) :=
  surface.covariance.adjoint_commutes_of_projection_eq_identity g projection_eq f ψ

/-- Every finite field/adjoint word on the selected vacuum is fixed. -/
theorem exact_word_fixed (word : List (ScalarWightmanFieldLetter d)) :
    D.domainUnitary g (scalarWightmanFieldWordOnVacuum fieldData word) =
      scalarWightmanFieldWordOnVacuum fieldData word :=
  surface.covariance.wordOnVacuum_fixed_of_projection_eq_identity g projection_eq word

/-- Cyclicity upgrades wordwise invariance to exact identity on the full Hilbert carrier. -/
theorem exact_full_hilbert_triviality :
    U.unitary g = LinearIsometryEquiv.refl ℂ H :=
  surface.unitary_eq_refl_of_projection_eq_identity g projection_eq

omit surface projection_eq in
/-- The derived negative sign therefore acts trivially in a scalar realization of the exact cover. -/
theorem exact_negative_sign_triviality
    {targetGroup : ProperOrthochronousPoincareTargetGroupData d}
    {doubleCover : ProperOrthochronousPoincareDoubleCoverData d G}
    {U₂ : StronglyContinuousUnitaryPoincareRepresentation
      doubleCover.toProperOrthochronousPoincareLiftData H}
    {vacuum₂ : PoincareInvariantVacuumData U₂}
    {D₂ : CommonInvariantDomainData vacuum₂}
    {field₂ : ScalarWightmanFieldOnCommonDomainData D₂}
    (surface₂ : ScalarWightmanAxiomSurfaceData field₂) :
    U₂.unitary (negativeProjectionKernelElement d targetGroup doubleCover : G) =
      LinearIsometryEquiv.refl ℂ H :=
  surface₂.negativeKernel_unitary_eq_refl

omit surface projection_eq in
/-- A propositionally equal lift index transports the whole dependent chain before applying the
same negative-sign theorem. -/
theorem exact_lift_equality_transport
    {targetGroup : ProperOrthochronousPoincareTargetGroupData d}
    {doubleCover : ProperOrthochronousPoincareDoubleCoverData d G}
    {otherLift : ProperOrthochronousPoincareLiftData d G}
    (chain : ScalarWightmanAxiomChainData d otherLift H)
    (lift_eq : doubleCover.toProperOrthochronousPoincareLiftData = otherLift) :
    chain.U.unitary (negativeProjectionKernelElement d targetGroup doubleCover : G) =
      LinearIsometryEquiv.refl ℂ H :=
  chain.negativeKernel_unitary_eq_refl_of_lift_eq lift_eq

end

end YangMills.Minkowski.ScalarWightmanKernelTriviality.Probes
