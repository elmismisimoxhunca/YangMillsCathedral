/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Minkowski.PoincareComplexSignKernel
import YangMills.Minkowski.ScalarWightmanAxiomSurface

/-!
# Triviality of the cover kernel in a cyclic scalar Wightman realization

For a scalar field, an element projecting to the affine identity leaves every test function fixed.
Exact covariance therefore makes its unitary commute with the field and adjoint on the common
domain. It fixes the vacuum, hence every finite field word. Vacuum cyclicity and continuity then
force the unitary to be the identity on the whole Hilbert space.

This is derived from an already supplied scalar Wightman surface. It constructs no representation,
field, theory, or cover, and it makes no claim for spinorial fields.
-/

namespace YangMills.Minkowski

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

/-- A lift element projecting to the affine identity commutes with the scalar field on the exact
common domain. -/
theorem ScalarWightmanFieldCovarianceData.field_commutes_of_projection_eq_identity
    (covariance : ScalarWightmanFieldCovarianceData fieldData)
    (g : G)
    (projection_eq : cover.projection g = ProperOrthochronousPoincareTransformation.identity d)
    (f : ScalarMinkowskiSchwartzTestFunction d) (ψ : D.domain) :
    D.domainUnitary g (fieldData.field f ψ) =
      fieldData.field f (D.domainUnitary g ψ) := by
  have transformed := covariance.field_covariant g f (D.domainUnitary g ψ)
  simpa [projection_eq] using transformed

/-- The same kernel element commutes with the exact adjoint field. -/
theorem ScalarWightmanFieldCovarianceData.adjoint_commutes_of_projection_eq_identity
    (covariance : ScalarWightmanFieldCovarianceData fieldData)
    (g : G)
    (projection_eq : cover.projection g = ProperOrthochronousPoincareTransformation.identity d)
    (f : ScalarMinkowskiSchwartzTestFunction d) (ψ : D.domain) :
    D.domainUnitary g (fieldData.adjointField f ψ) =
      fieldData.adjointField f (D.domainUnitary g ψ) := by
  have transformed := covariance.adjoint_covariant g f (D.domainUnitary g ψ)
  simpa [projection_eq] using transformed

/-- One field-or-adjoint letter commutes with an identity-projecting lift. -/
theorem ScalarWightmanFieldCovarianceData.letter_commutes_of_projection_eq_identity
    (covariance : ScalarWightmanFieldCovarianceData fieldData)
    (g : G)
    (projection_eq : cover.projection g = ProperOrthochronousPoincareTransformation.identity d)
    (letter : ScalarWightmanFieldLetter d) (ψ : D.domain) :
    D.domainUnitary g (letter.apply fieldData ψ) =
      letter.apply fieldData (D.domainUnitary g ψ) := by
  cases letter with
  | field f => exact covariance.field_commutes_of_projection_eq_identity g projection_eq f ψ
  | adjoint f => exact covariance.adjoint_commutes_of_projection_eq_identity g projection_eq f ψ

/-- Every finite field/adjoint word on the vacuum is fixed by an identity-projecting lift. -/
theorem ScalarWightmanFieldCovarianceData.wordOnVacuum_fixed_of_projection_eq_identity
    (covariance : ScalarWightmanFieldCovarianceData fieldData)
    (g : G)
    (projection_eq : cover.projection g = ProperOrthochronousPoincareTransformation.identity d)
    (word : List (ScalarWightmanFieldLetter d)) :
    D.domainUnitary g (scalarWightmanFieldWordOnVacuum fieldData word) =
      scalarWightmanFieldWordOnVacuum fieldData word := by
  induction word with
  | nil => exact D.domainUnitary_vacuum g
  | cons letter word ih =>
      change D.domainUnitary g
          (letter.apply fieldData (scalarWightmanFieldWordOnVacuum fieldData word)) =
        letter.apply fieldData (scalarWightmanFieldWordOnVacuum fieldData word)
      rw [covariance.letter_commutes_of_projection_eq_identity g projection_eq, ih]

/-- Scalar covariance and vacuum cyclicity force every identity-projecting lift element to act
trivially on the whole physical Hilbert space. -/
theorem ScalarWightmanAxiomSurfaceData.unitary_eq_refl_of_projection_eq_identity
    (surface : ScalarWightmanAxiomSurfaceData fieldData)
    (g : G)
    (projection_eq : cover.projection g = ProperOrthochronousPoincareTransformation.identity d) :
    U.unitary g = LinearIsometryEquiv.refl ℂ H := by
  let unitaryCLM : H →L[ℂ] H :=
    (U.unitary g).toContinuousLinearEquiv.toContinuousLinearMap
  have densePolynomial : Dense
      (scalarWightmanFieldPolynomialVacuumSubmodule fieldData : Set H) :=
    Submodule.dense_iff_topologicalClosure_eq_top.mpr surface.cyclicity
  have denseSpan : Dense
      (Submodule.span ℂ
        (Set.range (fun word =>
          (scalarWightmanFieldWordOnVacuum fieldData word).val)) : Set H) := by
    simpa [scalarWightmanFieldPolynomialVacuumSubmodule] using densePolynomial
  have clm_eq : unitaryCLM = ContinuousLinearMap.id ℂ H := by
    apply ContinuousLinearMap.ext_on denseSpan
    intro ψ hψ
    rcases hψ with ⟨word, rfl⟩
    change U.unitary g
        ((scalarWightmanFieldWordOnVacuum fieldData word : D.domain) : H) =
      ((scalarWightmanFieldWordOnVacuum fieldData word : D.domain) : H)
    have fixed := surface.covariance.wordOnVacuum_fixed_of_projection_eq_identity
      g projection_eq word
    exact congrArg Subtype.val fixed
  apply LinearIsometryEquiv.ext
  intro ψ
  simpa [unitaryCLM] using congrArg (fun f : H →L[ℂ] H => f ψ) clm_eq

/-- A fully connected scalar Wightman chain bundled over one exact lift index. This package exists
only to transport the dependent chain across an equality of lift records; it asserts no existence. -/
structure ScalarWightmanAxiomChainData
    (d : EuclideanDimension)
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (lift : ProperOrthochronousPoincareLiftData d G)
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] where
  U : StronglyContinuousUnitaryPoincareRepresentation lift H
  vacuumData : PoincareInvariantVacuumData U
  D : CommonInvariantDomainData vacuumData
  fieldData : ScalarWightmanFieldOnCommonDomainData D
  surface : ScalarWightmanAxiomSurfaceData fieldData

/-- Transport a complete dependent scalar chain across an equality of lift records. -/
def ScalarWightmanAxiomChainData.transport
    {d : EuclideanDimension}
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {firstLift secondLift : ProperOrthochronousPoincareLiftData d G}
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H]
    (chain : ScalarWightmanAxiomChainData d firstLift H)
    (lift_eq : firstLift = secondLift) :
    ScalarWightmanAxiomChainData d secondLift H := by
  subst secondLift
  exact chain

/-- Transport changes only the lift index; its exact Hilbert unitary remains the original one. -/
@[simp] theorem ScalarWightmanAxiomChainData.transport_unitary
    {d : EuclideanDimension}
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {firstLift secondLift : ProperOrthochronousPoincareLiftData d G}
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H]
    (chain : ScalarWightmanAxiomChainData d firstLift H)
    (lift_eq : firstLift = secondLift) (g : G) :
    (chain.transport lift_eq).U.unitary g = chain.U.unitary g := by
  subst secondLift
  rfl

/-- In particular, the derived negative sign of an exact two-sheet cover acts trivially in every
cyclic scalar Wightman realization over that cover. -/
theorem ScalarWightmanAxiomSurfaceData.negativeKernel_unitary_eq_refl
    {targetGroup : ProperOrthochronousPoincareTargetGroupData d}
    {doubleCover : ProperOrthochronousPoincareDoubleCoverData d G}
    {U : StronglyContinuousUnitaryPoincareRepresentation
      doubleCover.toProperOrthochronousPoincareLiftData H}
    {vacuumData : PoincareInvariantVacuumData U}
    {D : CommonInvariantDomainData vacuumData}
    {fieldData : ScalarWightmanFieldOnCommonDomainData D}
    (surface : ScalarWightmanAxiomSurfaceData fieldData) :
    U.unitary (negativeProjectionKernelElement d targetGroup doubleCover : G) =
      LinearIsometryEquiv.refl ℂ H :=
  surface.unitary_eq_refl_of_projection_eq_identity
    (negativeProjectionKernelElement d targetGroup doubleCover : G)
    (negativeProjectionKernelElement_mem_kernel d targetGroup doubleCover)

/-- Transport the whole dependent scalar chain across an equality between the selected lift and the
exact double-cover lift, then apply negative-sign triviality. -/
theorem ScalarWightmanAxiomChainData.negativeKernel_unitary_eq_refl_of_lift_eq
    {d : EuclideanDimension}
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {targetGroup : ProperOrthochronousPoincareTargetGroupData d}
    {doubleCover : ProperOrthochronousPoincareDoubleCoverData d G}
    {lift : ProperOrthochronousPoincareLiftData d G}
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H]
    (chain : ScalarWightmanAxiomChainData d lift H)
    (lift_eq : doubleCover.toProperOrthochronousPoincareLiftData = lift) :
    chain.U.unitary (negativeProjectionKernelElement d targetGroup doubleCover : G) =
      LinearIsometryEquiv.refl ℂ H := by
  subst lift
  exact chain.surface.negativeKernel_unitary_eq_refl

end

end YangMills.Minkowski
