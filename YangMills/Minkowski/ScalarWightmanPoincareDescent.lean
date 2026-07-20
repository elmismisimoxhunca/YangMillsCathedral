/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Minkowski.ScalarWightmanKernelTriviality

/-!
# Descent of a cyclic scalar Wightman representation to affine Poincaré kinematics

Once the kernel of an exact double cover acts trivially, two lifts of the same affine transformation
have the same Hilbert unitary. This module therefore descends the exact cover representation to a
strongly continuous unitary homomorphism on the named affine Poincaré target. Continuity is derived
through the existing quotient-map projection.

The construction is conditional on an already supplied scalar Wightman chain and exact cover. It
constructs no theory, field, cover, or mass gap and does not apply to spinorial representations.
-/

namespace YangMills.Minkowski

open Topology

noncomputable section

variable
    {d : EuclideanDimension}
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {targetGroup : ProperOrthochronousPoincareTargetGroupData d}
    {cover : ProperOrthochronousPoincareDoubleCoverData d G}
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H]
    (chain : ScalarWightmanAxiomChainData
      d cover.toProperOrthochronousPoincareLiftData H)

/-- Two lifts of the same exact affine transformation have the same unitary in a cyclic scalar
Wightman realization. -/
theorem ScalarWightmanAxiomChainData.unitary_eq_of_projection_eq
    (targetGroup : ProperOrthochronousPoincareTargetGroupData d)
    (first second : G)
    (projection_eq : cover.projection first = cover.projection second) :
    chain.U.unitary first = chain.U.unitary second := by
  letI : Group (ProperOrthochronousPoincareTransformation d) := targetGroup.group
  let quotient : properOrthochronousPoincareProjectionKernel d targetGroup cover :=
    ⟨second⁻¹ * first, by
      change targetGroup.projectionMonoidHom cover (second⁻¹ * first) = 1
      rw [map_mul, map_inv]
      change (cover.projection second)⁻¹ * cover.projection first = 1
      rw [projection_eq]
      simp⟩
  have quotient_trivial :
      chain.U.unitary (quotient : G) = LinearIsometryEquiv.refl ℂ H :=
    chain.surface.unitary_eq_refl_of_projection_eq_identity
      (quotient : G) (by
        have property := quotient.property
        change cover.projection (quotient : G) = @One.one _ targetGroup.group.toOne at property
        simpa [targetGroup.one_eq_identity] using property)
  have first_eq : first = second * (quotient : G) := by
    simp [quotient]
  calc
    chain.U.unitary first = chain.U.unitary (second * (quotient : G)) :=
      congrArg chain.U.unitary first_eq
    _ = chain.U.unitary second * chain.U.unitary (quotient : G) :=
      chain.U.unitary.map_mul second quotient
    _ = chain.U.unitary second := by rw [quotient_trivial]; simp

/-- A selected lift of each exact affine Poincaré transformation. Choice disappears from all
observable results through `unitary_eq_of_projection_eq`. -/
noncomputable def selectedAffinePoincareLift
    (p : ProperOrthochronousPoincareTransformation d) : G :=
  Classical.choose (cover.projection_surjective p)

@[simp] theorem selectedAffinePoincareLift_projection
    (p : ProperOrthochronousPoincareTransformation d) :
    cover.projection (selectedAffinePoincareLift (cover := cover) p) = p :=
  Classical.choose_spec (cover.projection_surjective p)

/-- Choice-independent descended unitary at one exact affine transformation. -/
noncomputable def ScalarWightmanAxiomChainData.descendedAffineUnitary
    (p : ProperOrthochronousPoincareTransformation d) : H ≃ₗᵢ[ℂ] H :=
  chain.U.unitary (selectedAffinePoincareLift (cover := cover) p)

/-- Any lift evaluates to the descended affine unitary of its exact projection. -/
theorem ScalarWightmanAxiomChainData.descendedAffineUnitary_projection
    (targetGroup : ProperOrthochronousPoincareTargetGroupData d)
    (g : G) :
    chain.descendedAffineUnitary (cover.projection g) = chain.U.unitary g :=
  chain.unitary_eq_of_projection_eq targetGroup
    (selectedAffinePoincareLift (cover := cover) (cover.projection g)) g
    (selectedAffinePoincareLift_projection (cover := cover) (cover.projection g))

/-- Projection coherence uniquely determines the descended affine unitary family. -/
theorem ScalarWightmanAxiomChainData.descendedAffineUnitary_unique
    (targetGroup : ProperOrthochronousPoincareTargetGroupData d)
    (candidate : ProperOrthochronousPoincareTransformation d → (H ≃ₗᵢ[ℂ] H))
    (candidate_coherent : ∀ g : G, candidate (cover.projection g) = chain.U.unitary g) :
    candidate = chain.descendedAffineUnitary := by
  funext p
  let g := selectedAffinePoincareLift (cover := cover) p
  calc
    candidate p = candidate (cover.projection g) := by
      rw [selectedAffinePoincareLift_projection]
    _ = chain.U.unitary g := candidate_coherent g
    _ = chain.descendedAffineUnitary (cover.projection g) :=
      (chain.descendedAffineUnitary_projection targetGroup g).symm
    _ = chain.descendedAffineUnitary p := by
      rw [selectedAffinePoincareLift_projection]

/-- The descended unitary restricted to the exact common invariant domain. -/
noncomputable def ScalarWightmanAxiomChainData.descendedAffineDomainUnitary
    (p : ProperOrthochronousPoincareTransformation d) :
    chain.D.domain ≃ₗᵢ[ℂ] chain.D.domain :=
  chain.D.domainUnitary (selectedAffinePoincareLift (cover := cover) p)

/-- Restriction to the domain is likewise independent of the selected lift. -/
theorem ScalarWightmanAxiomChainData.descendedAffineDomainUnitary_projection
    (targetGroup : ProperOrthochronousPoincareTargetGroupData d)
    (g : G) :
    chain.descendedAffineDomainUnitary (cover.projection g) = chain.D.domainUnitary g := by
  apply LinearIsometryEquiv.ext
  intro ψ
  apply Subtype.ext
  change chain.U.unitary
      (selectedAffinePoincareLift (cover := cover) (cover.projection g)) ψ =
    chain.U.unitary g ψ
  exact congrArg (fun unitary : H ≃ₗᵢ[ℂ] H => unitary ψ)
    (chain.descendedAffineUnitary_projection targetGroup g)

/-- Scalar-field covariance descends to the exact affine Poincaré target with no lift appearing in
the statement. -/
theorem ScalarWightmanAxiomChainData.field_covariant_descendedAffine
    (p : ProperOrthochronousPoincareTransformation d)
    (f : ScalarMinkowskiSchwartzTestFunction d) (ψ : chain.D.domain) :
    chain.descendedAffineDomainUnitary p
        (chain.fieldData.field f ((chain.descendedAffineDomainUnitary p).symm ψ)) =
      chain.fieldData.field (pullbackScalarMinkowskiSchwartzTestFunction d p f) ψ := by
  have covariance := chain.surface.covariance.field_covariant
    (selectedAffinePoincareLift (cover := cover) p) f ψ
  simpa [ScalarWightmanAxiomChainData.descendedAffineDomainUnitary] using covariance

/-- The exact adjoint-field covariance descends through the same affine-domain unitary. -/
theorem ScalarWightmanAxiomChainData.adjoint_covariant_descendedAffine
    (p : ProperOrthochronousPoincareTransformation d)
    (f : ScalarMinkowskiSchwartzTestFunction d) (ψ : chain.D.domain) :
    chain.descendedAffineDomainUnitary p
        (chain.fieldData.adjointField f ((chain.descendedAffineDomainUnitary p).symm ψ)) =
      chain.fieldData.adjointField (pullbackScalarMinkowskiSchwartzTestFunction d p f) ψ := by
  have covariance := chain.surface.covariance.adjoint_covariant
    (selectedAffinePoincareLift (cover := cover) p) f ψ
  simpa [ScalarWightmanAxiomChainData.descendedAffineDomainUnitary] using covariance

/-- The descended scalar unitaries form a homomorphism for the exact named affine target law. -/
noncomputable def ScalarWightmanAxiomChainData.descendedAffineUnitaryHom :
    letI : Group (ProperOrthochronousPoincareTransformation d) := targetGroup.group
    ProperOrthochronousPoincareTransformation d →* (H ≃ₗᵢ[ℂ] H) := by
  letI : Group (ProperOrthochronousPoincareTransformation d) := targetGroup.group
  exact
    { toFun := chain.descendedAffineUnitary
      map_one' := by
        apply chain.surface.unitary_eq_refl_of_projection_eq_identity
        exact (selectedAffinePoincareLift_projection (cover := cover)
          (1 : ProperOrthochronousPoincareTransformation d)).trans
            targetGroup.one_eq_identity
      map_mul' := by
        intro first second
        change chain.U.unitary
            (selectedAffinePoincareLift (cover := cover) (first * second)) =
          chain.U.unitary (selectedAffinePoincareLift (cover := cover) first) *
            chain.U.unitary (selectedAffinePoincareLift (cover := cover) second)
        have projectionEquality :
            cover.projection (selectedAffinePoincareLift (cover := cover) (first * second)) =
              cover.projection
                (selectedAffinePoincareLift (cover := cover) first *
                  selectedAffinePoincareLift (cover := cover) second) := by
          rw [selectedAffinePoincareLift_projection]
          change first * second = targetGroup.projectionMonoidHom cover
            (selectedAffinePoincareLift (cover := cover) first *
              selectedAffinePoincareLift (cover := cover) second)
          rw [map_mul, targetGroup.projectionMonoidHom_apply,
            targetGroup.projectionMonoidHom_apply,
            selectedAffinePoincareLift_projection,
            selectedAffinePoincareLift_projection]
        calc
          chain.U.unitary
              (selectedAffinePoincareLift (cover := cover) (first * second)) =
            chain.U.unitary
              (selectedAffinePoincareLift (cover := cover) first *
                selectedAffinePoincareLift (cover := cover) second) :=
            chain.unitary_eq_of_projection_eq targetGroup _ _ projectionEquality
          _ = chain.U.unitary (selectedAffinePoincareLift (cover := cover) first) *
              chain.U.unitary (selectedAffinePoincareLift (cover := cover) second) :=
            chain.U.unitary.map_mul _ _ }

@[simp] theorem ScalarWightmanAxiomChainData.descendedAffineUnitaryHom_apply
    (p : ProperOrthochronousPoincareTransformation d) :
    letI : Group (ProperOrthochronousPoincareTransformation d) := targetGroup.group
    ScalarWightmanAxiomChainData.descendedAffineUnitaryHom
        (targetGroup := targetGroup) chain p =
      chain.descendedAffineUnitary p :=
  rfl

/-- The descended affine representation is strongly continuous on every physical Hilbert vector.
Continuity descends through the exact quotient-map cover projection. -/
theorem ScalarWightmanAxiomChainData.descendedAffineUnitary_stronglyContinuous
    (targetGroup : ProperOrthochronousPoincareTargetGroupData d)
    (ψ : H) :
    Continuous (fun p : ProperOrthochronousPoincareTransformation d =>
      chain.descendedAffineUnitary p ψ) := by
  apply cover.projection_isQuotientMap.continuous_iff.mpr
  have sourceContinuous := chain.U.strongly_continuous ψ
  convert sourceContinuous using 1
  funext g
  exact congrArg (fun unitary : H ≃ₗᵢ[ℂ] H => unitary ψ)
    (chain.descendedAffineUnitary_projection targetGroup g)

end

end YangMills.Minkowski
