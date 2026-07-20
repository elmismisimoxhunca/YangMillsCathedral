/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Minkowski.ScalarWightmanPoincareDescent

/-!
# Hostile probes for scalar affine-Poincaré descent

The probes force lift-independence, exact projection coherence, multiplicativity under the named
target law, and strong continuity. No representation or theory is constructed.
-/

namespace YangMills.Minkowski.ScalarWightmanPoincareDescent.Probes

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

include targetGroup

/-- Two different lifts of one affine transformation cannot produce different scalar unitaries. -/
theorem exact_lift_independence (first second : G)
    (projection_eq : cover.projection first = cover.projection second) :
    chain.U.unitary first = chain.U.unitary second :=
  chain.unitary_eq_of_projection_eq targetGroup first second projection_eq

/-- Every original cover unitary is recovered at its exact affine projection. -/
theorem exact_projection_coherence (g : G) :
    chain.descendedAffineUnitary (cover.projection g) = chain.U.unitary g :=
  chain.descendedAffineUnitary_projection targetGroup g

/-- The common-domain restriction also recovers the exact original restricted unitary. -/
theorem exact_domain_projection_coherence (g : G) :
    chain.descendedAffineDomainUnitary (cover.projection g) = chain.D.domainUnitary g :=
  chain.descendedAffineDomainUnitary_projection targetGroup g

omit targetGroup in
/-- Scalar field covariance is stated directly on affine kinematics, with no lift choice exposed. -/
theorem exact_descended_field_covariance
    (p : ProperOrthochronousPoincareTransformation d)
    (f : ScalarMinkowskiSchwartzTestFunction d) (ψ : chain.D.domain) :
    chain.descendedAffineDomainUnitary p
        (chain.fieldData.field f ((chain.descendedAffineDomainUnitary p).symm ψ)) =
      chain.fieldData.field (pullbackScalarMinkowskiSchwartzTestFunction d p f) ψ :=
  chain.field_covariant_descendedAffine p f ψ

omit targetGroup in
/-- The same direct affine statement holds for the exact adjoint field. -/
theorem exact_descended_adjoint_covariance
    (p : ProperOrthochronousPoincareTransformation d)
    (f : ScalarMinkowskiSchwartzTestFunction d) (ψ : chain.D.domain) :
    chain.descendedAffineDomainUnitary p
        (chain.fieldData.adjointField f ((chain.descendedAffineDomainUnitary p).symm ψ)) =
      chain.fieldData.adjointField (pullbackScalarMinkowskiSchwartzTestFunction d p f) ψ :=
  chain.adjoint_covariant_descendedAffine p f ψ

omit targetGroup in
/-- Every explicitly designated scalar label in the same local-observable family inherits direct
affine covariance. -/
theorem exact_descended_observable_covariance
    {family : TemperedLocalObservableFamilyData chain.D}
    (covariance : CovariantLocalObservableFamilyData family)
    (A : family.Label) (hA : A ∈ covariance.scalarLabel)
    (p : ProperOrthochronousPoincareTransformation d)
    (f : ScalarMinkowskiSchwartzTestFunction d) (ψ : chain.D.domain) :
    chain.descendedAffineDomainUnitary p
        (family.operator A f ((chain.descendedAffineDomainUnitary p).symm ψ)) =
      family.operator A (pullbackScalarMinkowskiSchwartzTestFunction d p f) ψ :=
  covariance.operator_covariant_descendedAffine chain A hA p f ψ

omit targetGroup in
/-- Propositional lift equality descends covariance on the original, uncast observable family. -/
theorem exact_lift_equality_observable_covariance
    {otherLift : ProperOrthochronousPoincareLiftData d G}
    (otherChain : ScalarWightmanAxiomChainData d otherLift H)
    (lift_eq : cover.toProperOrthochronousPoincareLiftData = otherLift)
    {family : TemperedLocalObservableFamilyData otherChain.D}
    (covariance : CovariantLocalObservableFamilyData family)
    (A : family.Label) (hA : A ∈ covariance.scalarLabel)
    (p : ProperOrthochronousPoincareTransformation d)
    (f : ScalarMinkowskiSchwartzTestFunction d) (ψ : otherChain.D.domain) :
    otherChain.descendedAffineDomainUnitaryOfLiftEq lift_eq p
        (family.operator A f
          ((otherChain.descendedAffineDomainUnitaryOfLiftEq lift_eq p).symm ψ)) =
      family.operator A (pullbackScalarMinkowskiSchwartzTestFunction d p f) ψ :=
  covariance.operator_covariant_descendedAffineOfLiftEq
    otherChain lift_eq A hA p f ψ

/-- The descended map is a genuine homomorphism for the named target law. -/
theorem exact_affine_multiplicativity
    (first second : ProperOrthochronousPoincareTransformation d) :
    letI : Group (ProperOrthochronousPoincareTransformation d) := targetGroup.group
    chain.descendedAffineUnitaryHom (targetGroup := targetGroup) (first * second) =
      chain.descendedAffineUnitaryHom (targetGroup := targetGroup) first *
        chain.descendedAffineUnitaryHom (targetGroup := targetGroup) second := by
  letI : Group (ProperOrthochronousPoincareTransformation d) := targetGroup.group
  exact (chain.descendedAffineUnitaryHom (targetGroup := targetGroup)).map_mul first second

/-- Strong continuity survives quotient descent to exact affine kinematics. -/
theorem exact_affine_strong_continuity (ψ : H) :
    Continuous (fun p : ProperOrthochronousPoincareTransformation d =>
      chain.descendedAffineUnitary p ψ) :=
  chain.descendedAffineUnitary_stronglyContinuous targetGroup ψ

/-- No unrelated affine unitary family can satisfy coherence with every original cover lift. -/
theorem unrelated_descended_unitary_family_blocked
    (candidate : ProperOrthochronousPoincareTransformation d → (H ≃ₗᵢ[ℂ] H))
    (candidate_coherent : ∀ g : G,
      candidate (cover.projection g) = chain.U.unitary g) :
    candidate = chain.descendedAffineUnitary :=
  chain.descendedAffineUnitary_unique targetGroup candidate candidate_coherent

end

end YangMills.Minkowski.ScalarWightmanPoincareDescent.Probes
