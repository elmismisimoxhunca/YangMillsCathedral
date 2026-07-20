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

omit targetGroup in
/-- The selected-lift implementation cannot be changed to an unrelated unitary at one target. -/
theorem unrelated_descended_unitary_blocked
    (p : ProperOrthochronousPoincareTransformation d) (wrong : H ≃ₗᵢ[ℂ] H)
    (claimed : wrong = chain.descendedAffineUnitary p) :
    wrong = chain.U.unitary (selectedAffinePoincareLift (cover := cover) p) := by
  exact claimed

end

end YangMills.Minkowski.ScalarWightmanPoincareDescent.Probes
