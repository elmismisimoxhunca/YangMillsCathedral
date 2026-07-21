/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Mathematics.LieGroupRightInvariantScalarLaplacian

/-!
# Hostile probes for the right-invariant scalar Laplacian

The probes expose the exact manifold derivative, iterated right-invariant derivative, selected
orthonormal basis sum, all-basis coherence, constant annihilation, and rejection of a disconnected
replacement operator.
-/

namespace YangMills.Mathematics.LieGroupRightInvariantScalarLaplacian.Probes

open scoped Manifold ContDiff BigOperators

noncomputable section

variable
    {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [Group G] [TopologicalSpace G] [ChartedSpace E G]
    [LieGroup (modelWithCornersSelf ℝ E) ∞ G]
    {inner : Geometry.InvariantInnerProductData
      (I := modelWithCornersSelf ℝ E) (G := G)}

omit [LieGroup (modelWithCornersSelf ℝ E) ∞ G] in
/-- First differentiation uses the actual manifold derivative and actual right-invariant field. -/
theorem exact_first_right_invariant_derivative
    (f : G → ℝ) (Y : GroupLieAlgebra (modelWithCornersSelf ℝ E) G) (g : G) :
    rightInvariantScalarDerivative f Y g =
      mfderiv (modelWithCornersSelf ℝ E) 𝓘(ℝ, ℝ) f g
        (mulRightInvariantVectorField (modelWithCornersSelf ℝ E) Y g) :=
  rfl

omit [LieGroup (modelWithCornersSelf ℝ E) ∞ G] in
/-- The second derivative is the same first operator iterated in the stated order. -/
theorem exact_second_right_invariant_derivative
    (f : G → ℝ) (X Y : GroupLieAlgebra (modelWithCornersSelf ℝ E) G) (g : G) :
    rightInvariantScalarSecondDerivative f X Y g =
      rightInvariantScalarDerivative
        (fun q => rightInvariantScalarDerivative f Y q) X g :=
  rfl

/-- The selected Laplacian is exactly Driver's sum over the selected orthonormal basis. -/
theorem exact_selected_basis_laplacian
    (data : RightInvariantPairingLaplacianData inner)
    (f : SmoothLieGroupScalarFunction (E := E) (G := G)) (g : G) :
    data.laplacian f g =
      ∑ a, rightInvariantScalarSecondDerivative f
        (data.orthonormalBasis.basis a) (data.orthonormalBasis.basis a) g :=
  rfl

/-- Every other basis orthonormal for the same exact pairing computes the same operator. -/
theorem exact_other_basis_coherence
    (data : RightInvariantPairingLaplacianData inner)
    (other : Geometry.InvariantPairingOrthonormalBasisData inner)
    (f : SmoothLieGroupScalarFunction (E := E) (G := G)) (g : G) :
    data.laplacian f g = rightInvariantScalarLaplacianInBasis other.basis f g :=
  data.laplacian_eq_inBasis other f g

/-- A disconnected replacement value is rejected whenever it differs from the exact basis sum. -/
theorem changed_laplacian_value_blocked
    (data : RightInvariantPairingLaplacianData inner)
    (f : SmoothLieGroupScalarFunction (E := E) (G := G)) (g : G)
    (wrong : ℝ)
    (different : wrong ≠ rightInvariantScalarLaplacianInBasis
      data.orthonormalBasis.basis f g)
    (claimed : data.laplacian f g = wrong) : False := by
  apply different
  rw [← claimed]
  rfl

/-- The exact operator annihilates every constant smooth scalar function. -/
theorem exact_constant_laplacian_zero
    (data : RightInvariantPairingLaplacianData inner) (c : ℝ) (g : G) :
    data.laplacian (SmoothLieGroupScalarFunction.const c) g = 0 :=
  data.laplacian_const c g

end

end YangMills.Mathematics.LieGroupRightInvariantScalarLaplacian.Probes
