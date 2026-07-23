/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Mathematics.LieGroupRightInvariantComplexLaplacian

/-!
# Hostile probes for the right-invariant complex Laplacian
-/

namespace YangMills
namespace Mathematics
namespace LieGroupRightInvariantComplexLaplacian
namespace Probes

open scoped Manifold ContDiff

noncomputable section

universe uE uG

variable
    {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {G : Type uG} [Group G] [TopologicalSpace G] [ChartedSpace E G]
    [LieGroup (modelWithCornersSelf ℝ E) ∞ G]

omit [LieGroup (modelWithCornersSelf ℝ E) ∞ G] in
/-- The complex derivative retains the exact right-invariant vector field. -/
theorem exact_first_derivative
    (f : G → ℂ) (Y : GroupLieAlgebra (modelWithCornersSelf ℝ E) G) (g : G) :
    rightInvariantComplexDerivative f Y g =
      mfderiv (modelWithCornersSelf ℝ E) (modelWithCornersSelf ℝ ℂ) f g
        (mulRightInvariantVectorField (modelWithCornersSelf ℝ E) Y g) :=
  rfl

omit [LieGroup (modelWithCornersSelf ℝ E) ∞ G] in
/-- The second derivative is the same right-invariant operator iterated with `X` after `Y`. -/
theorem exact_second_derivative
    (f : G → ℂ)
    (X Y : GroupLieAlgebra (modelWithCornersSelf ℝ E) G) (g : G) :
    rightInvariantComplexSecondDerivative f X Y g =
      rightInvariantComplexDerivative
        (fun q => rightInvariantComplexDerivative f Y q) X g :=
  rfl

/-- The selected complex Laplacian is exactly the repeated-direction sum over its selected
same-pairing orthonormal basis. -/
theorem exact_selected_basis_sum
    {inner : Geometry.InvariantInnerProductData
      (I := modelWithCornersSelf ℝ E) (G := G)}
    (data : RightInvariantPairingComplexLaplacianData inner)
    (f : SmoothLieGroupComplexFunction (E := E) (G := G)) (g : G) :
    data.laplacian f g =
      ∑ a, rightInvariantComplexSecondDerivative f
        (data.orthonormalBasis.basis a) (data.orthonormalBasis.basis a) g :=
  rfl

/-- A disconnected replacement value is rejected whenever it differs from the exact selected-basis
sum. -/
theorem changed_selected_laplacian_value_blocked
    {inner : Geometry.InvariantInnerProductData
      (I := modelWithCornersSelf ℝ E) (G := G)}
    (data : RightInvariantPairingComplexLaplacianData inner)
    (f : SmoothLieGroupComplexFunction (E := E) (G := G)) (g : G)
    (wrong : ℂ)
    (different : wrong ≠ rightInvariantComplexLaplacianInBasis
      data.orthonormalBasis.basis f g)
    (claimed : data.laplacian f g = wrong) : False := by
  apply different
  rw [← claimed]
  rfl

omit [LieGroup (modelWithCornersSelf ℝ E) ∞ G] in
/-- Every complex constant is annihilated by the concrete basis Laplacian. -/
theorem exact_constant_zero
    {rank : ℕ}
    (basis : Module.Basis (Fin rank) ℝ
      (GroupLieAlgebra (modelWithCornersSelf ℝ E) G))
    (c : ℂ) (g : G) :
    rightInvariantComplexLaplacianInBasis basis (fun _ : G => c) g = 0 :=
  rightInvariantComplexLaplacianInBasis_const basis c g

/-- The selected pairing-normalized complex Laplacian annihilates constants. -/
theorem exact_pairing_laplacian_constant_zero
    {inner : Geometry.InvariantInnerProductData
      (I := modelWithCornersSelf ℝ E) (G := G)}
    (data : RightInvariantPairingComplexLaplacianData inner)
    (c : ℂ) (g : G) :
    data.laplacian (SmoothLieGroupComplexFunction.const c) g = 0 :=
  data.laplacian_const c g

/-- Every other basis must be orthonormal for the same pairing and compute the same value. -/
theorem exact_same_pairing_basis_value
    {inner : Geometry.InvariantInnerProductData
      (I := modelWithCornersSelf ℝ E) (G := G)}
    (data : RightInvariantPairingComplexLaplacianData inner)
    (other : Geometry.InvariantPairingOrthonormalBasisData inner)
    (f : SmoothLieGroupComplexFunction (E := E) (G := G)) (g : G) :
    data.laplacian f g = rightInvariantComplexLaplacianInBasis other.basis f g :=
  data.laplacian_eq_inBasis other f g

/-- Hostile basis probe: a changed value from another basis orthonormal for the same pairing is
contradictory. -/
theorem changed_same_pairing_basis_value_blocked
    {inner : Geometry.InvariantInnerProductData
      (I := modelWithCornersSelf ℝ E) (G := G)}
    (data : RightInvariantPairingComplexLaplacianData inner)
    (other : Geometry.InvariantPairingOrthonormalBasisData inner)
    (f : SmoothLieGroupComplexFunction (E := E) (G := G)) (g : G)
    (changed : rightInvariantComplexLaplacianInBasis other.basis f g ≠
      data.laplacian f g) : False :=
  changed (data.laplacian_eq_inBasis other f g).symm

end

end Probes
end LieGroupRightInvariantComplexLaplacian
end Mathematics
end YangMills
