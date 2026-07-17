/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Mathematics.LieGroupAdjoint

/-!
# Hostile probes for the Lie-group adjoint action

These probes enforce identity, multiplication order, and inverse behavior before the adjoint action
is used in principal-connection equivariance.
-/

namespace YangMills.Mathematics.Probes

open scoped Manifold ContDiff

universe uE uH uG

variable
    {E : Type uE} {H : Type uH}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H}
    {G : Type uG} [Group G] [TopologicalSpace G] [ChartedSpace H G]

/-- The identity adjoint map cannot be replaced by a nonidentity map. -/
theorem nonidentity_adjoint_one_blocked [LieGroup I ∞ G]
    (mismatch : lieGroupAdjoint I (1 : G) ≠
      ContinuousLinearMap.id ℝ (GroupLieAlgebra I G)) : False :=
  mismatch (lieGroupAdjoint_one I)

/-- Multiplication order in the adjoint representation is fixed. -/
theorem wrong_adjoint_multiplication_blocked [LieGroup I ∞ G]
    (g h : G)
    (mismatch : lieGroupAdjoint I (g * h) ≠
      (lieGroupAdjoint I g).comp (lieGroupAdjoint I h)) : False :=
  mismatch (lieGroupAdjoint_mul I g h)

/-- The inverse group element must undo the adjoint action. -/
theorem broken_adjoint_inverse_blocked [LieGroup I ∞ G]
    (g : G) (X : GroupLieAlgebra I G)
    (mismatch : lieGroupAdjoint I g⁻¹ (lieGroupAdjoint I g X) ≠ X) : False :=
  mismatch (lieGroupAdjoint_inv_apply I g X)

/-- The opposite composition order is also checked through the right-inverse law. -/
theorem broken_adjoint_rightInverse_blocked [LieGroup I ∞ G]
    (g : G) (X : GroupLieAlgebra I G)
    (mismatch : lieGroupAdjoint I g (lieGroupAdjoint I g⁻¹ X) ≠ X) : False :=
  mismatch (lieGroupAdjoint_apply_inv I g X)

end YangMills.Mathematics.Probes
