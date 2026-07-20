/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Mathematics.LieGroupInfinitesimalAdjoint

namespace YangMills.Mathematics.LieGroupInfinitesimalAdjoint.Probes

open scoped Manifold ContDiff

universe uE uH uG
noncomputable section

variable {E : Type uE} {H : Type uH}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H)
    {G : Type uG} [Group G] [TopologicalSpace G]
    [ChartedSpace H G] [LieGroup I ∞ G]
    [ENat.LEInfty (minSmoothness ℝ 3)]

/-- The inverse-adjoint derivative has the exact negative bracket sign. -/
theorem exact_inverse_adjoint_derivative (X Y : GroupLieAlgebra I G) :
    (NormedSpace.fromTangentSpace
      (groupLieAlgebraModelEquiv I (inverseAdjointOrbit I Y 1))
      (mfderiv I (modelWithCornersSelf ℝ E)
        (fun g => groupLieAlgebraModelEquiv I (inverseAdjointOrbit I Y g)) 1 X)) =
      -groupLieAlgebraModelEquiv I ⁅X, Y⁆ :=
  mfderiv_inverseAdjointOrbit_identity I X Y

/-- For a nonzero bracket, the opposite positive sign is rejected. -/
theorem positive_inverse_adjoint_sign_blocked
    (X Y : GroupLieAlgebra I G)
    (nonzero : groupLieAlgebraModelEquiv I ⁅X, Y⁆ ≠ 0)
    (positive : (NormedSpace.fromTangentSpace
      (groupLieAlgebraModelEquiv I (inverseAdjointOrbit I Y 1))
      (mfderiv I (modelWithCornersSelf ℝ E)
        (fun g => groupLieAlgebraModelEquiv I (inverseAdjointOrbit I Y g)) 1 X)) =
      groupLieAlgebraModelEquiv I ⁅X, Y⁆) : False := by
  apply nonzero
  have hneg : -groupLieAlgebraModelEquiv I ⁅X, Y⁆ =
      groupLieAlgebraModelEquiv I ⁅X, Y⁆ :=
    (mfderiv_inverseAdjointOrbit_identity I X Y).symm.trans positive
  have htwo : (2 : ℝ) • groupLieAlgebraModelEquiv I ⁅X, Y⁆ = 0 := by
    rw [two_smul]
    exact neg_eq_iff_add_eq_zero.mp hneg
  exact (smul_eq_zero.mp htwo).resolve_left (by norm_num)

end

end YangMills.Mathematics.LieGroupInfinitesimalAdjoint.Probes
