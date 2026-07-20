/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Mathematics.LieGroupInvariantFieldChartTarget

namespace YangMills.Mathematics.LieGroupInvariantFieldChartTarget.Probes

open Set ChartedSpace
open scoped Manifold ContDiff

universe uE uH uG
noncomputable section

variable {E : Type uE} {H : Type uH}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H)
    {G : Type uG} [Group G] [TopologicalSpace G]
    [ChartedSpace H G] [LieGroup I ∞ G]

/-- Left-invariant coordinates equal the second partial throughout the exact chart target. -/
theorem exact_left_target_identity
    (X : GroupLieAlgebra I G) (z : E) (hz : z ∈ (extChartAt I (1 : G)).target) :
    let c := extChartAt I (1 : G)
    let a := c (1 : G)
    let F := fun p : E × E => c (c.symm p.1 * c.symm p.2)
    extChartCoordinateField I (1 : G) (mulInvariantVectorField X) z =
      fderivWithin ℝ F (c.target ×ˢ c.target) (z, a)
        (0, mfderiv I 𝓘(ℝ, E) c 1 X) :=
  extChartCoordinateField_mulInvariantVectorField_eq_secondPartial_target I X z hz

/-- Right-invariant coordinates equal the first partial throughout the exact chart target. -/
theorem exact_right_target_identity
    (Y : GroupLieAlgebra I G) (z : E) (hz : z ∈ (extChartAt I (1 : G)).target) :
    let c := extChartAt I (1 : G)
    let a := c (1 : G)
    let F := fun p : E × E => c (c.symm p.1 * c.symm p.2)
    extChartCoordinateField I (1 : G) (mulRightInvariantVectorField I Y) z =
      fderivWithin ℝ F (c.target ×ˢ c.target) (a, z)
        (mfderiv I 𝓘(ℝ, E) c 1 Y, 0) :=
  extChartCoordinateField_mulRightInvariantVectorField_eq_firstPartial_on_target I Y z hz

/-- Changing the target-wide right identity contradicts the exact chain-rule theorem. -/
theorem changed_right_target_identity_blocked
    (Y : GroupLieAlgebra I G) (z : E) (hz : z ∈ (extChartAt I (1 : G)).target)
    (changed : (let c := extChartAt I (1 : G)
      let a := c (1 : G)
      let F := fun p : E × E => c (c.symm p.1 * c.symm p.2)
      extChartCoordinateField I (1 : G) (mulRightInvariantVectorField I Y) z ≠
        fderivWithin ℝ F (c.target ×ˢ c.target) (a, z)
          (mfderiv I 𝓘(ℝ, E) c 1 Y, 0))) : False :=
  changed (extChartCoordinateField_mulRightInvariantVectorField_eq_firstPartial_on_target I Y z hz)

end

end YangMills.Mathematics.LieGroupInvariantFieldChartTarget.Probes
