/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Mathematics.LieGroupChartMultiplication

namespace YangMills.Mathematics.LieGroupChartMultiplication.Probes

open Set ChartedSpace
open scoped Manifold ContDiff

universe uE uH uG

noncomputable section

variable {E : Type uE} {H : Type uH}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H)
    {G : Type uG} [Group G] [TopologicalSpace G]
    [ChartedSpace H G] [LieGroup I ∞ G]

/-- The exact corner-aware product range is retained. -/
theorem exact_chart_multiplication_regularity :
    let c := extChartAt I (1 : G)
    let a := c (1 : G)
    ContDiffWithinAt ℝ 2
      (fun z : E × E => c (c.symm z.1 * c.symm z.2))
      (range I ×ˢ range I) (a, a) :=
  contDiffWithinAt_extChartAt_mul_identity I

/-- Negating the exact within-range regularity is impossible. -/
theorem missing_chart_multiplication_regularity_blocked
    (missing : ¬ (let c := extChartAt I (1 : G)
      let a := c (1 : G)
      ContDiffWithinAt ℝ 2
        (fun z : E × E => c (c.symm z.1 * c.symm z.2))
        (range I ×ˢ range I) (a, a))) : False :=
  missing (contDiffWithinAt_extChartAt_mul_identity I)

end

end YangMills.Mathematics.LieGroupChartMultiplication.Probes
