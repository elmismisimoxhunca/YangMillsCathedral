/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import Mathlib.Geometry.Manifold.GroupLieAlgebra
import YangMills.Mathematics.MixedPartialLieBracket

/-!
# Centered-chart regularity of Lie-group multiplication

Multiplication in a `C∞` Lie group is twice continuously differentiable in the extended chart
centered at the identity, within the exact product of the corner-model ranges. This intentionally
does not replace `range I ×ˢ range I` by the whole model space.
-/

namespace YangMills.Mathematics

open Set Bundle ChartedSpace
open scoped Manifold ContDiff

universe uE uH uG

noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {E : Type uE} {H : Type uH}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H)
    {G : Type uG} [Group G] [TopologicalSpace G]
    [ChartedSpace H G] [LieGroup I ∞ G]

/-- Exact `C²`-within regularity of multiplication in the identity-centered extended chart. -/
theorem contDiffWithinAt_extChartAt_mul_identity :
    let c := extChartAt I (1 : G)
    let a := c (1 : G)
    ContDiffWithinAt ℝ 2
      (fun z : E × E => c (c.symm z.1 * c.symm z.2))
      (range I ×ˢ range I) (a, a) := by
  dsimp
  have hmul : ContMDiff (I.prod I) I ∞ (fun p : G × G => p.1 * p.2) :=
    contMDiff_mul I ∞
  have hm := hmul.contMDiffAt (x := ((1, 1) : G × G))
  rw [contMDiffAt_iff] at hm
  have hm2 := hm.2.of_le
    (show (↑(2 : ℕ∞) : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞) from WithTop.coe_le_coe.mpr le_top)
  convert hm2 using 1
  · norm_num
  · funext z
    simp only [Function.comp_apply, one_mul]
    rw [extChartAt_prod, PartialEquiv.prod_symm]
    rfl
  · exact ModelWithCorners.range_prod.symm
  · simp

end

end YangMills.Mathematics
