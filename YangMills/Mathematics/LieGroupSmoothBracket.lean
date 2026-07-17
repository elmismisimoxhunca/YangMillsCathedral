/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Mathematics.LieGroupContinuousBracket
import YangMills.Mathematics.SmoothLieBracketWedge

/-!
# Smoothness of the finite-dimensional Lie-group tangent bracket

The transported finite-dimensional tangent bracket is bilinear, hence smooth in the normed model.
This file connects the actual Mathlib `GroupLieAlgebra` bracket to the coordinate-smooth interface
used by smooth bracket-wedges.
-/

namespace YangMills.Mathematics

open scoped Manifold ContDiff

universe uE uH uG

set_option backward.isDefEq.respectTransparency false in
/-- The canonical normed coordinates of a finite-dimensional Lie-group tangent algebra have a
smooth bracket. -/
noncomputable instance instSmoothLieBracketCoordinatesGroupLieAlgebra
    {E : Type uE} {H : Type uH}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H}
    {G : Type uG} [Group G] [TopologicalSpace G] [ChartedSpace H G]
    [LieGroup I (minSmoothness ℝ 3) G] :
    letI : CompleteSpace E := FiniteDimensional.complete ℝ E
    SmoothLieBracketCoordinates (groupLieAlgebraModelEquiv (G := G) I) := by
  let coordinates := groupLieAlgebraModelEquiv (G := G) I
  let bracketContinuousLinear : E →L[ℝ] E →L[ℝ] E :=
    groupLieAlgebraCoordinateBracketCLM (I := I) (G := G)
  have bracket_smooth : ContDiff ℝ ∞ (coordinateLieBracket coordinates) := by
    exact (bracketContinuousLinear.contDiff.comp contDiff_fst).clm_apply contDiff_snd
  constructor
  change ContMDiff ((modelWithCornersSelf ℝ E).prod (modelWithCornersSelf ℝ E))
    (modelWithCornersSelf ℝ E) ∞ (coordinateLieBracket coordinates)
  rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod]
  exact bracket_smooth.contMDiff

end YangMills.Mathematics
