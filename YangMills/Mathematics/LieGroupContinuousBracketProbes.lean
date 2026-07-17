/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Mathematics.LieGroupContinuousBracket

/-!
# Probes for continuity of the Lie-group tangent bracket

These probes ensure that the finite-dimensional tangent Lie algebra reaches the generic continuous
bracket-wedge infrastructure rather than carrying only an unrelated algebraic bracket.
-/

namespace YangMills.Mathematics.Probes

open scoped Manifold ContDiff

universe uE uH uG

variable
    {E : Type uE} {H : Type uH}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H}
    {G : Type uG} [Group G] [TopologicalSpace G] [ChartedSpace H G]
    [LieGroup I (minSmoothness ℝ 3) G]

/-- The project's usual `C∞` finite-dimensional context supplies all local bracket plumbing. -/
theorem cinfinity_groupLieAlgebra_continuousBracket_available
    {E' : Type uE} {H' : Type uH}
    [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
    [TopologicalSpace H']
    {I' : ModelWithCorners ℝ E' H'}
    {G' : Type uG} [Group G'] [TopologicalSpace G'] [ChartedSpace H' G']
    [LieGroup I' ∞ G'] :
    letI : CompleteSpace E' := FiniteDimensional.complete ℝ E'
    letI : ENat.LEInfty (minSmoothness ℝ 3) := by
      rw [minSmoothness_of_isRCLikeNormedField]
      infer_instance
    ContinuousLieBracket (GroupLieAlgebra I' G') := by
  letI : CompleteSpace E' := FiniteDimensional.complete ℝ E'
  letI : ENat.LEInfty (minSmoothness ℝ 3) := by
    rw [minSmoothness_of_isRCLikeNormedField]
    infer_instance
  infer_instance

/-- The actual Mathlib tangent bracket is jointly continuous. -/
theorem groupLieAlgebra_bracket_continuous :
    Continuous fun pair : GroupLieAlgebra I G × GroupLieAlgebra I G => ⁅pair.1, pair.2⁆ :=
  ContinuousLieBracket.continuous_bracket

/-- A proposed discontinuity of that same tangent bracket is contradictory. -/
theorem discontinuous_groupLieAlgebra_bracket_blocked
    (discontinuous : ¬Continuous
      fun pair : GroupLieAlgebra I G × GroupLieAlgebra I G => ⁅pair.1, pair.2⁆) : False :=
  discontinuous groupLieAlgebra_bracket_continuous

/-- Tangent-Lie-algebra-valued one-forms can use the concrete bracket-wedge construction. -/
theorem groupLieAlgebra_lieBracketWedge_available
    (first second : E [⋀^Fin 1]→L[ℝ] GroupLieAlgebra I G) :
    Nonempty (E [⋀^Fin 2]→L[ℝ] GroupLieAlgebra I G) :=
  ⟨first.lieBracketWedgeOne second⟩

/-- The zero tangent-Lie-algebra-valued one-form gives a concrete zero bracket-wedge. -/
theorem zero_groupLieAlgebra_lieBracketWedge :
    (0 : E [⋀^Fin 1]→L[ℝ] GroupLieAlgebra I G).lieBracketWedgeOne 0 = 0 := by
  ext v
  simp

end YangMills.Mathematics.Probes
