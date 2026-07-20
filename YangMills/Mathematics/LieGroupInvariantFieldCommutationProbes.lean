/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Mathematics.LieGroupInvariantFieldCommutation

namespace YangMills.Mathematics.LieGroupInvariantFieldCommutation.Probes

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

/-- The exact Mathlib manifold bracket vanishes at the identity. -/
theorem exact_invariant_field_commutation (X Y : GroupLieAlgebra I G) :
    VectorField.mlieBracket I (mulInvariantVectorField X)
      (mulRightInvariantVectorField I Y) 1 = 0 :=
  mlieBracket_mulInvariant_mulRightInvariant_identity I X Y

/-- A nonzero identity bracket contradicts the corner-aware chart calculation. -/
theorem nonzero_invariant_field_bracket_blocked
    (X Y : GroupLieAlgebra I G)
    (nonzero : VectorField.mlieBracket I (mulInvariantVectorField X)
      (mulRightInvariantVectorField I Y) 1 ≠ 0) : False :=
  nonzero (mlieBracket_mulInvariant_mulRightInvariant_identity I X Y)

end

end YangMills.Mathematics.LieGroupInvariantFieldCommutation.Probes
