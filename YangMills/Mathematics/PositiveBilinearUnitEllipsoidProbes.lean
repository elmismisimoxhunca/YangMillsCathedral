/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Mathematics.PositiveBilinearUnitEllipsoid

/-!
# Probes for positive bilinear unit ellipsoids

These probes pin the strict-positivity premise and the exact von Neumann bounded sublevel set.
-/

namespace YangMills.Mathematics

open Bornology

universe uE

variable
    {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]

example
    (B : E →L[ℝ] E →L[ℝ] ℝ)
    (positive : ∀ v : E, v ≠ 0 → 0 < B v v) :
    IsVonNBounded ℝ {v | B v v < 1} :=
  positiveBilinear_unitEllipsoid_isVonNBounded B positive

/-- Hostile zero-form probe: strict positivity cannot be replaced by a disconnected proof for the
zero bilinear form on a nonzero space. -/
example
    (positive : ∀ v : ℝ, v ≠ 0 → 0 < (0 : ℝ →L[ℝ] ℝ →L[ℝ] ℝ) v v) : False := by
  have := positive 1 one_ne_zero
  norm_num at this

end YangMills.Mathematics
