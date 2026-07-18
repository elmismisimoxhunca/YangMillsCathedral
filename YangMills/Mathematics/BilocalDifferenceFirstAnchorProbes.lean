/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Mathematics.BilocalDifferenceFirstAnchor

/-!
# Hostile probes for bilocal first-anchor coordinates

The probes lock `(x,y) ↦ (x-y,x)`, rejecting the final-anchor or reversed-difference conventions.
-/

namespace YangMills.Mathematics.BilocalDifferenceFirstAnchor.Probes

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- Forward coordinates are exactly source-order difference and first anchor. -/
theorem exact_forward_coordinates (x y : E) :
    bilocalDifferenceFirstAnchorContinuousLinearEquiv E ![x, y] = (x - y, x) :=
  rfl

/-- Reconstruction is exactly `(difference,anchor) ↦ (anchor,anchor-difference)`. -/
theorem exact_reverse_coordinates (difference anchor : E) :
    (bilocalDifferenceFirstAnchorContinuousLinearEquiv E).symm (difference, anchor) =
      ![anchor, anchor - difference] :=
  rfl

/-- A concrete pair distinguishes the first anchor from the final anchor. -/
theorem final_anchor_convention_blocked :
    bilocalDifferenceFirstAnchorContinuousLinearEquiv ℝ ![(1 : ℝ), 0] = (1, 1) := by
  norm_num [bilocalDifferenceFirstAnchorContinuousLinearEquiv,
    bilocalDifferenceFirstAnchorLinearEquiv]

/-- The lifted Schwartz test evaluates with `x-y` and `x`, in that order. -/
theorem exact_lift_evaluation
    (relative anchor : SchwartzMap E ℂ) (x y : E) :
    bilocalDifferenceFirstAnchorSchwartzLift E relative anchor ![x, y] =
      relative (x - y) * anchor x :=
  rfl

end YangMills.Mathematics.BilocalDifferenceFirstAnchor.Probes
