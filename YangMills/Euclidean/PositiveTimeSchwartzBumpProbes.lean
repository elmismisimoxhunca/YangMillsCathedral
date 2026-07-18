/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Euclidean.PositiveTimeSchwartzBump

/-!
# Hostile probes for the positive-time Schwartz bump

These probes ensure that the anti-vacuity witness has nonempty topological support, is not the zero
Schwartz test hidden inside a subtype, and retains the exact strict-positive-time support proof.
They do not assert reflection positivity.
-/

namespace YangMills.Euclidean.PositiveTimeSchwartzBump.Probes

/-- The bump center belongs to the actual topological support. -/
theorem center_mem_positiveTimeBump_tsupport (d : EuclideanDimension) :
    positiveTimeBumpCenter d ∈ tsupport (positiveTimeBumpSchwartz d) := by
  apply subset_tsupport (positiveTimeBumpSchwartz d)
  simp [Function.mem_support, positiveTimeBumpSchwartz_center]

/-- The packaged positive-time subtype value is genuinely nonzero. -/
theorem positiveTimeBumpTest_value_ne_zero (d : EuclideanDimension) :
    (positiveTimeBumpTest d).1 ≠ 0 :=
  positiveTimeBumpSchwartz_ne_zero d

/-- The packaged witness retains the exact strict-positive-time topological-support condition. -/
theorem positiveTimeBumpTest_exact_support (d : EuclideanDimension) :
    HasStrictPositiveTimeSupport d (positiveTimeBumpTest d).1 :=
  (positiveTimeBumpTest d).2

/-- Replacing the explicit bump by zero contradicts its center value. -/
theorem positiveTimeBump_replacement_by_zero_blocked
    (d : EuclideanDimension) (hreplaced : positiveTimeBumpSchwartz d = 0) : False :=
  positiveTimeBumpSchwartz_ne_zero d hreplaced

end YangMills.Euclidean.PositiveTimeSchwartzBump.Probes
