/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Mathematics.SumOpensMeasurableSpace

/-!
# Hostile probes for measurable open sets in sums
-/

namespace YangMills.Mathematics.SumOpensMeasurableSpaceProbes

universe uα uβ

variable
    {α : Type uα} {β : Type uβ}
    [TopologicalSpace α] [MeasurableSpace α] [OpensMeasurableSpace α]
    [TopologicalSpace β] [MeasurableSpace β] [OpensMeasurableSpace β]

/-- The sum receives the intended open-measurability instance without any countability premise. -/
@[reducible] def exact_sum_opensMeasurableSpace : OpensMeasurableSpace (α ⊕ β) :=
  inferInstance

/-- Every open subset of the standard measurable sum is measurable. -/
theorem open_sum_set_measurable {set : Set (α ⊕ β)} (isOpenSet : IsOpen set) :
    MeasurableSet set :=
  isOpenSet.measurableSet

end YangMills.Mathematics.SumOpensMeasurableSpaceProbes
