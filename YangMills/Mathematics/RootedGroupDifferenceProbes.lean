/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Mathematics.RootedGroupDifference

/-!
# Hostile probes for rooted noncommutative difference coordinates
-/

namespace YangMills.Mathematics.RootedGroupDifference.Probes

universe uG

variable {G : Type uG} [Group G]

/-- The two-slot upper transform retains the exact noncommutative order. -/
theorem exact_upper_two_slots (first second : G) :
    upperForward ![first, second] 0 = first⁻¹ ∧
      upperForward ![first, second] 1 = second⁻¹ * first := by
  constructor
  · simp
  · simpa using upperForward_succ (![first, second] : Fin 2 → G) (0 : Fin 1)

/-- The two-slot lower transform retains the opposite rooted orientation. -/
theorem exact_lower_two_slots (first second : G) :
    lowerForward ![first, second] 0 = first ∧
      lowerForward ![first, second] 1 = first⁻¹ * second := by
  constructor
  · simp
  · simpa using lowerForward_succ (![first, second] : Fin 2 → G) (0 : Fin 1)

/-- Both recursive constructions are genuine equivalences at every finite length. -/
theorem exact_inverse_laws {n : ℕ} (values differences : Fin n → G) :
    upperRecover (upperForward values) = values ∧
      upperForward (upperRecover differences) = differences ∧
      lowerRecover (lowerForward values) = values ∧
      lowerForward (lowerRecover differences) = differences :=
  ⟨upperRecover_upperForward values, upperForward_upperRecover differences,
    lowerRecover_lowerForward values, lowerForward_lowerRecover differences⟩

/-- A reversed multiplication order cannot replace the upper difference unless an actual equality
is supplied. -/
theorem reversed_upper_order_blocked (first second : G)
    (different : second⁻¹ * first ≠ first * second⁻¹)
    (claimed : upperForward ![first, second] 1 = first * second⁻¹) : False := by
  rw [(exact_upper_two_slots first second).2] at claimed
  exact different claimed

section Measurable

variable [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]

/-- Forward and inverse maps on both rooted orientations are measurable. -/
theorem exact_measurable_equivalences (n : ℕ) :
    Measurable (upperMeasurableEquiv (G := G) n) ∧
      Measurable (upperMeasurableEquiv (G := G) n).symm ∧
      Measurable (lowerMeasurableEquiv (G := G) n) ∧
      Measurable (lowerMeasurableEquiv (G := G) n).symm :=
  ⟨(upperMeasurableEquiv (G := G) n).measurable,
    (upperMeasurableEquiv (G := G) n).measurable_invFun,
    (lowerMeasurableEquiv (G := G) n).measurable,
    (lowerMeasurableEquiv (G := G) n).measurable_invFun⟩

end Measurable

end YangMills.Mathematics.RootedGroupDifference.Probes
