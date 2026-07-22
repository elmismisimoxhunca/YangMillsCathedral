/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Mathematics.BoundaryConditionedProductDisintegration

/-!
# Hostile probes for boundary-conditioned product disintegrations
-/

namespace YangMills.Mathematics.BoundaryConditionedProductDisintegration.Probes

open MeasureTheory ProbabilityTheory Set

universe uBoundary uLeft uRight uWhole

variable
    {Boundary : Type uBoundary} {Left : Type uLeft} {Right : Type uRight}
    {Whole : Type uWhole}
    [MeasurableSpace Boundary] [MeasurableSpace Left] [MeasurableSpace Right]
    [MeasurableSpace Whole]

/-- The stored kernel is a genuine Mathlib conditional kernel for the joint boundary/whole law. -/
theorem exact_joint_conditional_kernel
    (data : BoundaryConditionedProductDisintegrationData Boundary Left Right Whole) :
    Measure.IsCondKernel
      (Measure.map (fun whole => (data.boundaryValue whole, whole)) data.wholeMeasure)
      data.conditionedWhole :=
  data.conditionedWhole_disintegration

/-- Genuine joint disintegration derives reconstruction by binding the boundary marginal. -/
theorem exact_bind_reconstruction
    (data : BoundaryConditionedProductDisintegrationData Boundary Left Right Whole) :
    Measure.bind data.boundaryMarginal data.conditionedWhole = data.wholeMeasure :=
  data.disintegration

/-- Every selected all-value conditional law assigns zero mass outside its exact boundary fiber,
without relying on measurability of singleton boundary values. -/
theorem exact_boundary_fiber_support
    (data : BoundaryConditionedProductDisintegrationData Boundary Left Right Whole)
    (boundary : Boundary) :
    data.conditionedWhole boundary {whole | data.boundaryValue whole ≠ boundary} = 0 :=
  data.conditionedWhole_outside_boundary_fiber boundary

/-- Exact disintegration derives whole-space normalization. -/
theorem exact_whole_normalization
    (data : BoundaryConditionedProductDisintegrationData Boundary Left Right Whole) :
    data.wholeMeasure univ = 1 :=
  data.wholeMeasure_univ

/-- A zero unconditional law cannot pass the disintegration contract. -/
theorem zero_whole_measure_blocked
    (data : BoundaryConditionedProductDisintegrationData Boundary Left Right Whole)
    (claimed : data.wholeMeasure = 0) : False :=
  data.wholeMeasure_ne_zero claimed

/-- The exact all-value product identity retains the reversed boundary on the right factor. -/
theorem exact_conditioned_product
    (data : BoundaryConditionedProductDisintegrationData Boundary Left Right Whole)
    (boundary : Boundary) :
    Measure.map data.restriction (data.conditionedWhole boundary) =
      (data.conditionedLeft boundary).prod
        (data.conditionedRight (data.boundaryReverse boundary)) :=
  data.conditioned_restriction_product boundary

/-- Product semantics derive the exact left conditional marginal. -/
theorem exact_left_marginal
    (data : BoundaryConditionedProductDisintegrationData Boundary Left Right Whole)
    (boundary : Boundary) :
    Measure.map (fun whole => (data.restriction whole).1) (data.conditionedWhole boundary) =
      data.conditionedLeft boundary :=
  data.conditioned_left_marginal boundary

/-- Product semantics derive the right marginal only at the orientation-reversed boundary value. -/
theorem exact_right_marginal
    (data : BoundaryConditionedProductDisintegrationData Boundary Left Right Whole)
    (boundary : Boundary) :
    Measure.map (fun whole => (data.restriction whole).2) (data.conditionedWhole boundary) =
      data.conditionedRight (data.boundaryReverse boundary) :=
  data.conditioned_right_marginal boundary

/-- Substituting a genuinely different unreversed right conditional law is rejected. -/
theorem unreversed_right_marginal_blocked
    (data : BoundaryConditionedProductDisintegrationData Boundary Left Right Whole)
    (boundary : Boundary)
    (different : data.conditionedRight boundary ≠
      data.conditionedRight (data.boundaryReverse boundary))
    (claimed : Measure.map (fun whole => (data.restriction whole).2)
      (data.conditionedWhole boundary) = data.conditionedRight boundary) : False := by
  apply different
  rw [← claimed]
  exact data.conditioned_right_marginal boundary

/-- Every conditional whole-space measure is nonzero because the kernel is genuinely Markov. -/
theorem zero_conditioned_measure_blocked
    (data : BoundaryConditionedProductDisintegrationData Boundary Left Right Whole)
    (boundary : Boundary) (claimed : data.conditionedWhole boundary = 0) : False := by
  letI : IsMarkovKernel data.conditionedWhole := data.conditionedWhole_markov
  have normalized : data.conditionedWhole boundary univ = 1 := by simp
  rw [claimed] at normalized
  simp at normalized

/-- The boundary parameter law must be the exact pushforward of the same whole-space law. -/
theorem unrelated_boundary_marginal_blocked
    (data : BoundaryConditionedProductDisintegrationData Boundary Left Right Whole)
    (wrong : Measure Boundary)
    (different : wrong ≠ Measure.map data.boundaryValue data.wholeMeasure)
    (claimed : data.boundaryMarginal = wrong) : False := by
  apply different
  rw [← claimed]
  exact data.boundaryMarginal_eq_map

/-- Reversing boundary orientation twice returns the exact original value. -/
theorem exact_boundary_double_reversal
    (data : BoundaryConditionedProductDisintegrationData Boundary Left Right Whole)
    (boundary : Boundary) :
    data.boundaryReverse (data.boundaryReverse boundary) = boundary :=
  data.boundaryReverse_involutive boundary

end YangMills.Mathematics.BoundaryConditionedProductDisintegration.Probes
