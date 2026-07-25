/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Euclidean.SchwingerTimeReflection
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-!
# A nonzero strict-positive-time Schwartz test

Reflection positivity must not quantify only over a subtype inhabited by the zero test. This module
constructs, in every supported Euclidean dimension, an explicit nonzero complex Schwartz test at
arity one whose topological support lies at strictly positive selected Euclidean time.

The construction is a smooth compactly supported bump centered at time one, with outer radius one
half. Metric coordinate bounds therefore keep its closed support at time at least one half. This is
anti-vacuity infrastructure only: OS-I's time-ordered/diagonal-flat source-space bridge, finite test
sequences, their product, and `(E2)` remain absent.
-/

namespace YangMills

/-- The arity-one configuration centered one unit along selected positive Euclidean time. -/
noncomputable def positiveTimeBumpCenter (d : EuclideanDimension) :
    EuclideanNPointSpace d 1 :=
  fun _ => EuclideanSpace.single (euclideanTimeCoordinate d) 1

/-- A smooth bump with inner radius `1/4` and outer radius `1/2`, centered at positive time one. -/
noncomputable def positiveTimeBump (d : EuclideanDimension) :
    ContDiffBump (positiveTimeBumpCenter d) where
  rIn := 1 / 4
  rOut := 1 / 2
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

/-- The complex-valued Schwartz test induced by the compactly supported real bump. -/
noncomputable def positiveTimeBumpSchwartz (d : EuclideanDimension) :
    ScalarSchwartzTestFunction d 1 := by
  let bump := positiveTimeBump d
  let complexBump : EuclideanNPointSpace d 1 → ℂ := Complex.ofRealCLM ∘ bump
  have compact : HasCompactSupport complexBump := bump.hasCompactSupport.comp_left rfl
  have smooth : ContDiff ℝ (⊤ : ℕ∞) complexBump :=
    Complex.ofRealCLM.contDiff.comp bump.contDiff
  exact compact.toSchwartzMap smooth

/-- The constructed Schwartz bump takes value one at its center. -/
theorem positiveTimeBumpSchwartz_center (d : EuclideanDimension) :
    positiveTimeBumpSchwartz d (positiveTimeBumpCenter d) = 1 := by
  unfold positiveTimeBumpSchwartz
  change Complex.ofRealCLM ((positiveTimeBump d) (positiveTimeBumpCenter d)) = 1
  rw [(positiveTimeBump d).one_of_mem_closedBall]
  · norm_num
  · exact Metric.mem_closedBall_self (le_of_lt (positiveTimeBump d).rIn_pos)

/-- The constructed strict-positive-time Schwartz test is nonzero. -/
theorem positiveTimeBumpSchwartz_ne_zero (d : EuclideanDimension) :
    positiveTimeBumpSchwartz d ≠ 0 := by
  intro hzero
  have atCenter := congrArg (fun f : ScalarSchwartzTestFunction d 1 =>
    f (positiveTimeBumpCenter d)) hzero
  rw [positiveTimeBumpSchwartz_center] at atCenter
  simp at atCenter

/-- The topological support of the constructed bump lies at strictly positive selected Euclidean
time. -/
theorem positiveTimeBumpSchwartz_hasStrictPositiveTimeSupport
    (d : EuclideanDimension) :
    HasStrictPositiveTimeSupport d (positiveTimeBumpSchwartz d) := by
  intro x hx i
  have hsubset := tsupport_comp_subset (show Complex.ofRealCLM 0 = 0 by simp)
    (positiveTimeBump d)
  have hxbump : x ∈ tsupport (positiveTimeBump d) := by
    apply hsubset
    exact hx
  rw [(positiveTimeBump d).tsupport_eq, Metric.mem_closedBall] at hxbump
  have hpoint :
      dist (x i) (positiveTimeBumpCenter d i) ≤ (1 / 2 : ℝ) :=
    (dist_le_pi_dist x (positiveTimeBumpCenter d) i).trans hxbump
  have htime :
      dist (x i (euclideanTimeCoordinate d))
        (positiveTimeBumpCenter d i (euclideanTimeCoordinate d)) ≤ (1 / 2 : ℝ) :=
    (PiLp.dist_apply_le (x i) (positiveTimeBumpCenter d i)
      (euclideanTimeCoordinate d)).trans hpoint
  simp [positiveTimeBumpCenter] at htime
  rw [Real.dist_eq] at htime
  have hlower := (abs_le.mp htime).1
  linarith

/-- The explicit nonzero positive-time test packaged in the support subtype. -/
noncomputable def positiveTimeBumpTest (d : EuclideanDimension) :
    ScalarPositiveTimeSchwartzTestFunction d 1 :=
  ⟨positiveTimeBumpSchwartz d, positiveTimeBumpSchwartz_hasStrictPositiveTimeSupport d⟩

end YangMills
