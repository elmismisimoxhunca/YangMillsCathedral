/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Renormalization.SchwartzScaling

/-!
# Hostile probes for normalized Schwartz scaling

The probes expose the exact inverse-coordinate and Jacobian-power convention, scale-zero
totalization, and nonvanishing at positive scale.
-/

namespace YangMills.Renormalization.SchwartzScaling.Probes

/-- Positive-scale evaluation is exactly `r⁻ᵈ f(x/r)`. -/
theorem exact_normalized_dilation
    (d : EuclideanDimension) {r : ℝ} (hr : 0 < r)
    (test : Minkowski.ScalarMinkowskiSchwartzTestFunction d)
    (x : Minkowski.Spacetime d) :
    normalizedRelativeSchwartzDilationCLM d r test x =
      (((r : ℂ) ^ d.value)⁻¹) • test (r⁻¹ • x) :=
  normalizedRelativeSchwartzDilationCLM_apply d (ne_of_gt hr) test x

/-- The arbitrary totalized value at the excluded scale is visibly zero. -/
theorem exact_zero_scale_totalization (d : EuclideanDimension) :
    normalizedRelativeSchwartzDilationCLM d 0 = 0 :=
  normalizedRelativeSchwartzDilationCLM_zero d

/-- Positive normalized scaling cannot collapse a genuine test to zero. -/
theorem positive_scale_nonzero
    (d : EuclideanDimension) {r : ℝ} (hr : 0 < r)
    {test : Minkowski.ScalarMinkowskiSchwartzTestFunction d} (htest : test ≠ 0) :
    normalizedRelativeSchwartzDilationCLM d r test ≠ 0 :=
  normalizedRelativeSchwartzDilationCLM_ne_zero d hr htest

/-- Replacing inverse-coordinate scaling by direct scaling is exposed pointwise whenever the test
distinguishes those values. -/
theorem direct_scaling_replacement_blocked
    (d : EuclideanDimension) {r : ℝ} (hr : 0 < r)
    (test : Minkowski.ScalarMinkowskiSchwartzTestFunction d)
    (x : Minkowski.Spacetime d)
    (mismatch : test (r⁻¹ • x) ≠ test (r • x)) :
    normalizedRelativeSchwartzDilationCLM d r test x ≠
      (((r : ℂ) ^ d.value)⁻¹) • test (r • x) := by
  rw [normalizedRelativeSchwartzDilationCLM_apply d (ne_of_gt hr)]
  intro equality
  have scaleNonzero : ((r : ℂ) ^ d.value)⁻¹ ≠ 0 := by
    exact inv_ne_zero (pow_ne_zero _ (Complex.ofReal_ne_zero.mpr (ne_of_gt hr)))
  have multiplied : ((r : ℂ) ^ d.value)⁻¹ * test (r⁻¹ • x) =
      ((r : ℂ) ^ d.value)⁻¹ * test (r • x) := by
    simpa [smul_eq_mul] using equality
  exact mismatch (mul_left_cancel₀ scaleNonzero multiplied)

end YangMills.Renormalization.SchwartzScaling.Probes
