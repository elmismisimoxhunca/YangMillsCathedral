/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Minkowski.WightmanField

/-!
# Normalized Schwartz dilations at short distance

This reusable infrastructure defines the finite-dimensional normalized dilation
`f ↦ r⁻ᵈ f(·/r)` on Minkowski-coordinate Schwartz tests. The Euclidean norm/topology controls
Schwartz decay; no Lorentz-invariant measure claim is made. At `r = 0` the operator is explicitly
zero, while all source-facing asymptotics use the filter `r → 0+`. Negative inputs are only a total
infrastructure extension: in odd dimension the displayed `r⁻ᵈ` factor is orientation-signed and is
not claimed to be Lebesgue-normalized there.
-/

namespace YangMills.Renormalization

open scoped SchwartzMap

noncomputable section

/-- Continuous linear coordinate dilation `x ↦ x/r` for nonzero real `r`. -/
def inverseScaleContinuousLinearEquiv
    (d : EuclideanDimension) (r : ℝ) (hr : r ≠ 0) :
    Minkowski.Spacetime d ≃L[ℝ] Minkowski.Spacetime d :=
  ContinuousLinearEquiv.smulLeft (Units.mk0 r⁻¹ (inv_ne_zero hr))

/-- Continuous-linear normalized Schwartz dilation, totalized by zero at scale zero. -/
def normalizedRelativeSchwartzDilationCLM
    (d : EuclideanDimension) (r : ℝ) :
    Minkowski.ScalarMinkowskiSchwartzTestFunction d →L[ℂ]
      Minkowski.ScalarMinkowskiSchwartzTestFunction d := by
  by_cases hr : r = 0
  · exact 0
  · exact (((r : ℂ) ^ d.value)⁻¹) •
      SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
        (inverseScaleContinuousLinearEquiv d r hr)

/-- Pointwise value of the normalized dilation at positive/nonzero scale. -/
@[simp]
theorem normalizedRelativeSchwartzDilationCLM_apply
    (d : EuclideanDimension) {r : ℝ} (hr : r ≠ 0)
    (test : Minkowski.ScalarMinkowskiSchwartzTestFunction d)
    (x : Minkowski.Spacetime d) :
    normalizedRelativeSchwartzDilationCLM d r test x =
      (((r : ℂ) ^ d.value)⁻¹) • test (r⁻¹ • x) := by
  simp [normalizedRelativeSchwartzDilationCLM, hr,
    inverseScaleContinuousLinearEquiv]

/-- At scale zero the totalized dilation is exactly zero. -/
@[simp]
theorem normalizedRelativeSchwartzDilationCLM_zero
    (d : EuclideanDimension) :
    normalizedRelativeSchwartzDilationCLM d 0 = 0 := by
  simp [normalizedRelativeSchwartzDilationCLM]

/-- Positive-scale normalized dilation cannot kill a nonzero Schwartz test. -/
theorem normalizedRelativeSchwartzDilationCLM_ne_zero
    (d : EuclideanDimension) {r : ℝ} (hr : 0 < r)
    {test : Minkowski.ScalarMinkowskiSchwartzTestFunction d} (htest : test ≠ 0) :
    normalizedRelativeSchwartzDilationCLM d r test ≠ 0 := by
  intro hzero
  apply htest
  ext x
  let y : Minkowski.Spacetime d := r • x
  have atY := congrArg
    (fun f : Minkowski.ScalarMinkowskiSchwartzTestFunction d => f y) hzero
  rw [normalizedRelativeSchwartzDilationCLM_apply d (ne_of_gt hr)] at atY
  have hrComplex : (r : ℂ) ^ d.value ≠ 0 :=
    pow_ne_zero _ (Complex.ofReal_ne_zero.mpr (ne_of_gt hr))
  have hxy : r⁻¹ • y = x := by
    simp [y, inv_smul_smul₀ (ne_of_gt hr)]
  rw [hxy] at atY
  simpa [hrComplex] using atY

end

end YangMills.Renormalization
