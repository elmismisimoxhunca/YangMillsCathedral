/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Euclidean.SchwingerTensorProduct

/-!
# Hostile probes for bundled concatenated Schwartz tensors

The probes connect the bundled Schwartz result to the exact raw kernel, independently exercise both
factors, and retain algebraic bilinearity. They make no ordered-subspace closure claim.
-/

namespace YangMills.Euclidean.SchwingerTensorProduct.Probes

/-- Bundled evaluation is exactly the raw two-factor kernel. -/
theorem bundled_tensor_exact_raw_kernel
    (d : EuclideanDimension) {n m : ℕ} (f : ScalarSchwartzTestFunction d n)
    (g : ScalarSchwartzTestFunction d m) (x : EuclideanNPointSpace d (n + m)) :
    scalarSchwartzTensorProductOnConfiguration d f g x =
      scalarSchwartzRawTensorKernel d f g x :=
  scalarSchwartzTensorProductOnConfiguration_apply d f g x

/-- Zeroing the first factor zeroes the bundled tensor. -/
@[simp] theorem bundled_tensor_zero_left
    (d : EuclideanDimension) {n m : ℕ} (g : ScalarSchwartzTestFunction d m) :
    scalarSchwartzTensorProductOnConfiguration d
      (0 : ScalarSchwartzTestFunction d n) g = 0 := by
  ext x
  simp [scalarSchwartzRawTensorKernel]

/-- Zeroing the second factor zeroes the bundled tensor. -/
@[simp] theorem bundled_tensor_zero_right
    (d : EuclideanDimension) {n m : ℕ} (f : ScalarSchwartzTestFunction d n) :
    scalarSchwartzTensorProductOnConfiguration d f
      (0 : ScalarSchwartzTestFunction d m) = 0 := by
  ext x
  simp [scalarSchwartzRawTensorKernel]

/-- The tensor of two explicit nonzero bumps remains nonzero after exact configuration pullback. -/
theorem bundled_positiveTimeBump_tensor_ne_zero
    (d : EuclideanDimension) :
    scalarSchwartzTensorProductOnConfiguration d
      (positiveTimeBumpSchwartz d) (positiveTimeBumpSchwartz d) ≠ 0 := by
  intro hzero
  have atCenters := congrArg (fun h : ScalarSchwartzTestFunction d (1 + 1) =>
    h (euclideanConfigurationMerge d 1 1
      (positiveTimeBumpCenter d, positiveTimeBumpCenter d))) hzero
  rw [scalarSchwartzTensorProductOnConfiguration_merge] at atCenters
  rw [positiveTimeBumpSchwartz_center] at atCenters
  simp at atCenters

/-- Exact left additivity is retained after pullback. -/
theorem bundled_tensor_exact_add_left
    (d : EuclideanDimension) {n m : ℕ} (f₁ f₂ : ScalarSchwartzTestFunction d n)
    (g : ScalarSchwartzTestFunction d m) :
    scalarSchwartzTensorProductOnConfiguration d (f₁ + f₂) g =
      scalarSchwartzTensorProductOnConfiguration d f₁ g +
        scalarSchwartzTensorProductOnConfiguration d f₂ g :=
  scalarSchwartzTensorProductOnConfiguration_add_left d f₁ f₂ g

/-- Exact right scalar compatibility is retained after pullback. -/
theorem bundled_tensor_exact_smul_right
    (d : EuclideanDimension) {n m : ℕ} (c : ℂ)
    (f : ScalarSchwartzTestFunction d n) (g : ScalarSchwartzTestFunction d m) :
    scalarSchwartzTensorProductOnConfiguration d f (c • g) =
      c • scalarSchwartzTensorProductOnConfiguration d f g :=
  scalarSchwartzTensorProductOnConfiguration_smul_right d c f g

end YangMills.Euclidean.SchwingerTensorProduct.Probes
