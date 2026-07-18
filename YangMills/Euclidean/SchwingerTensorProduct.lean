/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Euclidean.SchwingerConfigurationConcatenation
import YangMills.Mathematics.SchwartzTensorProduct

/-!
# Bundled tensor products on concatenated Euclidean configurations

This module pulls the generic scalar Schwartz tensor product back through the exact continuous
configuration split. The result is an actual `(n+m)`-point Schwartz test whose value is the raw
kernel previously defined for the Osterwalder–Schrader sequence product.

Generic tensor products do not preserve the project's global strict time ordering: cross-block time
inequalities and coincidence flatness require additional hypotheses. Accordingly this module makes
no ordered-subspace closure or reflection-positivity claim.
-/

namespace YangMills

/-- The bundled scalar Schwartz tensor product on the exact concatenated Euclidean configuration. -/
noncomputable def scalarSchwartzTensorProductOnConfiguration
    (d : EuclideanDimension) {n m : ℕ} (f : ScalarSchwartzTestFunction d n)
    (g : ScalarSchwartzTestFunction d m) : ScalarSchwartzTestFunction d (n + m) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (euclideanConfigurationSplit d n m)
    (Mathematics.scalarSchwartzTensorProduct f g)

/-- The bundled concatenated tensor evaluates as the exact previously defined raw kernel. -/
@[simp] theorem scalarSchwartzTensorProductOnConfiguration_apply
    (d : EuclideanDimension) {n m : ℕ} (f : ScalarSchwartzTestFunction d n)
    (g : ScalarSchwartzTestFunction d m) (x : EuclideanNPointSpace d (n + m)) :
    scalarSchwartzTensorProductOnConfiguration d f g x =
      scalarSchwartzRawTensorKernel d f g x := by
  rfl

/-- Evaluation at an exactly merged pair is the product of the original evaluations. -/
@[simp] theorem scalarSchwartzTensorProductOnConfiguration_merge
    (d : EuclideanDimension) {n m : ℕ} (f : ScalarSchwartzTestFunction d n)
    (g : ScalarSchwartzTestFunction d m) (x : EuclideanNPointSpace d n)
    (y : EuclideanNPointSpace d m) :
    scalarSchwartzTensorProductOnConfiguration d f g
        (euclideanConfigurationMerge d n m (x, y)) = f x * g y := by
  rw [scalarSchwartzTensorProductOnConfiguration_apply]
  exact scalarSchwartzRawTensorKernel_merge d f g x y

/-- The concatenated tensor is additive in its first factor. -/
theorem scalarSchwartzTensorProductOnConfiguration_add_left
    (d : EuclideanDimension) {n m : ℕ} (f₁ f₂ : ScalarSchwartzTestFunction d n)
    (g : ScalarSchwartzTestFunction d m) :
    scalarSchwartzTensorProductOnConfiguration d (f₁ + f₂) g =
      scalarSchwartzTensorProductOnConfiguration d f₁ g +
        scalarSchwartzTensorProductOnConfiguration d f₂ g := by
  ext x
  simp [scalarSchwartzRawTensorKernel, add_mul]

/-- The concatenated tensor is additive in its second factor. -/
theorem scalarSchwartzTensorProductOnConfiguration_add_right
    (d : EuclideanDimension) {n m : ℕ} (f : ScalarSchwartzTestFunction d n)
    (g₁ g₂ : ScalarSchwartzTestFunction d m) :
    scalarSchwartzTensorProductOnConfiguration d f (g₁ + g₂) =
      scalarSchwartzTensorProductOnConfiguration d f g₁ +
        scalarSchwartzTensorProductOnConfiguration d f g₂ := by
  ext x
  simp [scalarSchwartzRawTensorKernel, mul_add]

/-- The concatenated tensor respects scalar multiplication in its first factor. -/
theorem scalarSchwartzTensorProductOnConfiguration_smul_left
    (d : EuclideanDimension) {n m : ℕ} (c : ℂ)
    (f : ScalarSchwartzTestFunction d n) (g : ScalarSchwartzTestFunction d m) :
    scalarSchwartzTensorProductOnConfiguration d (c • f) g =
      c • scalarSchwartzTensorProductOnConfiguration d f g := by
  ext x
  simp [scalarSchwartzRawTensorKernel, smul_eq_mul, mul_assoc]

/-- The concatenated tensor respects scalar multiplication in its second factor. -/
theorem scalarSchwartzTensorProductOnConfiguration_smul_right
    (d : EuclideanDimension) {n m : ℕ} (c : ℂ)
    (f : ScalarSchwartzTestFunction d n) (g : ScalarSchwartzTestFunction d m) :
    scalarSchwartzTensorProductOnConfiguration d f (c • g) =
      c • scalarSchwartzTensorProductOnConfiguration d f g := by
  ext x
  simp [scalarSchwartzRawTensorKernel, smul_eq_mul, mul_left_comm]

end YangMills
