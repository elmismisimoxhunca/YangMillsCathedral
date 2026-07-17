/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Mathematics.SmoothManifoldDifferentialFormOperations

/-!
# Probes for linear operations on smooth manifold forms
-/

namespace YangMills.Mathematics.Probes

open scoped Manifold ContDiff

universe uE uH uM uV uW

variable
    {E : Type uE} {H : Type uH}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
    {M : Type uM} [TopologicalSpace M]
    {V : Type uV} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]
    [IsTopologicalAddGroup V] [ContinuousSMul ℝ V]
    {W : Type uW} [NormedAddCommGroup W] [NormedSpace ℝ W]
    {I : ModelWithCorners ℝ E H} [ChartedSpace H M] [IsManifold I ∞ M]
    {coordinates : V ≃L[ℝ] W} {k : ℕ}

/-- Addition preserves both smoothness and the exact pointwise sum. -/
theorem malformed_smoothForm_addition_blocked
    (first second : SmoothManifoldDifferentialForm I M V coordinates k)
    (mismatch : (SmoothManifoldDifferentialForm.add first second).toForm ≠
      first.toForm + second.toForm) : False :=
  mismatch rfl

/-- Scalar multiplication preserves both smoothness and the exact pointwise scalar action. -/
theorem malformed_smoothForm_scalar_blocked
    (scalar : ℝ) (form : SmoothManifoldDifferentialForm I M V coordinates k)
    (mismatch : (SmoothManifoldDifferentialForm.smul scalar form).toForm ≠
      scalar • form.toForm) : False :=
  mismatch rfl

/-- Bundled addition cannot hide a nonsmooth result. -/
theorem nonsmooth_smoothForm_addition_blocked
    (first second : SmoothManifoldDifferentialForm I M V coordinates k)
    (nonsmooth : ¬(SmoothManifoldDifferentialForm.add first second).toForm.IsSmooth coordinates) :
    False :=
  nonsmooth (SmoothManifoldDifferentialForm.add first second).smooth

/-- Bundled scalar multiplication cannot hide a nonsmooth result. -/
theorem nonsmooth_smoothForm_scalar_blocked
    (scalar : ℝ) (form : SmoothManifoldDifferentialForm I M V coordinates k)
    (nonsmooth : ¬(SmoothManifoldDifferentialForm.smul scalar form).toForm.IsSmooth coordinates) :
    False :=
  nonsmooth (SmoothManifoldDifferentialForm.smul scalar form).smooth

end YangMills.Mathematics.Probes
