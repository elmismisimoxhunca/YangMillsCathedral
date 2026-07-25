/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import Mathlib.Analysis.Normed.Module.Alternating.Basic
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

/-!
# Pointwise differential forms on manifolds

This module supplies the reusable typed carrier needed before principal connection and curvature
forms can be stated. Smoothness of a form as a section and the exterior derivative remain separate
infrastructure tasks.
-/

namespace YangMills.Mathematics

open scoped Manifold ContDiff

universe uE uH uM uE' uH' uM' uV

variable
    {E : Type uE} {H : Type uH}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
    {M : Type uM} [TopologicalSpace M]
    {E' : Type uE'} {H' : Type uH'}
    [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
    {M' : Type uM'} [TopologicalSpace M']
    {V : Type uV} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]
    [IsTopologicalAddGroup V] [ContinuousSMul ℝ V]

/-- A degree-`k`, `V`-valued pointwise differential form on a charted manifold.

Each value is a continuous alternating `k`-linear map on the tangent space. No smooth-section
regularity is hidden in this carrier. -/
abbrev ManifoldDifferentialForm
    (I : ModelWithCorners ℝ E H) (M : Type uM) [TopologicalSpace M] [ChartedSpace H M]
    (V : Type uV) [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]
    [IsTopologicalAddGroup V] [ContinuousSMul ℝ V] (k : ℕ) :=
  (x : M) → ContinuousAlternatingMap ℝ (TangentSpace I x) V (Fin k)

/-- Pull back a pointwise differential form along a smooth map using Mathlib's manifold derivative. -/
noncomputable def ManifoldDifferentialForm.pullback
    {I : ModelWithCorners ℝ E H} {I' : ModelWithCorners ℝ E' H'}
    [ChartedSpace H M] [ChartedSpace H' M']
    (f : M → M') (_smooth : ContMDiff I I' ∞ f)
    {k : ℕ} (form : ManifoldDifferentialForm I' M' V k) :
    ManifoldDifferentialForm I M V k :=
  fun x => (form (f x)).compContinuousLinearMap (mfderiv I I' f x)

/-- Evaluate a one-form on its single tangent-vector argument. -/
noncomputable def ManifoldDifferentialForm.evalOne
    {I : ModelWithCorners ℝ E H} [ChartedSpace H M]
    (form : ManifoldDifferentialForm I M V 1) (x : M) (v : TangentSpace I x) : V :=
  form x (fun _ => v)

/-- A two-form vanishes when both arguments are the same vector. -/
theorem ManifoldDifferentialForm.evalTwo_same
    {I : ModelWithCorners ℝ E H} [ChartedSpace H M]
    (form : ManifoldDifferentialForm I M V 2) (x : M) (v : TangentSpace I x) :
    form x (fun _ => v) = 0 := by
  exact (form x).map_eq_zero_of_eq (fun _ => v) (i := 0) (j := 1) rfl (by decide)

/-- Pullback preserves the zero form. -/
@[simp]
theorem ManifoldDifferentialForm.pullback_zero
    {I : ModelWithCorners ℝ E H} {I' : ModelWithCorners ℝ E' H'}
    [ChartedSpace H M] [ChartedSpace H' M']
    (f : M → M') (smooth : ContMDiff I I' ∞ f) (k : ℕ) :
    ManifoldDifferentialForm.pullback f smooth
      (0 : ManifoldDifferentialForm I' M' V k) = 0 := by
  rfl

end YangMills.Mathematics
