/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Mathematics.SmoothManifoldDifferentialFormDiffeomorphPullback

namespace YangMills.Mathematics.SmoothManifoldDifferentialFormDiffeomorphPullback.Probes

open scoped Manifold ContDiff

universe uE uE' uH uH' uM uM' uV uW
noncomputable section

variable {E : Type uE} {E' : Type uE'} {H : Type uH} {H' : Type uH'}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
    [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
    {M : Type uM} {M' : Type uM'} [TopologicalSpace M] [TopologicalSpace M']
    {I : ModelWithCorners ℝ E H} {I' : ModelWithCorners ℝ E' H'}
    [ChartedSpace H M] [IsManifold I ∞ M]
    [ChartedSpace H' M'] [IsManifold I' ∞ M']
    {V : Type uV} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]
    [IsTopologicalAddGroup V] [ContinuousSMul ℝ V]
    {W : Type uW} [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- The smooth wrapper retains the exact manifold pullback carrier. -/
theorem exact_smooth_diffeomorph_pullback
    (e : M ≃ₘ^∞⟮I, I'⟯ M') (coordinates : V ≃L[ℝ] W) (k : ℕ)
    (form : SmoothManifoldDifferentialForm I' M' V coordinates k) :
    (form.pullbackDiffeomorph e coordinates k).toForm =
      form.toForm.pullback e e.contMDiff := rfl

/-- A different pointwise carrier cannot be substituted for the exact pullback. -/
theorem changed_smooth_diffeomorph_pullback_blocked
    (e : M ≃ₘ^∞⟮I, I'⟯ M') (coordinates : V ≃L[ℝ] W) (k : ℕ)
    (form : SmoothManifoldDifferentialForm I' M' V coordinates k)
    (changed : (form.pullbackDiffeomorph e coordinates k).toForm ≠
      form.toForm.pullback e e.contMDiff) : False := changed rfl

end

end YangMills.Mathematics.SmoothManifoldDifferentialFormDiffeomorphPullback.Probes
