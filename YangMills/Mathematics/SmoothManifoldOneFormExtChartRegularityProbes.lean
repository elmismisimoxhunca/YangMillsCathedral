/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Mathematics.SmoothManifoldOneFormExtChartRegularity

/-!
# Hostile probes for generic one-form extended-chart regularity
-/

namespace YangMills.Mathematics.SmoothManifoldOneFormExtChartRegularity.Probes

open Set
open scoped Manifold ContDiff

universe uE uH uM uV uW

variable
    {E : Type uE} {H : Type uH}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace H]
    {M : Type uM} [TopologicalSpace M]
    {V : Type uV} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]
    [IsTopologicalAddGroup V] [ContinuousSMul ℝ V]
    {W : Type uW} [NormedAddCommGroup W] [NormedSpace ℝ W]
    {I : ModelWithCorners ℝ E H} [ChartedSpace H M] [IsManifold I ∞ M]

/-- Evaluation-based smoothness reconstructs the complete one-form carrier on the chart target. -/
theorem exact_chart_target_regularity
    (coordinates : V ≃L[ℝ] W)
    (form : SmoothManifoldDifferentialForm I M V coordinates 1)
    (p : M) :
    ContDiffWithinAt ℝ ∞ (form.toForm.inExtChartAt coordinates 1 p)
      (extChartAt I p).target ((extChartAt I p) p) :=
  SmoothManifoldDifferentialForm.inExtChartAt_contDiffWithinAt coordinates form p

/-- The same regularity holds on the exact corner-model range at the chart center. -/
theorem exact_model_range_regularity
    (coordinates : V ≃L[ℝ] W)
    (form : SmoothManifoldDifferentialForm I M V coordinates 1)
    (p : M) :
    ContDiffWithinAt ℝ ∞ (form.toForm.inExtChartAt coordinates 1 p)
      (Set.range ⇑I) ((extChartAt I p) p) :=
  SmoothManifoldDifferentialForm.inExtChartAt_contDiffWithinAt_range coordinates form p

/-- In particular the exact coordinate one-form is differentiable on `Set.range I`. -/
theorem exact_model_range_differentiability
    (coordinates : V ≃L[ℝ] W)
    (form : SmoothManifoldDifferentialForm I M V coordinates 1)
    (p : M) :
    DifferentiableWithinAt ℝ (form.toForm.inExtChartAt coordinates 1 p)
      (Set.range ⇑I) ((extChartAt I p) p) :=
  SmoothManifoldDifferentialForm.inExtChartAt_differentiableWithinAt_range coordinates form p

/-- A nonsmooth coordinate carrier contradicts generic finite-dimensional reconstruction. -/
theorem nonsmooth_chart_target_blocked
    (coordinates : V ≃L[ℝ] W)
    (form : SmoothManifoldDifferentialForm I M V coordinates 1)
    (p : M)
    (wrong : ¬ ContDiffWithinAt ℝ ∞ (form.toForm.inExtChartAt coordinates 1 p)
      (extChartAt I p).target ((extChartAt I p) p)) : False :=
  wrong (SmoothManifoldDifferentialForm.inExtChartAt_contDiffWithinAt coordinates form p)

/-- A nondifferentiable exact range carrier is likewise impossible. -/
theorem nondifferentiable_model_range_blocked
    (coordinates : V ≃L[ℝ] W)
    (form : SmoothManifoldDifferentialForm I M V coordinates 1)
    (p : M)
    (wrong : ¬ DifferentiableWithinAt ℝ (form.toForm.inExtChartAt coordinates 1 p)
      (Set.range ⇑I) ((extChartAt I p) p)) : False :=
  wrong (SmoothManifoldDifferentialForm.inExtChartAt_differentiableWithinAt_range
    coordinates form p)

end YangMills.Mathematics.SmoothManifoldOneFormExtChartRegularity.Probes
