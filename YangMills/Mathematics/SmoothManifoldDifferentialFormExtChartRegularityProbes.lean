/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Mathematics.SmoothManifoldDifferentialFormExtChartRegularity

namespace YangMills.Mathematics.SmoothManifoldDifferentialFormExtChartRegularity.Probes

open Set
open scoped Manifold ContDiff Topology
open YangMills.Mathematics

universe uE uH uM uV uW

variable
    {E : Type uE} {H : Type uH}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace H]
    {M : Type uM} [TopologicalSpace M]
    {V : Type uV} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]
    [IsTopologicalAddGroup V] [ContinuousSMul ℝ V]
    {W : Type uW} [NormedAddCommGroup W] [NormedSpace ℝ W]
    {I : ModelWithCorners ℝ E H} [ChartedSpace H M] [IsManifold I ∞ M]

noncomputable section

/-- The generic helper supplies a smooth intrinsic field on the exact chart source. -/
theorem exact_pulled_constant_field_smooth
    (p : M) (v : E) :
    ManifoldTangentField.IsSmoothOn I (extChartAt I p).source
      (extChartPulledBackConstantField (I := I) p v) :=
  extChartPulledBackConstantField_isSmoothOn p v

/-- Arbitrary degree retains distinct exact-target and full-model-range `C∞` regularity. -/
theorem exact_target_and_modelRange_regularity
    (coordinates : V ≃L[ℝ] W) (k : ℕ)
    (form : SmoothManifoldDifferentialForm I M V coordinates k) (p : M) :
    ContDiffWithinAt ℝ ∞ (form.toForm.inExtChartAt coordinates k p)
        (extChartAt I p).target ((extChartAt I p) p) ∧
      ContDiffWithinAt ℝ ∞ (form.toForm.inExtChartAt coordinates k p)
        (Set.range ⇑I) ((extChartAt I p) p) :=
  ⟨form.inExtChartAt_contDiffWithinAt_target coordinates k p,
    form.inExtChartAt_contDiffWithinAt_modelRange coordinates k p⟩

/-- The differentiability corollaries retain the same two noninterchangeable calculus sets. -/
theorem exact_target_and_modelRange_differentiability
    (coordinates : V ≃L[ℝ] W) (k : ℕ)
    (form : SmoothManifoldDifferentialForm I M V coordinates k) (p : M) :
    DifferentiableWithinAt ℝ (form.toForm.inExtChartAt coordinates k p)
        (extChartAt I p).target ((extChartAt I p) p) ∧
      DifferentiableWithinAt ℝ (form.toForm.inExtChartAt coordinates k p)
        (Set.range ⇑I) ((extChartAt I p) p) :=
  ⟨form.inExtChartAt_differentiableWithinAt_target coordinates k p,
    form.inExtChartAt_differentiableWithinAt_modelRange coordinates k p⟩

/-- A hostile failure of exact-target regularity contradicts the arbitrary-degree reconstruction. -/
theorem nonsmooth_target_coordinate_blocked
    (coordinates : V ≃L[ℝ] W) (k : ℕ)
    (form : SmoothManifoldDifferentialForm I M V coordinates k) (p : M)
    (hostile : ¬ ContDiffWithinAt ℝ ∞ (form.toForm.inExtChartAt coordinates k p)
      (extChartAt I p).target ((extChartAt I p) p)) : False :=
  hostile (form.inExtChartAt_contDiffWithinAt_target coordinates k p)

/-- A hostile failure on the full corner-model range is rejected independently of target regularity. -/
theorem nonsmooth_modelRange_coordinate_blocked
    (coordinates : V ≃L[ℝ] W) (k : ℕ)
    (form : SmoothManifoldDifferentialForm I M V coordinates k) (p : M)
    (hostile : ¬ ContDiffWithinAt ℝ ∞ (form.toForm.inExtChartAt coordinates k p)
      (Set.range ⇑I) ((extChartAt I p) p)) : False :=
  hostile (form.inExtChartAt_contDiffWithinAt_modelRange coordinates k p)

end

end YangMills.Mathematics.SmoothManifoldDifferentialFormExtChartRegularity.Probes
