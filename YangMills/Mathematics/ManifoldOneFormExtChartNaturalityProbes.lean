/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Mathematics.ManifoldOneFormExtChartNaturality

/-!
# Hostile probes for inverse-chart one-form Cartan naturality

The probes expose exact generic Cartan transport and reject a mismatched transported value. No
principal connection or derivative certificate is used.
-/

namespace YangMills.Mathematics.ManifoldOneFormExtChartNaturality.Probes

open Set Function
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
    [FiniteDimensional ℝ E]

/-- The intrinsic Cartan expression on chart-pulled constants equals the coordinate Cartan
expression with `Set.range I` tangent transport and the actual chart target calculus set. -/
theorem exact_inverse_chart_cartan_transport
    (coordinates : V ≃L[ℝ] W) (form : ManifoldDifferentialForm I M V 1)
    (p : M) (x : E) (hx : x ∈ (extChartAt I p).target) (v w : E)
    (hcoord : DifferentiableWithinAt ℝ
      (form.inExtChartAt coordinates 1 p) (extChartAt I p).target x) :
    form.oneFormCartanExpressionCoordinates coordinates (extChartAt I p).source
        ((extChartAt I p).symm x)
        (VectorField.mpullback I (modelWithCornersSelf ℝ E)
          (extChartAt I p) (fun _ => v))
        (VectorField.mpullback I (modelWithCornersSelf ℝ E)
          (extChartAt I p) (fun _ => w)) =
      ManifoldDifferentialForm.oneFormCartanExpressionCoordinates
        (I := modelWithCornersSelf ℝ E) (ContinuousLinearEquiv.refl ℝ W)
        (form.inExtChartAt coordinates 1 p).toManifoldForm
        (extChartAt I p).target x (fun _ => v) (fun _ => w) :=
  form.oneFormCartanExpressionCoordinates_inExtChartAt coordinates p x hx v w hcoord

/-- An unrelated or sign-reversed coordinate Cartan value cannot replace the exact transported
expression. -/
theorem mismatched_inverse_chart_cartan_transport_blocked
    (coordinates : V ≃L[ℝ] W) (form : ManifoldDifferentialForm I M V 1)
    (p : M) (x : E) (hx : x ∈ (extChartAt I p).target) (v w : E)
    (hcoord : DifferentiableWithinAt ℝ
      (form.inExtChartAt coordinates 1 p) (extChartAt I p).target x)
    (different :
      form.oneFormCartanExpressionCoordinates coordinates (extChartAt I p).source
          ((extChartAt I p).symm x)
          (VectorField.mpullback I (modelWithCornersSelf ℝ E)
            (extChartAt I p) (fun _ => v))
          (VectorField.mpullback I (modelWithCornersSelf ℝ E)
            (extChartAt I p) (fun _ => w)) ≠
        ManifoldDifferentialForm.oneFormCartanExpressionCoordinates
          (I := modelWithCornersSelf ℝ E) (ContinuousLinearEquiv.refl ℝ W)
          (form.inExtChartAt coordinates 1 p).toManifoldForm
          (extChartAt I p).target x (fun _ => v) (fun _ => w)) : False :=
  different (form.oneFormCartanExpressionCoordinates_inExtChartAt
    coordinates p x hx v w hcoord)

end YangMills.Mathematics.ManifoldOneFormExtChartNaturality.Probes
