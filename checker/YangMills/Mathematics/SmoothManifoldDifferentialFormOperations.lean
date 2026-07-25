/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Mathematics.SmoothManifoldDifferentialForms
import Mathlib.Geometry.Manifold.Algebra.SMul

/-!
# Linear operations on smooth manifold differential forms

Addition and real scalar multiplication preserve the local vector-field evaluation criterion for
smooth differential forms. These operations are bundled without changing their pointwise meanings.
-/

namespace YangMills.Mathematics

open Set
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

namespace SmoothManifoldDifferentialForm

/-- Add two smooth forms of the same degree and value type. -/
noncomputable def add
    (first second : SmoothManifoldDifferentialForm I M V coordinates k) :
    SmoothManifoldDifferentialForm I M V coordinates k where
  toForm := first.toForm + second.toForm
  smooth := by
    intro s fields fields_smooth
    have first_smooth := first.eval_smooth s fields fields_smooth
    have second_smooth := second.eval_smooth s fields fields_smooth
    convert first_smooth.add second_smooth using 1
    funext x
    simp

/-- Multiply a smooth form by a real scalar. -/
noncomputable def smul (scalar : ℝ)
    (form : SmoothManifoldDifferentialForm I M V coordinates k) :
    SmoothManifoldDifferentialForm I M V coordinates k where
  toForm := scalar • form.toForm
  smooth := by
    intro s fields fields_smooth
    have form_smooth := form.eval_smooth s fields fields_smooth
    have scalar_smooth : ContMDiffOn I (modelWithCornersSelf ℝ ℝ) ∞
        (fun _ : M => scalar) s :=
      contMDiff_const.contMDiffOn
    convert scalar_smooth.smul form_smooth using 1
    funext x
    simp

@[simp]
theorem add_toForm
    (first second : SmoothManifoldDifferentialForm I M V coordinates k) :
    (add first second).toForm = first.toForm + second.toForm :=
  rfl

@[simp]
theorem smul_toForm (scalar : ℝ)
    (form : SmoothManifoldDifferentialForm I M V coordinates k) :
    (smul scalar form).toForm = scalar • form.toForm :=
  rfl

end SmoothManifoldDifferentialForm

end YangMills.Mathematics
