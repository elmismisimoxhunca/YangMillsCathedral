/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Mathematics.ManifoldDifferentialForms
import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection

/-!
# Smooth manifold differential forms by local vector-field evaluation

A pointwise form is smooth when evaluating it on every tuple of locally smooth tangent-vector
fields gives a smooth value function. Values may be represented in a normed model through an
explicit continuous linear equivalence. This avoids pretending that the raw pointwise family has a
canonical product topology.
-/

namespace YangMills.Mathematics

open Set
open scoped Manifold ContDiff

universe uE uH uM uV uW uW₂

variable
    {E : Type uE} {H : Type uH}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
    {M : Type uM} [TopologicalSpace M]
    {V : Type uV} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]
    [IsTopologicalAddGroup V] [ContinuousSMul ℝ V]
    {W : Type uW} [NormedAddCommGroup W] [NormedSpace ℝ W]
    {W₂ : Type uW₂} [NormedAddCommGroup W₂] [NormedSpace ℝ W₂]

/-- Local smoothness of a pointwise differential form, tested against locally smooth tangent fields.

The explicit `valueCoordinates` map is essential when the value type is an intrinsic tangent or
Lie-algebra type whose topology is available but whose normed model is intentionally opaque. -/
def ManifoldDifferentialForm.IsSmooth
    {I : ModelWithCorners ℝ E H} [ChartedSpace H M] [IsManifold I ∞ M]
    {k : ℕ} (valueCoordinates : V ≃L[ℝ] W)
    (form : ManifoldDifferentialForm I M V k) : Prop :=
  ∀ (s : Set M) (fields : Fin k → (x : M) → TangentSpace I x),
    (∀ i, ContMDiffOn I (I.prod (modelWithCornersSelf ℝ E)) ∞
      (fun x => (⟨x, fields i x⟩ : TangentBundle I M)) s) →
    ContMDiffOn I (modelWithCornersSelf ℝ W) ∞
      (fun x => valueCoordinates (form x (fun i => fields i x))) s

namespace ManifoldDifferentialForm

/-- Smoothness does not depend on the chosen continuously linearly equivalent normed value model. -/
theorem isSmooth_iff_valueCoordinates
    {I : ModelWithCorners ℝ E H} [ChartedSpace H M] [IsManifold I ∞ M]
    {k : ℕ} (firstCoordinates : V ≃L[ℝ] W) (secondCoordinates : V ≃L[ℝ] W₂)
    (form : ManifoldDifferentialForm I M V k) :
    form.IsSmooth firstCoordinates ↔ form.IsSmooth secondCoordinates := by
  constructor
  · intro smooth s fields fields_smooth
    have firstSmooth := smooth s fields fields_smooth
    have secondSmooth := (firstCoordinates.symm.trans secondCoordinates).toContinuousLinearMap
      |>.contMDiff.comp_contMDiffOn firstSmooth
    simpa [Function.comp_def] using secondSmooth
  · intro smooth s fields fields_smooth
    have secondSmooth := smooth s fields fields_smooth
    have firstSmooth := (secondCoordinates.symm.trans firstCoordinates).toContinuousLinearMap
      |>.contMDiff.comp_contMDiffOn secondSmooth
    simpa [Function.comp_def] using firstSmooth

end ManifoldDifferentialForm

/-- A pointwise form bundled together with genuine local smoothness evidence. -/
structure SmoothManifoldDifferentialForm
    (I : ModelWithCorners ℝ E H) (M : Type uM) [TopologicalSpace M]
    [ChartedSpace H M] [IsManifold I ∞ M]
    (V : Type uV) [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]
    [IsTopologicalAddGroup V] [ContinuousSMul ℝ V]
    {W : Type uW} [NormedAddCommGroup W] [NormedSpace ℝ W]
    (valueCoordinates : V ≃L[ℝ] W) (k : ℕ) where
  /-- Underlying degree-`k` pointwise differential form. -/
  toForm : ManifoldDifferentialForm I M V k
  /-- Local smoothness under evaluation on locally smooth vector fields. -/
  smooth : toForm.IsSmooth valueCoordinates

namespace SmoothManifoldDifferentialForm

variable {I : ModelWithCorners ℝ E H} [ChartedSpace H M] [IsManifold I ∞ M]
variable {valueCoordinates : V ≃L[ℝ] W} {k : ℕ}

/-- Evaluation on any locally smooth tuple of fields is smooth by construction. -/
theorem eval_smooth
    (form : SmoothManifoldDifferentialForm I M V valueCoordinates k)
    (s : Set M) (fields : Fin k → (x : M) → TangentSpace I x)
    (fields_smooth : ∀ i, ContMDiffOn I (I.prod (modelWithCornersSelf ℝ E)) ∞
      (fun x => (⟨x, fields i x⟩ : TangentBundle I M)) s) :
    ContMDiffOn I (modelWithCornersSelf ℝ W) ∞
      (fun x => valueCoordinates (form.toForm x (fun i => fields i x))) s :=
  form.smooth s fields fields_smooth

/-- The zero form is smooth in every degree. -/
noncomputable def zero (valueCoordinates : V ≃L[ℝ] W) (k : ℕ) :
    SmoothManifoldDifferentialForm I M V valueCoordinates k where
  toForm := 0
  smooth := by
    intro s fields fields_smooth
    simpa using (contMDiff_const : ContMDiff I (modelWithCornersSelf ℝ W) ∞
      (fun _ : M => (0 : W))).contMDiffOn

end SmoothManifoldDifferentialForm

end YangMills.Mathematics
