/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Mathematics.SmoothManifoldDifferentialForms

/-!
# Evaluation of smooth forms along smooth maps

The project's fixed-value smooth differential-form predicate is phrased using ambient tangent
fields. This module proves that a smooth form can be evaluated smoothly on fields along a smooth map
whenever those fields are restrictions of ambient smooth fields on a containing set.

The theorem is reusable manifold infrastructure. It does not postulate existence of ambient
extensions and does not mention Yang--Mills curvature.
-/

namespace YangMills.Mathematics

open Set
open scoped Manifold ContDiff

universe uE uH uM uE' uH' uM' uV uW

noncomputable section

variable
    {E : Type uE} {H : Type uH}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
    {M : Type uM} [TopologicalSpace M]
    {E' : Type uE'} {H' : Type uH'}
    [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
    {M' : Type uM'} [TopologicalSpace M']
    {V : Type uV} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]
    [IsTopologicalAddGroup V] [ContinuousSMul ℝ V]
    {W : Type uW} [NormedAddCommGroup W] [NormedSpace ℝ W]
    {I : ModelWithCorners ℝ E H} {I' : ModelWithCorners ℝ E' H'}
    [ChartedSpace H M] [IsManifold I ∞ M]
    [ChartedSpace H' M'] [IsManifold I' ∞ M']

namespace ManifoldDifferentialForm.IsSmooth

omit [IsManifold I ∞ M] in
/-- Smooth evaluation along a smooth map, provided the along-map tangent fields agree with ambient
smooth fields on a containing target set. -/
theorem eval_comp_of_ambientFields
    {k : ℕ} (coordinates : V ≃L[ℝ] W)
    (form : ManifoldDifferentialForm I' M' V k)
    (form_smooth : form.IsSmooth coordinates)
    (f : M → M') {s : Set M} {t : Set M'}
    (f_smooth : ContMDiffOn I I' ∞ f s)
    (f_maps : Set.MapsTo f s t)
    (fields : Fin k → (x : M) → TangentSpace I' (f x))
    (ambientFields : Fin k → (y : M') → TangentSpace I' y)
    (ambient_smooth : ∀ i,
      ContMDiffOn I' (I'.prod 𝓘(ℝ, E')) ∞
        (fun y => (⟨y, ambientFields i y⟩ : TangentBundle I' M')) t)
    (agree : ∀ i x, x ∈ s → ambientFields i (f x) = fields i x) :
    ContMDiffOn I 𝓘(ℝ, W) ∞
      (fun x => coordinates (form (f x) (fun i => fields i x))) s := by
  have ambientEvaluation := form_smooth t ambientFields ambient_smooth
  have composed := ambientEvaluation.comp f_smooth f_maps
  refine composed.congr ?_
  intro x hx
  congr 2
  funext i
  exact (agree i x hx).symm

omit [IsManifold I ∞ M] in
/-- The same result when the along-map fields are definitionally restrictions of the ambient
fields. -/
theorem eval_comp
    {k : ℕ} (coordinates : V ≃L[ℝ] W)
    (form : ManifoldDifferentialForm I' M' V k)
    (form_smooth : form.IsSmooth coordinates)
    (f : M → M') {s : Set M} {t : Set M'}
    (f_smooth : ContMDiffOn I I' ∞ f s)
    (f_maps : Set.MapsTo f s t)
    (ambientFields : Fin k → (y : M') → TangentSpace I' y)
    (ambient_smooth : ∀ i,
      ContMDiffOn I' (I'.prod 𝓘(ℝ, E')) ∞
        (fun y => (⟨y, ambientFields i y⟩ : TangentBundle I' M')) t) :
    ContMDiffOn I 𝓘(ℝ, W) ∞
      (fun x => coordinates (form (f x) (fun i => ambientFields i (f x)))) s :=
  form_smooth.eval_comp_of_ambientFields coordinates form f f_smooth f_maps
    (fun i x => ambientFields i (f x)) ambientFields ambient_smooth (by simp)

end ManifoldDifferentialForm.IsSmooth

end

end YangMills.Mathematics
