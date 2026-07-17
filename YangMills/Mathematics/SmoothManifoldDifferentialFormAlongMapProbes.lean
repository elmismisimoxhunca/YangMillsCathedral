/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Mathematics.SmoothManifoldDifferentialFormAlongMap

/-!
# Hostile probes for smooth differential-form evaluation along maps
-/

namespace YangMills.Mathematics.Probes

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
    [ChartedSpace H M]
    [ChartedSpace H' M'] [IsManifold I' ∞ M']

/-- Smoothness cannot be lost when along-map fields agree with ambient smooth fields. -/
theorem nonsmooth_formEvaluationAlongMap_blocked
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
    (agree : ∀ i x, x ∈ s → ambientFields i (f x) = fields i x)
    (failure : ¬ContMDiffOn I 𝓘(ℝ, W) ∞
      (fun x => coordinates (form (f x) (fun i => fields i x))) s) : False :=
  failure (form_smooth.eval_comp_of_ambientFields coordinates form f f_smooth f_maps
    fields ambientFields ambient_smooth agree)

/-- Restricting globally typed ambient fields along a smooth map cannot produce a nonsmooth form
evaluation. -/
theorem nonsmooth_restrictedAmbientFormEvaluation_blocked
    {k : ℕ} (coordinates : V ≃L[ℝ] W)
    (form : ManifoldDifferentialForm I' M' V k)
    (form_smooth : form.IsSmooth coordinates)
    (f : M → M') {s : Set M} {t : Set M'}
    (f_smooth : ContMDiffOn I I' ∞ f s)
    (f_maps : Set.MapsTo f s t)
    (ambientFields : Fin k → (y : M') → TangentSpace I' y)
    (ambient_smooth : ∀ i,
      ContMDiffOn I' (I'.prod 𝓘(ℝ, E')) ∞
        (fun y => (⟨y, ambientFields i y⟩ : TangentBundle I' M')) t)
    (failure : ¬ContMDiffOn I 𝓘(ℝ, W) ∞
      (fun x => coordinates (form (f x) (fun i => ambientFields i (f x)))) s) : False :=
  failure (form_smooth.eval_comp coordinates form f f_smooth f_maps
    ambientFields ambient_smooth)

end

end YangMills.Mathematics.Probes
