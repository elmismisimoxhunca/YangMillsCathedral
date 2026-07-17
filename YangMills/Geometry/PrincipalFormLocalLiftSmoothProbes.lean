/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Geometry.PrincipalFormLocalLiftSmooth

/-!
# Hostile probes for smooth principal-form evaluation on local lifts
-/

namespace YangMills.Geometry.Probes

open Set
open scoped Manifold ContDiff Bundle

universe uEG uHG uEB uHB uEP uHP uG uB uP uV uW

noncomputable section

variable
    {EG : Type uEG} {HG : Type uHG}
    [NormedAddCommGroup EG] [NormedSpace ℝ EG] [TopologicalSpace HG]
    {EB : Type uEB} {HB : Type uHB}
    [NormedAddCommGroup EB] [NormedSpace ℝ EB] [TopologicalSpace HB]
    {EP : Type uEP} {HP : Type uHP}
    [NormedAddCommGroup EP] [NormedSpace ℝ EP] [TopologicalSpace HP]
    {G : Type uG} {B : Type uB} {P : Type uP}
    [Group G] [TopologicalSpace G] [TopologicalSpace B] [TopologicalSpace P]
    [IsTopologicalGroup G]
    {IG : ModelWithCorners ℝ EG HG}
    {IB : ModelWithCorners ℝ EB HB}
    {IP : ModelWithCorners ℝ EP HP}
    [ChartedSpace HG G] [LieGroup IG ∞ G]
    [ChartedSpace HB B] [IsManifold IB ∞ B]
    [ChartedSpace HP P] [IsManifold IP ∞ P]
    {torsor : PrincipalBundleTorsorData G B P}
    {bundle : TopologicalPrincipalBundleData torsor}
    {V : Type uV} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]
    [IsTopologicalAddGroup V] [ContinuousSMul ℝ V]
    {W : Type uW} [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- Smoothness of an exact principal form cannot be lost when it is evaluated on the exact local
lifts of smooth base fields. -/
theorem nonsmooth_principalForm_exactLocalLiftEvaluation_blocked
    {k : ℕ} (coordinates : V ≃L[ℝ] W)
    (form : YangMills.Mathematics.ManifoldDifferentialForm IP P V k)
    (form_smooth : form.IsSmooth coordinates)
    (smoothBundle : SmoothPrincipalBundleData IB IG IP torsor bundle)
    (chart : PrincipalBundleLocalTrivialization torsor)
    (chart_mem : chart ∈ bundle.trivializationAtlas)
    {s : Set B} (hs : s ⊆ chart.baseSet)
    (fields : Fin k → (b : B) → TangentSpace IB b)
    (fields_smooth : ∀ i, ContMDiffOn IB IB.tangent ∞
      (fun b => (⟨b, fields i b⟩ : TangentBundle IB B)) s)
    (failure : ¬ContMDiffOn IB 𝓘(ℝ, W) ∞
      (fun b => coordinates
        (form (principalBundleLocalSection chart b)
          (fun i => principalBundleLocalTangentLift (IB := IB) (IP := IP)
            chart b (fields i b)))) s) : False :=
  failure (principalBundleLocalTangentLift_formEvaluation_contMDiffOn
    coordinates form form_smooth smoothBundle chart chart_mem hs fields fields_smooth)

end

end YangMills.Geometry.Probes
