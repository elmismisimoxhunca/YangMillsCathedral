/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Geometry.PrincipalBundleLocalTangentLiftAmbient
import YangMills.Mathematics.SmoothManifoldDifferentialFormAlongMap

/-!
# Smooth principal-form evaluation on exact local lifts

A smooth fixed-value differential form on a principal total space evaluates smoothly on the exact
local tangent lifts of smooth base tangent fields. The proof consumes the chart-local ambient
extensions constructed in the preceding geometry layer.

This is a generic evaluation theorem. It does not mention connections or curvature and does not add
a regularity certificate.
-/

namespace YangMills.Geometry

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

/-- A smooth principal-space form evaluates smoothly on exact local lifts of smooth base tangent
fields. -/
theorem principalBundleLocalTangentLift_formEvaluation_contMDiffOn
    {k : ℕ} (coordinates : V ≃L[ℝ] W)
    (form : YangMills.Mathematics.ManifoldDifferentialForm IP P V k)
    (form_smooth : form.IsSmooth coordinates)
    (smoothBundle : SmoothPrincipalBundleData IB IG IP torsor bundle)
    (chart : PrincipalBundleLocalTrivialization torsor)
    (chart_mem : chart ∈ bundle.trivializationAtlas)
    {s : Set B} (hs : s ⊆ chart.baseSet)
    (fields : Fin k → (b : B) → TangentSpace IB b)
    (fields_smooth : ∀ i, ContMDiffOn IB IB.tangent ∞
      (fun b => (⟨b, fields i b⟩ : TangentBundle IB B)) s) :
    ContMDiffOn IB 𝓘(ℝ, W) ∞
      (fun b => coordinates
        (form (principalBundleLocalSection chart b)
          (fun i => principalBundleLocalTangentLift (IB := IB) (IP := IP)
            chart b (fields i b)))) s := by
  classical
  have extensions : ∀ i, ∃ ambientField : (p : P) → TangentSpace IP p,
      ContMDiffOn IP IP.tangent ∞
        (fun p => (⟨p, ambientField p⟩ : TangentBundle IP P))
        (chart.toPartialHomeomorph.source ∩ torsor.projection ⁻¹' s) ∧
      ∀ ⦃b : B⦄, b ∈ s →
        ambientField (principalBundleLocalSection chart b) =
          principalBundleLocalTangentLift (IB := IB) (IP := IP)
            chart b (fields i b) := fun i =>
    exists_principalBundleLocalTangentLift_ambientField smoothBundle chart chart_mem hs
      (fields i) (fields_smooth i)
  choose ambientFields ambientSmooth ambientAgree using extensions
  exact form_smooth.eval_comp_of_ambientFields (s := s)
    (t := chart.toPartialHomeomorph.source ∩ torsor.projection ⁻¹' s)
    coordinates form (principalBundleLocalSection chart)
    ((principalBundleLocalSection_contMDiffOn smoothBundle chart chart_mem).mono hs)
    (fun b hb => ⟨chart.toPartialHomeomorph.map_target
      (principalBundleLocalSection_pair_mem_target chart (hs hb)), by
        change torsor.projection (principalBundleLocalSection chart b) ∈ s
        rw [principalBundleLocalSection_projection chart (hs hb)]
        exact hb⟩)
    (fun i b => principalBundleLocalTangentLift (IB := IB) (IP := IP)
      chart b (fields i b)) ambientFields ambientSmooth
    (fun i b hb => ambientAgree i hb)

end

end YangMills.Geometry
