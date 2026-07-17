/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Geometry.PrincipalBundleLocalTangentLiftAmbient

/-!
# Hostile probes for ambient extensions of principal local tangent lifts
-/

namespace YangMills.Geometry.Probes

open Set
open scoped Manifold ContDiff Bundle

universe uEG uHG uEB uHB uEP uHP uG uB uP

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

/-- A smooth base field cannot fail to have a smooth ambient extension on the exact chart subset. -/
theorem missing_principalBundleLocalTangentLift_ambientField_blocked
    (smoothBundle : SmoothPrincipalBundleData IB IG IP torsor bundle)
    (chart : PrincipalBundleLocalTrivialization torsor)
    (chart_mem : chart ∈ bundle.trivializationAtlas)
    {s : Set B} (hs : s ⊆ chart.baseSet)
    (field : (b : B) → TangentSpace IB b)
    (field_smooth : ContMDiffOn IB IB.tangent ∞
      (fun b => (⟨b, field b⟩ : TangentBundle IB B)) s)
    (failure : ¬∃ ambientField : (p : P) → TangentSpace IP p,
      ContMDiffOn IP IP.tangent ∞
        (fun p => (⟨p, ambientField p⟩ : TangentBundle IP P))
        (chart.toPartialHomeomorph.source ∩ torsor.projection ⁻¹' s) ∧
      ∀ ⦃b : B⦄, b ∈ s →
        ambientField (principalBundleLocalSection chart b) =
          principalBundleLocalTangentLift (IB := IB) (IP := IP)
            chart b (field b)) : False :=
  failure (exists_principalBundleLocalTangentLift_ambientField
    smoothBundle chart chart_mem hs field field_smooth)

/-- It is impossible that every smooth ambient extension disagrees with the exact local lift at
some point of the specified base set. -/
theorem universal_principalBundleLocalTangentLift_disagreement_blocked
    (smoothBundle : SmoothPrincipalBundleData IB IG IP torsor bundle)
    (chart : PrincipalBundleLocalTrivialization torsor)
    (chart_mem : chart ∈ bundle.trivializationAtlas)
    {s : Set B} (hs : s ⊆ chart.baseSet)
    (field : (b : B) → TangentSpace IB b)
    (field_smooth : ContMDiffOn IB IB.tangent ∞
      (fun b => (⟨b, field b⟩ : TangentBundle IB B)) s)
    (disagrees : ∀ ambientField : (p : P) → TangentSpace IP p,
      ContMDiffOn IP IP.tangent ∞
        (fun p => (⟨p, ambientField p⟩ : TangentBundle IP P))
        (chart.toPartialHomeomorph.source ∩ torsor.projection ⁻¹' s) →
      ∃ b, b ∈ s ∧
        ambientField (principalBundleLocalSection chart b) ≠
          principalBundleLocalTangentLift (IB := IB) (IP := IP)
            chart b (field b)) : False := by
  obtain ⟨ambientField, ambientSmooth, ambientAgree⟩ :=
    exists_principalBundleLocalTangentLift_ambientField
      smoothBundle chart chart_mem hs field field_smooth
  obtain ⟨b, hb, mismatch⟩ := disagrees ambientField ambientSmooth
  exact mismatch (ambientAgree hb)

end

end YangMills.Geometry.Probes
