/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Geometry.PrincipalBundleLocalTangentLiftSmooth

/-!
# Ambient extensions of principal local tangent lifts

In a designated principal chart, a smooth base tangent field extends to a smooth tangent field on
the corresponding part of the total space. The construction transports the base field with zero
group component through the inverse principal chart and agrees exactly with the derivative-based
local lift at group coordinate `1`.

The field is totalized by zero outside the chart source only to provide a dependent function; no
smoothness is claimed outside the stated set. No connection, curvature, or regularity certificate is
introduced.
-/

namespace YangMills.Geometry

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

private def principalBundleHorizontalCoordinateField
    (field : (b : B) → TangentSpace IB b) (z : B × G) :
    TangentBundle (IB.prod IG) (B × G) :=
  (equivTangentBundleProd IB B IG G).symm
    (⟨z.1, field z.1⟩, ⟨z.2, 0⟩)

omit [IsTopologicalGroup G] in
private theorem principalBundleHorizontalCoordinateField_contMDiffOn
    {s : Set B}
    (field : (b : B) → TangentSpace IB b)
    (field_smooth : ContMDiffOn IB IB.tangent ∞
      (fun b => (⟨b, field b⟩ : TangentBundle IB B)) s) :
    ContMDiffOn (IB.prod IG) (IB.prod IG).tangent ∞
      (principalBundleHorizontalCoordinateField (IG := IG) field)
      (s ×ˢ (Set.univ : Set G)) := by
  have firstSmooth : ContMDiffOn (IB.prod IG) IB.tangent ∞
      (fun z : B × G => (⟨z.1, field z.1⟩ : TangentBundle IB B))
      (s ×ˢ (Set.univ : Set G)) := by
    exact field_smooth.comp contMDiffOn_fst (by intro z hz; exact hz.1)
  have secondSmooth : ContMDiffOn (IB.prod IG) IG.tangent ∞
      (fun z : B × G => (⟨z.2, 0⟩ : TangentBundle IG G))
      (s ×ˢ (Set.univ : Set G)) := by
    exact ((Bundle.contMDiff_zeroSection ℝ (TangentSpace IG : G → Type _)).comp
      contMDiff_snd).contMDiffOn
  convert (contMDiff_equivTangentBundleProd_symm.comp_contMDiffOn
      (firstSmooth.prodMk secondSmooth)) using 1; rfl

private def principalBundleLocalAmbientTotal
    (chart : PrincipalBundleLocalTrivialization torsor)
    (field : (b : B) → TangentSpace IB b) (p : P) : TangentBundle IP P :=
  tangentMapWithin (IB.prod IG) IP chart.toPartialHomeomorph.symm
    chart.toPartialHomeomorph.target
    (principalBundleHorizontalCoordinateField (IG := IG) field
      (chart.toPartialHomeomorph p))

private theorem principalBundleLocalAmbientTotal_contMDiffOn
    (smoothBundle : SmoothPrincipalBundleData IB IG IP torsor bundle)
    (chart : PrincipalBundleLocalTrivialization torsor)
    (chart_mem : chart ∈ bundle.trivializationAtlas)
    {s : Set B} (hs : s ⊆ chart.baseSet)
    (field : (b : B) → TangentSpace IB b)
    (field_smooth : ContMDiffOn IB IB.tangent ∞
      (fun b => (⟨b, field b⟩ : TangentBundle IB B)) s) :
    ContMDiffOn IP IP.tangent ∞
      (principalBundleLocalAmbientTotal (IG := IG) (IB := IB) (IP := IP) chart field)
      (chart.toPartialHomeomorph.source ∩ torsor.projection ⁻¹' s) := by
  have coordSmooth : ContMDiffOn (IB.prod IG) (IB.prod IG).tangent ∞
      (principalBundleHorizontalCoordinateField (IG := IG) field)
      (s ×ˢ (Set.univ : Set G)) :=
    principalBundleHorizontalCoordinateField_contMDiffOn field field_smooth
  have coordMaps : Set.MapsTo
      (principalBundleHorizontalCoordinateField (IG := IG) field)
      (s ×ˢ (Set.univ : Set G))
      (Bundle.TotalSpace.proj ⁻¹' chart.toPartialHomeomorph.target) := by
    intro z hz
    rw [chart.target_eq]
    exact ⟨hs hz.1, Set.mem_univ z.2⟩
  have inverseTangentSmooth :=
    (smoothBundle.inverse_trivialization_smooth chart chart_mem)
      |>.contMDiffOn_tangentMapWithin (m := ∞) (by simp)
        chart.toPartialHomeomorph.open_target.uniqueMDiffOn
  have coordinateOutputSmooth := inverseTangentSmooth.comp coordSmooth coordMaps
  have chartMaps : Set.MapsTo chart.toPartialHomeomorph
      (chart.toPartialHomeomorph.source ∩ torsor.projection ⁻¹' s)
      (s ×ˢ (Set.univ : Set G)) := by
    intro p hp
    exact ⟨by rw [chart.base_coordinate p hp.1]; exact hp.2, Set.mem_univ _⟩
  convert coordinateOutputSmooth.comp
      ((smoothBundle.trivialization_smooth chart chart_mem).mono Set.inter_subset_left)
      chartMaps using 1; rfl

omit [IsTopologicalGroup G] [LieGroup IG ∞ G] [IsManifold IB ∞ B]
    [IsManifold IP ∞ P] in
private theorem principalBundleLocalAmbientTotal_proj
    (chart : PrincipalBundleLocalTrivialization torsor)
    (field : (b : B) → TangentSpace IB b)
    {p : P} (hp : p ∈ chart.toPartialHomeomorph.source) :
    (principalBundleLocalAmbientTotal (IG := IG) (IB := IB) (IP := IP)
      chart field p).proj = p := by
  change chart.toPartialHomeomorph.symm (chart.toPartialHomeomorph p) = p
  exact chart.toPartialHomeomorph.left_inv hp

private def tangentBundleFiberOfEq
    (q : TangentBundle IP P) (p : P) (h : q.proj = p) : TangentSpace IP p :=
  h ▸ q.2

omit [IsManifold IP ∞ P] in
private theorem tangentBundle_mk_fiberOfEq
    (q : TangentBundle IP P) (p : P) (h : q.proj = p) :
    (⟨p, tangentBundleFiberOfEq q p h⟩ : TangentBundle IP P) = q := by
  subst p
  rfl

private theorem principalBundleLocalAmbientTotal_localSection
    (smoothBundle : SmoothPrincipalBundleData IB IG IP torsor bundle)
    (chart : PrincipalBundleLocalTrivialization torsor)
    (chart_mem : chart ∈ bundle.trivializationAtlas)
    (field : (b : B) → TangentSpace IB b)
    {b : B} (hb : b ∈ chart.baseSet) :
    principalBundleLocalAmbientTotal (IG := IG) (IB := IB) (IP := IP)
        chart field (principalBundleLocalSection chart b) =
      (⟨principalBundleLocalSection chart b,
        principalBundleLocalTangentLift (IB := IB) (IP := IP)
          chart b (field b)⟩ : TangentBundle IP P) := by
  let input : TangentBundle IB B := ⟨b, field b⟩
  have targetMem := principalBundleLocalSection_pair_mem_target chart hb
  have inverseMDiff : MDifferentiableAt (IB.prod IG) IP
      chart.toPartialHomeomorph.symm (b, (1 : G)) :=
    ((smoothBundle.inverse_trivialization_smooth chart chart_mem).contMDiffAt
      (chart.toPartialHomeomorph.open_target.mem_nhds targetMem)).mdifferentiableAt (by simp)
  have pairSmooth : ContMDiff IB (IB.prod IG) ∞
      (fun x : B => (x, (1 : G))) :=
    contMDiff_id.prodMk contMDiff_const
  have pairMDiff : MDifferentiableAt IB (IB.prod IG)
      (fun x : B => (x, (1 : G))) b :=
    pairSmooth.mdifferentiableAt (by simp)
  have chain := tangentMap_comp_at input inverseMDiff pairMDiff
  have pairTangent :
      tangentMap IB (IB.prod IG) (fun x : B => (x, (1 : G))) input =
        principalBundleHorizontalCoordinateField (IG := IG) field (b, (1 : G)) := by
    rw [tangentMap_prod_left]
    rfl
  change tangentMapWithin (IB.prod IG) IP chart.toPartialHomeomorph.symm
      chart.toPartialHomeomorph.target
      (principalBundleHorizontalCoordinateField (IG := IG) field
        (chart.toPartialHomeomorph (principalBundleLocalSection chart b))) =
    tangentMap IB IP (principalBundleLocalSection chart) input
  simp only [principalBundleLocalSection, chart.toPartialHomeomorph.right_inv targetMem]
  rw [tangentMapWithin_eq_tangentMap
    (chart.toPartialHomeomorph.open_target.uniqueMDiffWithinAt targetMem) inverseMDiff]
  rw [← pairTangent]
  exact chain.symm

/-- A smooth tangent field on the source of a designated principal chart whose restriction to the
chart's identity-coordinate local section is the derivative-based local lift of the given base
field. The witness is totalized by zero away from the chart source; no regularity is claimed there. -/
theorem exists_principalBundleLocalTangentLift_ambientField
    (smoothBundle : SmoothPrincipalBundleData IB IG IP torsor bundle)
    (chart : PrincipalBundleLocalTrivialization torsor)
    (chart_mem : chart ∈ bundle.trivializationAtlas)
    {s : Set B} (hs : s ⊆ chart.baseSet)
    (field : (b : B) → TangentSpace IB b)
    (field_smooth : ContMDiffOn IB IB.tangent ∞
      (fun b => (⟨b, field b⟩ : TangentBundle IB B)) s) :
    ∃ ambientField : (p : P) → TangentSpace IP p,
      ContMDiffOn IP IP.tangent ∞
        (fun p => (⟨p, ambientField p⟩ : TangentBundle IP P))
        (chart.toPartialHomeomorph.source ∩ torsor.projection ⁻¹' s) ∧
      ∀ ⦃b : B⦄, b ∈ s →
        ambientField (principalBundleLocalSection chart b) =
          principalBundleLocalTangentLift (IB := IB) (IP := IP)
            chart b (field b) := by
  classical
  let total : P → TangentBundle IP P :=
    principalBundleLocalAmbientTotal (IG := IG) (IB := IB) (IP := IP) chart field
  let ambientField : (p : P) → TangentSpace IP p := fun p =>
    if hp : p ∈ chart.toPartialHomeomorph.source then
      tangentBundleFiberOfEq (total p) p
        (principalBundleLocalAmbientTotal_proj (IG := IG) (IB := IB) (IP := IP)
          chart field hp)
    else 0
  have mk_ambient_eq_total {p : P} (hp : p ∈ chart.toPartialHomeomorph.source) :
      (⟨p, ambientField p⟩ : TangentBundle IP P) = total p := by
    simp only [ambientField, hp, dite_true]
    exact tangentBundle_mk_fiberOfEq _ _ _
  refine ⟨ambientField, ?_, ?_⟩
  · refine (principalBundleLocalAmbientTotal_contMDiffOn smoothBundle chart chart_mem hs
      field field_smooth).congr ?_
    intro p hp
    exact mk_ambient_eq_total hp.1
  · intro b hb
    have hbChart := hs hb
    have sectionMem : principalBundleLocalSection chart b ∈
        chart.toPartialHomeomorph.source :=
      chart.toPartialHomeomorph.map_target
        (principalBundleLocalSection_pair_mem_target chart hbChart)
    have bundledEq :
        (⟨principalBundleLocalSection chart b,
          ambientField (principalBundleLocalSection chart b)⟩ : TangentBundle IP P) =
        (⟨principalBundleLocalSection chart b,
          principalBundleLocalTangentLift (IB := IB) (IP := IP)
            chart b (field b)⟩ : TangentBundle IP P) := by
      rw [mk_ambient_eq_total sectionMem]
      exact principalBundleLocalAmbientTotal_localSection smoothBundle chart chart_mem field hbChart
    injection bundledEq


end

end YangMills.Geometry
