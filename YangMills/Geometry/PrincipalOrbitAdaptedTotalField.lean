/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Geometry.PrincipalOrbitAdaptedProductBracket
import YangMills.Mathematics.ManifoldOneFormExteriorDerivativeDiffeomorph
import Mathlib.Geometry.Manifold.LocalDiffeomorph

/-!
# Orbit-adapted tangent fields on a principal total space

Product-coordinate adapted fields are transported through one designated smooth principal partial
trivialization. At points normalized to fiber coordinate `1`, this yields arbitrary prescribed
tangent values, smoothness on an exact open full-fiber source, all-group right-translation
adaptation, and zero within-bracket with the principal fundamental field.
-/

namespace YangMills.Geometry.PrincipalOrbitAdapted

open Set Function Bundle
open scoped Manifold ContDiff
open YangMills.Mathematics

universe uEG uHG uEB uHB uEP uHP uG uB uP

noncomputable section
set_option maxHeartbeats 2000000

variable
    {EG : Type uEG} {HG : Type uHG}
    [NormedAddCommGroup EG] [NormedSpace ℝ EG] [FiniteDimensional ℝ EG]
    [TopologicalSpace HG]
    {EB : Type uEB} {HB : Type uHB}
    [NormedAddCommGroup EB] [NormedSpace ℝ EB] [FiniteDimensional ℝ EB]
    [TopologicalSpace HB]
    {EP : Type uEP} {HP : Type uHP}
    [NormedAddCommGroup EP] [NormedSpace ℝ EP] [FiniteDimensional ℝ EP]
    [TopologicalSpace HP]
    {G : Type uG} {B : Type uB} {P : Type uP}
    [Group G] [TopologicalSpace G] [TopologicalSpace B] [TopologicalSpace P]
    [IsTopologicalGroup G]
    (IG : ModelWithCorners ℝ EG HG)
    (IB : ModelWithCorners ℝ EB HB)
    (IP : ModelWithCorners ℝ EP HP)
    [ChartedSpace HG G] [LieGroup IG ∞ G]
    [ChartedSpace HB B] [IsManifold IB ∞ B]
    [ChartedSpace HP P] [IsManifold IP ∞ P]
    [ENat.LEInfty (minSmoothness ℝ 3)]
    {torsor : PrincipalBundleTorsorData G B P}
    {bundle : TopologicalPrincipalBundleData torsor}
    (smoothBundle : SmoothPrincipalBundleData IB IG IP torsor bundle)
    (chart : PrincipalBundleLocalTrivialization torsor)
    (chart_mem : chart ∈ bundle.trivializationAtlas)

private def principalChartPartialDiffeomorph
    (smoothBundle : SmoothPrincipalBundleData IB IG IP torsor bundle)
    (chart_mem : chart ∈ bundle.trivializationAtlas) :
    PartialDiffeomorph IP (IB.prod IG) P (B × G) ∞ where
  toPartialEquiv := chart.toPartialHomeomorph.toPartialEquiv
  open_source := chart.toPartialHomeomorph.open_source
  open_target := chart.toPartialHomeomorph.open_target
  contMDiffOn_toFun := smoothBundle.trivialization_smooth chart chart_mem
  contMDiffOn_invFun := smoothBundle.inverse_trivialization_smooth chart chart_mem

omit [FiniteDimensional ℝ EG] [FiniteDimensional ℝ EB] [FiniteDimensional ℝ EP]
    [ENat.LEInfty (minSmoothness ℝ 3)] in
private theorem partial_mfderivWithin_isInvertible
    (smoothBundle : SmoothPrincipalBundleData IB IG IP torsor bundle)
    (chart_mem : chart ∈ bundle.trivializationAtlas)
    {q : P} (hq : q ∈ chart.toPartialHomeomorph.source) :
    ContinuousLinearMap.IsInvertible
      (mfderivWithin IP (IB.prod IG) chart.toPartialHomeomorph
        chart.toPartialHomeomorph.source q) := by
  let phi := principalChartPartialDiffeomorph (IG := IG) (IB := IB) (IP := IP)
    (chart := chart) smoothBundle chart_mem
  have hl := PartialDiffeomorph.isLocalDiffeomorphAt IP (IB.prod IG) ∞ phi hq
  change IsLocalDiffeomorphAt IP (IB.prod IG) ∞ chart.toPartialHomeomorph q at hl
  let L := hl.mfderivToContinuousLinearEquiv (by simp)
  have hL : (L : TangentSpace IP q →L[ℝ]
      TangentSpace (IB.prod IG) (chart.toPartialHomeomorph q)) =
      mfderiv IP (IB.prod IG) chart.toPartialHomeomorph q := by
    exact hl.mfderivToContinuousLinearEquiv_coe (by simp)
  refine ⟨L, ?_⟩
  rw [hL]
  exact (mfderivWithin_eq_mfderiv
    (chart.toPartialHomeomorph.open_source.uniqueMDiffWithinAt hq)
    (((smoothBundle.trivialization_smooth chart chart_mem).mdifferentiableOn
      (by simp) q hq).mdifferentiableAt
        (chart.toPartialHomeomorph.open_source.mem_nhds hq))).symm

private def productVerticalField (X : GroupLieAlgebra IG G)
    (z : B × G) : TangentSpace (IB.prod IG) z :=
  (0, mulInvariantVectorField X z.2)

/-- The exact total-space source obtained by pulling back the product field's centered base-chart
source through the designated principal partial trivialization. -/
def adaptedTotalSource (b : B) : Set P :=
  chart.toPartialHomeomorph.source ∩
    chart.toPartialHomeomorph ⁻¹' ((extChartAt IB b).source ×ˢ (Set.univ : Set G))

/-- Transport the orbit-adapted product field back through the designated principal partial
trivialization. -/
def adaptedTotalField (b : B) (u : TangentSpace IB b)
    (w : GroupLieAlgebra IG G) (q : P) : TangentSpace IP q :=
  VectorField.mpullbackWithin IP (IB.prod IG) chart.toPartialHomeomorph
    (adaptedProductField IG IB b u 1 w) chart.toPartialHomeomorph.source q

omit [FiniteDimensional ℝ EB] [IsTopologicalGroup G] [IsManifold IB ∞ B]
    [ENat.LEInfty (minSmoothness ℝ 3)] in
/-- The exact total source is open. -/
theorem isOpen_adaptedTotalSource (b : B) :
    IsOpen (adaptedTotalSource (IB := IB) chart b) :=
  chart.toPartialHomeomorph.isOpen_inter_preimage
    (isOpen_adaptedProductDomain IB b)

omit [FiniteDimensional ℝ EG] [FiniteDimensional ℝ EB] [FiniteDimensional ℝ EP]
    [ENat.LEInfty (minSmoothness ℝ 3)] in
private theorem partial_mfderivWithin_inverse_eq
    (smoothBundle : SmoothPrincipalBundleData IB IG IP torsor bundle)
    (chart_mem : chart ∈ bundle.trivializationAtlas)
    {q : P} (hq : q ∈ chart.toPartialHomeomorph.source) :
    (mfderivWithin IP (IB.prod IG) chart.toPartialHomeomorph
      chart.toPartialHomeomorph.source q).inverse =
      mfderivWithin (IB.prod IG) IP chart.toPartialHomeomorph.symm
        chart.toPartialHomeomorph.target (chart.toPartialHomeomorph q) := by
  let f := chart.toPartialHomeomorph
  let g := chart.toPartialHomeomorph.symm
  have hf : MDifferentiableWithinAt IP (IB.prod IG) f f.source q :=
    ((SmoothPrincipalBundleData.trivialization_smooth smoothBundle chart chart_mem) q hq)
      |>.mdifferentiableWithinAt (by simp)
  have hg : MDifferentiableWithinAt (IB.prod IG) IP g g.source (f q) :=
    ((SmoothPrincipalBundleData.inverse_trivialization_smooth smoothBundle chart chart_mem)
      (f q) (f.map_source hq)) |>.mdifferentiableWithinAt (by simp)
  have hgf : g (f q) = q := f.left_inv hq
  have hf' : MDifferentiableWithinAt IP (IB.prod IG) f f.source (g (f q)) := by
    rw [hgf]
    exact hf
  have hleft := mfderivWithin_comp (I := IB.prod IG) (I' := IP) (I'' := IB.prod IG)
    (f q) hf' hg (by
      intro z hz
      exact g.map_source hz)
    (f.open_target.uniqueMDiffWithinAt (f.map_source hq))
  rw [hgf] at hleft
  have hleftfun : f ∘ g =ᶠ[Filter.principal f.target] id := by
    change {z | (f ∘ g) z = id z} ∈ Filter.principal f.target
    rw [Filter.mem_principal]
    intro z hz
    exact f.right_inv hz
  have hleftderiv : mfderivWithin (IB.prod IG) (IB.prod IG) (f ∘ g)
      f.target (f q) = ContinuousLinearMap.id ℝ (TangentSpace (IB.prod IG) (f q)) := by
    rw [mfderivWithin_congr (fun z hz => hleftfun hz) (hleftfun (f.map_source hq))]
    exact mfderivWithin_id (f.open_target.uniqueMDiffWithinAt (f.map_source hq))
  have hright := mfderivWithin_comp (I := IP) (I' := IB.prod IG) (I'' := IP)
    q hg hf (by
      intro z hz
      exact f.map_source hz)
    (f.open_source.uniqueMDiffWithinAt hq)
  have hrightfun : g ∘ f =ᶠ[Filter.principal f.source] id := by
    change {z | (g ∘ f) z = id z} ∈ Filter.principal f.source
    rw [Filter.mem_principal]
    intro z hz
    exact f.left_inv hz
  have hrightderiv : mfderivWithin IP IP (g ∘ f) f.source q =
      ContinuousLinearMap.id ℝ (TangentSpace IP q) := by
    rw [mfderivWithin_congr (fun z hz => hrightfun hz) (hrightfun hq)]
    exact mfderivWithin_id (f.open_source.uniqueMDiffWithinAt hq)
  apply ContinuousLinearMap.inverse_eq
  · exact hleft.symm.trans hleftderiv
  · exact hright.symm.trans hrightderiv

omit [FiniteDimensional ℝ EG] [FiniteDimensional ℝ EB] [FiniteDimensional ℝ EP]
    [ENat.LEInfty (minSmoothness ℝ 3)] in
private theorem partial_mfderivWithin_inverse_apply_self
    (smoothBundle : SmoothPrincipalBundleData IB IG IP torsor bundle)
    (chart_mem : chart ∈ bundle.trivializationAtlas)
    {q : P} (hq : q ∈ chart.toPartialHomeomorph.source) (v : TangentSpace IP q) :
    (mfderivWithin IP (IB.prod IG) chart.toPartialHomeomorph
      chart.toPartialHomeomorph.source q).inverse
        (mfderivWithin IP (IB.prod IG) chart.toPartialHomeomorph
          chart.toPartialHomeomorph.source q v) = v := by
  let f := chart.toPartialHomeomorph
  let g := chart.toPartialHomeomorph.symm
  rw [partial_mfderivWithin_inverse_eq (IG := IG) (IB := IB) (IP := IP)
    (chart := chart) smoothBundle chart_mem hq]
  have hf : MDifferentiableWithinAt IP (IB.prod IG) f f.source q :=
    ((SmoothPrincipalBundleData.trivialization_smooth smoothBundle chart chart_mem) q hq)
      |>.mdifferentiableWithinAt (by simp)
  have hg : MDifferentiableWithinAt (IB.prod IG) IP g g.source (f q) :=
    ((SmoothPrincipalBundleData.inverse_trivialization_smooth smoothBundle chart chart_mem)
      (f q) (f.map_source hq)) |>.mdifferentiableWithinAt (by simp)
  have hchain := mfderivWithin_comp (I := IP) (I' := IB.prod IG) (I'' := IP)
    q hg hf (by intro z hz; exact f.map_source hz)
    (f.open_source.uniqueMDiffWithinAt hq)
  have hrightfun : g ∘ f =ᶠ[Filter.principal f.source] id := by
    change {z | (g ∘ f) z = id z} ∈ Filter.principal f.source
    rw [Filter.mem_principal]
    intro z hz
    exact f.left_inv hz
  have hcomp : mfderivWithin IP IP (g ∘ f) f.source q =
      ContinuousLinearMap.id ℝ (TangentSpace IP q) := by
    rw [mfderivWithin_congr (fun z hz => hrightfun hz) (hrightfun hq)]
    exact mfderivWithin_id (f.open_source.uniqueMDiffWithinAt hq)
  have happ := congrArg (fun L => L v) (hchain.symm.trans hcomp)
  exact happ

omit [FiniteDimensional ℝ EG] [FiniteDimensional ℝ EP] in
/-- The transported field is `C∞` on the exact open source obtained from the designated principal
partial trivialization and the centered base chart. -/
theorem adaptedTotalField_isSmoothOn
    (smoothBundle : SmoothPrincipalBundleData IB IG IP torsor bundle)
    (chart_mem : chart ∈ bundle.trivializationAtlas)
    (b : B) (u : TangentSpace IB b) (w : GroupLieAlgebra IG G) :
    ManifoldTangentField.IsSmoothOn IP
      (adaptedTotalSource (IB := IB) chart b)
      (adaptedTotalField IG IB IP chart b u w) := by
  let D : Set (B × G) := (extChartAt IB b).source ×ˢ (Set.univ : Set G)
  let F : (z : B × G) → TangentSpace (IB.prod IG) z :=
    adaptedProductField IG IB b u 1 w
  have hF : ContMDiffOn (IB.prod IG) (IB.prod IG).tangent ∞
      (fun z => (⟨z, F z⟩ : TangentBundle (IB.prod IG) (B × G))) D :=
    adaptedProductField_isSmoothOn IG IB b u 1 w
  have hInv :=
    (SmoothPrincipalBundleData.inverse_trivialization_smooth smoothBundle chart chart_mem)
      |>.contMDiffOn_tangentMapWithin (m := ∞) (by simp)
        chart.toPartialHomeomorph.open_target.uniqueMDiffOn
  have hmaps : Set.MapsTo
      (fun z => (⟨z, F z⟩ : TangentBundle (IB.prod IG) (B × G)))
      (D ∩ chart.toPartialHomeomorph.target)
      (Bundle.TotalSpace.proj ⁻¹' chart.toPartialHomeomorph.target) := by
    intro z hz
    exact hz.2
  have hout : ContMDiffOn (IB.prod IG) IP.tangent ∞
      (fun z => tangentMapWithin (IB.prod IG) IP chart.toPartialHomeomorph.symm
        chart.toPartialHomeomorph.target
        (⟨z, F z⟩ : TangentBundle (IB.prod IG) (B × G)))
      (D ∩ chart.toPartialHomeomorph.target) :=
    hInv.comp (hF.mono inter_subset_left) hmaps
  have hchartmaps : Set.MapsTo chart.toPartialHomeomorph
      (adaptedTotalSource (IB := IB) chart b)
      (D ∩ chart.toPartialHomeomorph.target) := by
    intro q hq
    exact ⟨hq.2, chart.toPartialHomeomorph.map_source hq.1⟩
  have hcomp := hout.comp
    ((SmoothPrincipalBundleData.trivialization_smooth smoothBundle chart chart_mem).mono
      inter_subset_left) hchartmaps
  refine hcomp.congr ?_
  intro q hq
  apply Bundle.TotalSpace.ext
  · exact (chart.toPartialHomeomorph.left_inv hq.1).symm
  · change adaptedTotalField IG IB IP chart b u w q ≍
      mfderivWithin (IB.prod IG) IP chart.toPartialHomeomorph.symm
        chart.toPartialHomeomorph.target (chart.toPartialHomeomorph q)
          (F (chart.toPartialHomeomorph q))
    rw [adaptedTotalField, VectorField.mpullbackWithin_apply,
      partial_mfderivWithin_inverse_eq (IG := IG) (IB := IB) (IP := IP)
        (chart := chart) smoothBundle chart_mem hq.1]
    rfl

omit [FiniteDimensional ℝ EG] [FiniteDimensional ℝ EB] [IsTopologicalGroup G] in
private theorem productVerticalField_isSmoothOn
    (X : GroupLieAlgebra IG G) (s : Set (B × G)) :
    ManifoldTangentField.IsSmoothOn (IB.prod IG) s (productVerticalField IG IB X) := by
  let first : B × G → TangentBundle IB B := fun z => ⟨z.1, 0⟩
  have hfirst : ContMDiff (IB.prod IG) IB.tangent ∞ first :=
    (contMDiff_zeroSection ℝ (TangentSpace IB)).comp contMDiff_fst
  let second : B × G → TangentBundle IG G := fun z =>
    ⟨z.2, mulInvariantVectorField X z.2⟩
  have hsecond : ContMDiff (IB.prod IG) IG.tangent ∞ second :=
    (contMDiff_mulInvariantVectorField_top IG X).comp contMDiff_snd
  have hpair : ContMDiff (IB.prod IG) (IB.tangent.prod IG.tangent) ∞
      (fun z => (first z, second z)) := hfirst.prodMk hsecond
  have htotal := contMDiff_equivTangentBundleProd_symm.comp hpair
  intro z hz
  convert (htotal z).contMDiffWithinAt using 1
  all_goals rfl

omit [FiniteDimensional ℝ EG] [FiniteDimensional ℝ EB] [FiniteDimensional ℝ EP]
    [ENat.LEInfty (minSmoothness ℝ 3)] in
private theorem principalFundamentalVectorField_eq_productPullback
    (smoothBundle : SmoothPrincipalBundleData IB IG IP torsor bundle)
    (chart_mem : chart ∈ bundle.trivializationAtlas)
    (X : GroupLieAlgebra IG G) {q : P}
    (hq : q ∈ chart.toPartialHomeomorph.source) :
    principalFundamentalVectorField (smoothBundle := smoothBundle) X q =
      VectorField.mpullbackWithin IP (IB.prod IG) chart.toPartialHomeomorph
        (productVerticalField IG IB X) chart.toPartialHomeomorph.source q := by
  let e := chart.toPartialHomeomorph
  let orbit : G → P := principalOrbitMap torsor q
  let K : G → B × G := fun g => ((e q).1, (e q).2 * g)
  have horbit : ContMDiff IG IP ∞ orbit := principalOrbitMap_smooth smoothBundle q
  have heAt : MDifferentiableAt IP (IB.prod IG) e q :=
    (((smoothBundle.trivialization_smooth chart chart_mem) q hq).mdifferentiableWithinAt
      (by simp)).mdifferentiableAt (e.open_source.mem_nhds hq)
  have horbitOne : orbit (1 : G) = q := torsor.right_one q
  have heAt' : MDifferentiableAt IP (IB.prod IG) e (orbit (1 : G)) := by
    rw [horbitOne]
    exact heAt
  have hchain := mfderiv_comp (I := IG) (I' := IP) (I'' := IB.prod IG)
    (f := orbit) (g := e) (1 : G) heAt' (horbit.mdifferentiableAt (by simp))
  have hfun : e ∘ orbit = K := by
    funext g
    exact chart.rightAction_coordinate q hq g
  rw [mfderiv_congr (x := (1 : G)) hfun] at hchain
  rw [horbitOne] at hchain
  let left : G → G := fun g => (e q).2 * g
  let embed : G → B × G := fun g => ((e q).1, g)
  have hleft : ContMDiff IG IG ∞ left := contMDiff_mul_left
  have hembed : ContMDiff IG (IB.prod IG) ∞ embed := contMDiff_const.prodMk contMDiff_id
  have hKchain := mfderiv_comp (I := IG) (I' := IG) (I'' := IB.prod IG)
    (f := left) (g := embed) (1 : G) (hembed.mdifferentiableAt (by simp))
      (hleft.mdifferentiableAt (by simp))
  have hK : embed ∘ left = K := by rfl
  rw [mfderiv_congr (x := (1 : G)) hK, mfderiv_prod_right] at hKchain
  simp only [left] at hKchain
  have happ := congrArg (fun L => L X) (hchain.symm.trans hKchain)
  change mfderiv IP (IB.prod IG) e q
      (principalFundamentalVectorField (smoothBundle := smoothBundle) X q) =
    productVerticalField IG IB X (e q) at happ
  rw [VectorField.mpullbackWithin_apply]
  have hinv := partial_mfderivWithin_isInvertible (IG := IG) (IB := IB) (IP := IP)
    (chart := chart) smoothBundle chart_mem hq
  symm
  apply hinv.inverse_apply_eq.mpr
  rw [mfderivWithin_eq_mfderiv (e.open_source.uniqueMDiffWithinAt hq) heAt]
  exact happ.symm

omit [FiniteDimensional ℝ EG] [FiniteDimensional ℝ EB] [FiniteDimensional ℝ EP]
    [ENat.LEInfty (minSmoothness ℝ 3)] in
/-- The transported field obeys exact principal right-translation adaptation along the whole
orbit through a point represented by identity fiber coordinate. -/
theorem adaptedTotalField_rightTranslation
    (smoothBundle : SmoothPrincipalBundleData IB IG IP torsor bundle)
    (chart_mem : chart ∈ bundle.trivializationAtlas)
    (b : B) (p : P) (hp : p ∈ chart.toPartialHomeomorph.source)
    (hcoord : chart.toPartialHomeomorph p = (b, (1 : G)))
    (u : TangentSpace IB b) (w : GroupLieAlgebra IG G) (g : G) :
    principalRightTranslationDifferential smoothBundle p g
        (adaptedTotalField IG IB IP chart b u w p) =
      adaptedTotalField IG IB IP chart b u w (torsor.rightAction p g) := by
  let e := chart.toPartialHomeomorph
  let R : B × G → B × G := fun z => (z.1, z.2 * g)
  let F : (z : B × G) → TangentSpace (IB.prod IG) z :=
    adaptedProductField IG IB b u 1 w
  have hpg : torsor.rightAction p g ∈ e.source := chart.rightAction_mem_source hp g
  have hcoordpg : e (torsor.rightAction p g) = (b, g) := by
    rw [chart.rightAction_coordinate p hp g, hcoord]
    simp
  have hAsmooth : ContMDiff IP IP ∞ (principalRightTranslation torsor g) :=
    principalRightTranslation_smooth smoothBundle g
  have hA : MDifferentiableWithinAt IP IP (principalRightTranslation torsor g) e.source p :=
    (hAsmooth.mdifferentiableAt (by simp)).mdifferentiableWithinAt
  have he' : MDifferentiableWithinAt IP (IB.prod IG) e e.source (torsor.rightAction p g) :=
    ((smoothBundle.trivialization_smooth chart chart_mem) (torsor.rightAction p g) hpg)
      |>.mdifferentiableWithinAt (by simp)
  have hleft := mfderivWithin_comp (I := IP) (I' := IP) (I'' := IB.prod IG)
    p he' hA (by intro q hq; exact chart.rightAction_mem_source hq g)
    (e.open_source.uniqueMDiffWithinAt hp)
  have he : MDifferentiableWithinAt IP (IB.prod IG) e e.source p :=
    ((smoothBundle.trivialization_smooth chart chart_mem) p hp)
      |>.mdifferentiableWithinAt (by simp)
  have hRsmooth : ContMDiff (IB.prod IG) (IB.prod IG) ∞ R :=
    contMDiff_fst.prodMk (contMDiff_snd.mul contMDiff_const)
  have hR : MDifferentiableWithinAt (IB.prod IG) (IB.prod IG) R e.target (e p) :=
    (hRsmooth.mdifferentiableAt (by simp)).mdifferentiableWithinAt
  have hright := mfderivWithin_comp (I := IP) (I' := IB.prod IG)
    (I'' := IB.prod IG) p hR he (by
      intro q hq
      exact e.map_source hq)
    (e.open_source.uniqueMDiffWithinAt hp)
  have hfun : e ∘ (principalRightTranslation torsor g) =ᶠ[Filter.principal e.source] R ∘ e := by
    change {q | (e ∘ (principalRightTranslation torsor g)) q = (R ∘ e) q} ∈
      Filter.principal e.source
    rw [Filter.mem_principal]
    intro q hq
    change e (torsor.rightAction q g) = R (e q)
    rw [chart.rightAction_coordinate q hq g]
  have hderivEq : mfderivWithin IP (IB.prod IG)
      (e ∘ (principalRightTranslation torsor g)) e.source p =
      mfderivWithin IP (IB.prod IG) (R ∘ e) e.source p :=
    mfderivWithin_congr (fun q hq => hfun hq) (hfun hp)
  have hchains := hleft.symm.trans (hderivEq.trans hright)
  unfold principalRightTranslation at hchains
  have hproduct := adaptedProductField_rightTranslation IG IB b u 1 g w
  have hprodWithin : mfderivWithin (IB.prod IG) (IB.prod IG) R e.target (e p)
      (F (e p)) = F (R (e p)) := by
    rw [mfderivWithin_eq_mfderiv
      (e.open_target.uniqueMDiffWithinAt (e.map_source hp))
      (hRsmooth.mdifferentiableAt (by simp)), hcoord]
    exact hproduct
  have hinv := partial_mfderivWithin_isInvertible (IG := IG) (IB := IB) (IP := IP)
    (chart := chart) smoothBundle chart_mem hp
  have hinvpg := partial_mfderivWithin_isInvertible (IG := IG) (IB := IB) (IP := IP)
    (chart := chart) smoothBundle chart_mem hpg
  simp only [adaptedTotalField, VectorField.mpullbackWithin_apply]
  apply hinvpg.injective
  rw [hinvpg.self_apply_inverse]
  simp only [principalRightTranslationDifferential]
  rw [← mfderivWithin_eq_mfderiv (e.open_source.uniqueMDiffWithinAt hp)
    (hAsmooth.mdifferentiableAt (by simp))]
  unfold principalRightTranslation
  have happ := congrArg
    (fun L => L ((mfderivWithin IP (IB.prod IG) e e.source p).inverse (F (e p))))
    hchains
  change mfderivWithin IP (IB.prod IG) e e.source (torsor.rightAction p g)
      (mfderivWithin IP IP (fun q => torsor.rightAction q g) e.source p
        ((mfderivWithin IP (IB.prod IG) e e.source p).inverse (F (e p)))) =
    mfderivWithin (IB.prod IG) (IB.prod IG) R e.target (e p)
      (mfderivWithin IP (IB.prod IG) e e.source p
        ((mfderivWithin IP (IB.prod IG) e e.source p).inverse (F (e p)))) at happ
  rw [hinv.self_apply_inverse, hprodWithin] at happ
  have hRp : R (e p) = e (torsor.rightAction p g) := by
    rw [hcoord, hcoordpg]
    simp [R]
  rw [hRp] at happ
  exact happ

/-- On the exact transported open source, the adapted total field has zero intrinsic within
bracket with the principal fundamental vector field at the identity-coordinate point. -/
theorem mlieBracketWithin_principalFundamental_adaptedTotalField
    (smoothBundle : SmoothPrincipalBundleData IB IG IP torsor bundle)
    (chart_mem : chart ∈ bundle.trivializationAtlas)
    (b : B) (p : P) (hp : p ∈ chart.toPartialHomeomorph.source)
    (hcoord : chart.toPartialHomeomorph p = (b, (1 : G)))
    (u : TangentSpace IB b) (X w : GroupLieAlgebra IG G) :
    VectorField.mlieBracketWithin IP
      (principalFundamentalVectorField (smoothBundle := smoothBundle) X)
      (adaptedTotalField IG IB IP chart b u w)
      (adaptedTotalSource (IB := IB) chart b) p = 0 := by
  let e := chart.toPartialHomeomorph
  let S := e.source
  let D : Set (B × G) := (extChartAt IB b).source ×ˢ (Set.univ : Set G)
  let V : (z : B × G) → TangentSpace (IB.prod IG) z := productVerticalField IG IB X
  let W : (z : B × G) → TangentSpace (IB.prod IG) z := adaptedProductField IG IB b u 1 w
  have hD : e p ∈ D := by
    rw [hcoord]
    exact adaptedProductDomain_mem IB b (1 : G)
  have hU : p ∈ adaptedTotalSource (IB := IB) chart b := ⟨hp, hD⟩
  have hV : MDifferentiableWithinAt (IB.prod IG) (IB.prod IG).tangent
      (fun z => (⟨z, V z⟩ : TangentBundle (IB.prod IG) (B × G))) D (e p) :=
    ((productVerticalField_isSmoothOn IG IB X D) (e p) hD).mdifferentiableWithinAt
      (by simp)
  have hW : MDifferentiableWithinAt (IB.prod IG) (IB.prod IG).tangent
      (fun z => (⟨z, W z⟩ : TangentBundle (IB.prod IG) (B × G))) D (e p) :=
    ((adaptedProductField_isSmoothOn IG IB b u 1 w) (e p) hD).mdifferentiableWithinAt
      (by simp)
  have he : ContMDiffWithinAt IP (IB.prod IG) ∞ e S p :=
    (smoothBundle.trivialization_smooth chart chart_mem) p hp
  have hpre : e ⁻¹' D ∈ nhdsWithin p S := by
    apply Filter.mem_of_superset
      (mem_nhdsWithin_of_mem_nhds
        ((isOpen_adaptedTotalSource (IB := IB) chart b).mem_nhds hU))
    exact inter_subset_right
  have hclosure : p ∈ closure (interior S) := by
    rw [e.open_source.interior_eq]
    exact subset_closure hp
  have hnat := VectorField.mpullbackWithin_mlieBracketWithin
    (f := (e : P → B × G)) (V := V) (W := W) (x₀ := p)
    (s := S) (t := D) hV hW e.open_source.uniqueMDiffOn he hp
    (show minSmoothness ℝ 2 ≤ (∞ : ℕ∞ω) by
      rw [minSmoothness_of_isRCLikeNormedField]
      exact WithTop.coe_le_coe.mpr le_top)
    hpre hclosure
  have hprod : VectorField.mlieBracketWithin (IB.prod IG) V W D (e p) = 0 := by
    rw [hcoord]
    exact mlieBracketWithin_verticalFundamental_adaptedProductField_center
      IG IB b u X w
  rw [VectorField.mpullbackWithin_apply, hprod, map_zero] at hnat
  have hS : VectorField.mlieBracketWithin IP
      (principalFundamentalVectorField (smoothBundle := smoothBundle) X)
      (adaptedTotalField IG IB IP chart b u w) S p = 0 := by
    have hcongr := VectorField.mlieBracketWithin_congr'
      (I := IP) (s := S) (x := p)
      (V₁ := principalFundamentalVectorField (smoothBundle := smoothBundle) X)
      (V := VectorField.mpullbackWithin IP (IB.prod IG) e V S)
      (W₁ := adaptedTotalField IG IB IP chart b u w)
      (W := VectorField.mpullbackWithin IP (IB.prod IG) e W S)
      (fun q hq => principalFundamentalVectorField_eq_productPullback
        (IG := IG) (IB := IB) (IP := IP) (chart := chart)
        smoothBundle chart_mem X hq)
      (fun _ _ => rfl) hp
    rw [hcongr]
    exact hnat.symm
  rw [VectorField.mlieBracketWithin_of_isOpen
    (isOpen_adaptedTotalSource (IB := IB) chart b) hU,
    ← VectorField.mlieBracketWithin_of_isOpen e.open_source hp]
  exact hS

omit [FiniteDimensional ℝ EG] [FiniteDimensional ℝ EB] [FiniteDimensional ℝ EP]
    [ENat.LEInfty (minSmoothness ℝ 3)] in
/-- At a point represented by identity fiber coordinate, transporting the product field whose
prescribed product tangent is the chart derivative of `v` recovers exactly `v`. -/
theorem adaptedTotalField_self
    (smoothBundle : SmoothPrincipalBundleData IB IG IP torsor bundle)
    (chart_mem : chart ∈ bundle.trivializationAtlas)
    (b : B) (p : P) (hp : p ∈ chart.toPartialHomeomorph.source)
    (hcoord : chart.toPartialHomeomorph p = (b, (1 : G)))
    (v : TangentSpace IP p) :
    let coordinate := mfderivWithin IP (IB.prod IG) chart.toPartialHomeomorph
      chart.toPartialHomeomorph.source p v
    adaptedTotalField IG IB IP chart b coordinate.1 coordinate.2 p = v := by
  dsimp only
  rw [adaptedTotalField, VectorField.mpullbackWithin_apply, hcoord,
    adaptedProductField_self]
  exact partial_mfderivWithin_inverse_apply_self (IG := IG) (IB := IB) (IP := IP)
    (chart := chart) smoothBundle chart_mem hp v

/-- Strong compiled transport package: an arbitrary prescribed total tangent at an
identity-coordinate point extends to a field smooth on the exact transported open source, adapted
to every principal right translation along the orbit, and commuting there at the point with the
fixed principal fundamental field. -/
theorem exists_principalAdaptedTotalField
    (smoothBundle : SmoothPrincipalBundleData IB IG IP torsor bundle)
    (chart_mem : chart ∈ bundle.trivializationAtlas)
    (b : B) (p : P) (hp : p ∈ chart.toPartialHomeomorph.source)
    (hcoord : chart.toPartialHomeomorph p = (b, (1 : G)))
    (v : TangentSpace IP p) (X : GroupLieAlgebra IG G) :
    ∃ field : (q : P) → TangentSpace IP q,
      field p = v ∧
      IsOpen (adaptedTotalSource (IB := IB) chart b) ∧
      p ∈ adaptedTotalSource (IB := IB) chart b ∧
      ManifoldTangentField.IsSmoothOn IP
        (adaptedTotalSource (IB := IB) chart b) field ∧
      (∀ g : G, principalRightTranslationDifferential smoothBundle p g (field p) =
        field (torsor.rightAction p g)) ∧
      VectorField.mlieBracketWithin IP
        (principalFundamentalVectorField (smoothBundle := smoothBundle) X)
        field (adaptedTotalSource (IB := IB) chart b) p = 0 := by
  let coordinate := mfderivWithin IP (IB.prod IG) chart.toPartialHomeomorph
    chart.toPartialHomeomorph.source p v
  let field := adaptedTotalField IG IB IP chart b coordinate.1 coordinate.2
  refine ⟨field, ?_, isOpen_adaptedTotalSource (IB := IB) chart b, ?_, ?_, ?_, ?_⟩
  · exact adaptedTotalField_self (IG := IG) (IB := IB) (IP := IP) (chart := chart)
      smoothBundle chart_mem b p hp hcoord v
  · constructor
    · exact hp
    · change chart.toPartialHomeomorph p ∈
        ((extChartAt IB b).source ×ˢ (Set.univ : Set G))
      rw [hcoord]
      exact adaptedProductDomain_mem IB b (1 : G)
  · exact adaptedTotalField_isSmoothOn (IG := IG) (IB := IB) (IP := IP)
      (chart := chart) smoothBundle chart_mem b coordinate.1 coordinate.2
  · intro g
    exact adaptedTotalField_rightTranslation (IG := IG) (IB := IB) (IP := IP)
      (chart := chart) smoothBundle chart_mem b p hp hcoord coordinate.1 coordinate.2 g
  · exact mlieBracketWithin_principalFundamental_adaptedTotalField
      (IG := IG) (IB := IB) (IP := IP) (chart := chart)
      smoothBundle chart_mem b p hp hcoord coordinate.1 X coordinate.2

end
end YangMills.Geometry.PrincipalOrbitAdapted

