/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Geometry.AdjointBundleGaugeHomeomorph
import YangMills.Geometry.AdjointBundleSmoothAtlas
import YangMills.Geometry.SmoothGaugeAssociatedFunction
import Mathlib.Geometry.Manifold.Diffeomorph

/-!
# Smooth gauge automorphism of the adjoint quotient

In every designated model-bundle trivialization, the covariant quotient action is exactly
`(b,X) ↦ (b, Ad(g_ϕ(s(b)))X)`. Smoothness of the local associated function and joint adjoint
evaluation derive the local formula's smoothness. Exact compatibility between the first-stage bundle
trivializations and the named quotient atlas then globalizes forward and inverse smoothness,
packaging the established quotient homeomorphism as a `C∞` diffeomorphism.

Together with the separately proved fixed-fiber continuous-linear equivalences, this supplies the
smooth and fiber-linear content of the gauge action. No scalar/action/observable invariance follows
automatically.
-/

namespace YangMills.Geometry

open Set
open scoped Manifold ContDiff
open YangMills.Mathematics

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
    {IB : ModelWithCorners ℝ EB HB}
    {IG : ModelWithCorners ℝ EG HG}
    {IP : ModelWithCorners ℝ EP HP}
    [ChartedSpace HG G] [LieGroup IG ∞ G]
    [ChartedSpace HB B] [IsManifold IB ∞ B]
    [ChartedSpace HP P] [IsManifold IP ∞ P]
    {torsor : PrincipalBundleTorsorData G B P}
    {bundle : TopologicalPrincipalBundleData torsor}
    {smoothBundle : SmoothPrincipalBundleData IB IG IP torsor bundle}

namespace SmoothGaugeTransformation

set_option pp.universes false in
set_option pp.all false in
 theorem inducedAdjointBundleAction_modelBundleTrivialization
    (gauge : SmoothGaugeTransformation smoothBundle)
    (chart : PrincipalBundleLocalTrivialization torsor)
    (z : B × EG)
    (hz : z ∈ (AdjointBundle.modelBundleTrivialization (I := IG) bundle chart).target) :
    AdjointBundle.modelBundleTrivialization (I := IG) bundle chart
        (gauge.inducedAdjointBundleAction
          ((AdjointBundle.modelBundleTrivialization (I := IG) bundle chart).toOpenPartialHomeomorph.symm z)) =
      (z.1, lieGroupAdjointCoordinates (I := IG)
        (gauge.associatedGaugeFunction (principalBundleLocalSection chart z.1)) z.2) := by
  let coordinates := groupLieAlgebraModelEquiv (G := G) IG
  let X : GroupLieAlgebra IG G := coordinates.symm z.2
  let p : P := principalBundleLocalSection chart z.1
  have hb : z.1 ∈ chart.baseSet :=
    (AdjointBundle.modelBundleTrivialization (I := IG) bundle chart).mem_target.mp hz
  have hp : p ∈ chart.toPartialHomeomorph.source := by
    rw [chart.source_eq]
    change torsor.projection p ∈ chart.baseSet
    rw [principalBundleLocalSection_projection chart hb]
    exact hb
  have hgp : gauge p ∈ chart.toPartialHomeomorph.source := by
    rw [chart.source_eq]
    change torsor.projection (gauge p) ∈ chart.baseSet
    rw [gauge.preserves_projection, principalBundleLocalSection_projection chart hb]
    exact hb
  rw [AdjointBundle.modelBundleTrivialization_symm_apply]
  change AdjointBundle.modelBundleTrivialization (I := IG) bundle chart
    (gauge.inducedAdjointBundleAction (AdjointBundle.mk torsor p X)) = _
  rw [gauge.inducedAdjointBundleAction_mk,
    AdjointBundle.modelBundleTrivialization_apply,
    AdjointBundle.localCoordinate_mk chart (gauge p) X hgp]
  apply Prod.ext
  · rw [gauge.preserves_projection, principalBundleLocalSection_projection chart hb]
  · rw [gauge.associatedGaugeFunction_localSection_eq_secondCoordinate chart hb]
    rfl

/-- The exact model-trivialization formula is smooth on its natural target. -/
theorem inducedAdjointBundleAction_modelFormula_contMDiffOn
    (gauge : SmoothGaugeTransformation smoothBundle)
    (chart : PrincipalBundleLocalTrivialization torsor)
    (chart_mem : chart ∈ bundle.trivializationAtlas) :
    ContMDiffOn (IB.prod 𝓘(ℝ, EG)) (IB.prod 𝓘(ℝ, EG)) ∞
      (fun z : B × EG =>
        (z.1, lieGroupAdjointCoordinates (I := IG)
          (gauge.associatedGaugeFunction (principalBundleLocalSection chart z.1)) z.2))
      (AdjointBundle.modelBundleTrivialization (I := IG) bundle chart).target := by
  let e := AdjointBundle.modelBundleTrivialization (I := IG) bundle chart
  let localGauge : B → G := fun b =>
    gauge.associatedGaugeFunction (principalBundleLocalSection chart b)
  have hlocal : ContMDiffOn IB IG ∞ localGauge chart.baseSet := by
    simpa [localGauge] using
      gauge.associatedGaugeFunction_localSection_contMDiffOn chart chart_mem
  have htarget : e.target = chart.baseSet ×ˢ (Set.univ : Set EG) := e.target_eq
  have hlocalComp : ContMDiffOn (IB.prod 𝓘(ℝ, EG)) IG ∞
      (fun z : B × EG => localGauge z.1) e.target := by
    apply hlocal.comp contMDiffOn_fst
    rw [htarget]
    exact prod_subset_preimage_fst _ _
  have hinput : ContMDiffOn (IB.prod 𝓘(ℝ, EG)) (IG.prod 𝓘(ℝ, EG)) ∞
      (fun z : B × EG => (localGauge z.1, z.2)) e.target :=
    hlocalComp.prodMk contMDiffOn_snd
  have hfiber : ContMDiffOn (IB.prod 𝓘(ℝ, EG)) 𝓘(ℝ, EG) ∞
      (fun z : B × EG => lieGroupAdjointCoordinates (I := IG) (localGauge z.1) z.2)
      e.target := by
    simpa [Function.comp_def] using
      (lieGroupAdjointCoordinates_action_contMDiff (I := IG) (G := G)).comp_contMDiffOn hinput
  exact contMDiffOn_fst.prodMk hfiber

end SmoothGaugeTransformation
end
end YangMills.Geometry

namespace YangMills.Geometry
open Set
open scoped Manifold ContDiff
open YangMills.Mathematics
noncomputable section

universe uEG uHG uEB uHB uEP uHP uG uB uP
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
    {IB : ModelWithCorners ℝ EB HB} {IG : ModelWithCorners ℝ EG HG}
    {IP : ModelWithCorners ℝ EP HP}
    [ChartedSpace HG G] [LieGroup IG ∞ G]
    [ChartedSpace HB B] [IsManifold IB ∞ B]
    [ChartedSpace HP P] [IsManifold IP ∞ P]
    {torsor : PrincipalBundleTorsorData G B P}
    {bundle : TopologicalPrincipalBundleData torsor}
    {smoothBundle : SmoothPrincipalBundleData IB IG IP torsor bundle}

set_option pp.universes false in
set_option pp.all false in
theorem selectedModelBundleTrivialization_contMDiffAt
    (smoothBundle : SmoothPrincipalBundleData IB IG IP torsor bundle)
    (x : AdjointBundle (I := IG) torsor) :
    letI : ChartedSpace (ModelProd HB EG) (AdjointBundle (I := IG) torsor) :=
      AdjointBundle.modelChartedSpace (IG := IG) bundle
    letI : IsManifold (IB.prod 𝓘(ℝ, EG)) ∞ (AdjointBundle (I := IG) torsor) :=
      AdjointBundle.modelIsManifold smoothBundle
    let e := AdjointBundle.modelBundleTrivialization (I := IG) bundle
      (bundle.trivializationAt (AdjointBundle.projection torsor x))
    ContMDiffAt (IB.prod 𝓘(ℝ, EG)) (IB.prod 𝓘(ℝ, EG)) ∞ e x := by
  letI : ChartedSpace (ModelProd HB EG) (AdjointBundle (I := IG) torsor) :=
    AdjointBundle.modelChartedSpace (IG := IG) bundle
  letI : IsManifold (IB.prod 𝓘(ℝ, EG)) ∞ (AdjointBundle (I := IG) torsor) :=
    AdjointBundle.modelIsManifold smoothBundle
  let e := AdjointBundle.modelBundleTrivialization (I := IG) bundle
    (bundle.trivializationAt (AdjointBundle.projection torsor x))
  let q := chartAt (ModelProd HB EG) x
  let c := chartAt (ModelProd HB EG) (e x)
  have hx : x ∈ q.source := mem_chart_source (ModelProd HB EG) x
  have hq : ContMDiffAt (IB.prod 𝓘(ℝ, EG)) (IB.prod 𝓘(ℝ, EG)) ∞ q x :=
    (contMDiffOn_chart (I := IB.prod 𝓘(ℝ, EG))).contMDiffAt
      (q.open_source.mem_nhds hx)
  have hcMem : q x ∈ c.target := by
    change c (e x) ∈ c.target
    exact c.map_source (mem_chart_source (ModelProd HB EG) (e x))
  have hc : ContMDiffAt (IB.prod 𝓘(ℝ, EG)) (IB.prod 𝓘(ℝ, EG)) ∞ c.symm (q x) :=
    (contMDiffOn_chart_symm (I := IB.prod 𝓘(ℝ, EG))).contMDiffAt
      (c.open_target.mem_nhds hcMem)
  have hcomp := hc.comp x hq
  apply hcomp.congr_of_eventuallyEq
  filter_upwards [q.open_source.mem_nhds hx] with y hy
  change e y = c.symm (q y)
  change y ∈ (e.toOpenPartialHomeomorph ≫ₕ c).source at hy
  rw [OpenPartialHomeomorph.trans_source] at hy
  change e y = c.symm (c (e y))
  exact (c.left_inv hy.2).symm

end
end YangMills.Geometry

namespace YangMills.Geometry
open Set
open scoped Manifold ContDiff
noncomputable section
universe uEG uHG uEB uHB uEP uHP uG uB uP
variable
    {EG : Type uEG} {HG : Type uHG} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
    [TopologicalSpace HG] {EB : Type uEB} {HB : Type uHB} [NormedAddCommGroup EB]
    [NormedSpace ℝ EB] [TopologicalSpace HB] {EP : Type uEP} {HP : Type uHP}
    [NormedAddCommGroup EP] [NormedSpace ℝ EP] [TopologicalSpace HP]
    {G : Type uG} {B : Type uB} {P : Type uP} [Group G] [TopologicalSpace G]
    [TopologicalSpace B] [TopologicalSpace P] [IsTopologicalGroup G]
    {IB : ModelWithCorners ℝ EB HB} {IG : ModelWithCorners ℝ EG HG}
    {IP : ModelWithCorners ℝ EP HP} [ChartedSpace HG G] [LieGroup IG ∞ G]
    [ChartedSpace HB B] [IsManifold IB ∞ B] [ChartedSpace HP P] [IsManifold IP ∞ P]
    {torsor : PrincipalBundleTorsorData G B P} {bundle : TopologicalPrincipalBundleData torsor}

set_option pp.universes false in
set_option pp.all false in
theorem selectedModelBundleTrivialization_symm_contMDiffAt
    (smoothBundle : SmoothPrincipalBundleData IB IG IP torsor bundle)
    (x : AdjointBundle (I := IG) torsor)
    (w : B × EG)
    (hw : w ∈ (AdjointBundle.modelBundleTrivialization (I := IG) bundle
      (bundle.trivializationAt (AdjointBundle.projection torsor x))).target)
    (hbase : w.1 = (AdjointBundle.modelBundleTrivialization (I := IG) bundle
      (bundle.trivializationAt (AdjointBundle.projection torsor x)) x).1) :
    letI : ChartedSpace (ModelProd HB EG) (AdjointBundle (I := IG) torsor) :=
      AdjointBundle.modelChartedSpace (IG := IG) bundle
    letI : IsManifold (IB.prod 𝓘(ℝ, EG)) ∞ (AdjointBundle (I := IG) torsor) :=
      AdjointBundle.modelIsManifold smoothBundle
    ContMDiffAt (IB.prod 𝓘(ℝ, EG)) (IB.prod 𝓘(ℝ, EG)) ∞
      (AdjointBundle.modelBundleTrivialization (I := IG) bundle
        (bundle.trivializationAt (AdjointBundle.projection torsor x))).toOpenPartialHomeomorph.symm w := by
  letI : ChartedSpace (ModelProd HB EG) (AdjointBundle (I := IG) torsor) :=
    AdjointBundle.modelChartedSpace (IG := IG) bundle
  letI : IsManifold (IB.prod 𝓘(ℝ, EG)) ∞ (AdjointBundle (I := IG) torsor) :=
    AdjointBundle.modelIsManifold smoothBundle
  let e := AdjointBundle.modelBundleTrivialization (I := IG) bundle
    (bundle.trivializationAt (AdjointBundle.projection torsor x))
  let q := chartAt (ModelProd HB EG) x
  let c := chartAt (ModelProd HB EG) (e x)
  have hx : x ∈ e.source := AdjointBundle.mem_source_bundleTrivializationAt bundle x
  have hwc : w ∈ c.source := by
    change w.1 ∈ (chartAt HB (e x).1).source ∧ w.2 ∈ Set.univ
    exact ⟨hbase ▸ mem_chart_source HB (e x).1, Set.mem_univ _⟩
  have hsource : e.toOpenPartialHomeomorph.symm w ∈ q.source := by
    change e.toOpenPartialHomeomorph.symm w ∈
      (e.toOpenPartialHomeomorph ≫ₕ c).source
    rw [OpenPartialHomeomorph.trans_source]
    refine ⟨e.toOpenPartialHomeomorph.map_target hw, ?_⟩
    change e (e.toOpenPartialHomeomorph.symm w) ∈ c.source
    rw [e.apply_symm_apply hw]
    exact hwc
  have hqw : c w ∈ q.target := by
    have hmap := q.map_source hsource
    change c (e (e.toOpenPartialHomeomorph.symm w)) ∈ q.target at hmap
    have heq : e (e.toOpenPartialHomeomorph.symm w) = w :=
      e.apply_symm_apply hw
    rw [heq] at hmap
    exact hmap
  have hc : ContMDiffAt (IB.prod 𝓘(ℝ, EG)) (IB.prod 𝓘(ℝ, EG)) ∞ c w :=
    (contMDiffOn_chart (I := IB.prod 𝓘(ℝ, EG))).contMDiffAt
      (c.open_source.mem_nhds hwc)
  have hq : ContMDiffAt (IB.prod 𝓘(ℝ, EG)) (IB.prod 𝓘(ℝ, EG)) ∞ q.symm (c w) :=
    (contMDiffOn_chart_symm (I := IB.prod 𝓘(ℝ, EG))).contMDiffAt
      (q.open_target.mem_nhds hqw)
  have hcomp := hq.comp w hc
  apply hcomp.congr_of_eventuallyEq
  filter_upwards [c.open_source.mem_nhds hwc] with y hy
  change e.toOpenPartialHomeomorph.symm y = q.symm (c y)
  change e.toOpenPartialHomeomorph.symm y =
    e.toOpenPartialHomeomorph.symm (c.symm (c y))
  rw [c.left_inv hy]

end
end YangMills.Geometry

namespace YangMills.Geometry
open Set
open scoped Manifold ContDiff
open YangMills.Mathematics
noncomputable section
universe uEG uHG uEB uHB uEP uHP uG uB uP
variable
    {EG : Type uEG} {HG : Type uHG} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
    [TopologicalSpace HG] {EB : Type uEB} {HB : Type uHB} [NormedAddCommGroup EB]
    [NormedSpace ℝ EB] [TopologicalSpace HB] {EP : Type uEP} {HP : Type uHP}
    [NormedAddCommGroup EP] [NormedSpace ℝ EP] [TopologicalSpace HP]
    {G : Type uG} {B : Type uB} {P : Type uP} [Group G] [TopologicalSpace G]
    [TopologicalSpace B] [TopologicalSpace P] [IsTopologicalGroup G]
    {IB : ModelWithCorners ℝ EB HB} {IG : ModelWithCorners ℝ EG HG}
    {IP : ModelWithCorners ℝ EP HP} [ChartedSpace HG G] [LieGroup IG ∞ G]
    [ChartedSpace HB B] [IsManifold IB ∞ B] [ChartedSpace HP P] [IsManifold IP ∞ P]
    {torsor : PrincipalBundleTorsorData G B P} {bundle : TopologicalPrincipalBundleData torsor}
    {smoothBundle : SmoothPrincipalBundleData IB IG IP torsor bundle}

namespace SmoothGaugeTransformation

set_option pp.universes false in
set_option pp.all false in
theorem inducedAdjointBundleAction_contMDiff
    (gauge : SmoothGaugeTransformation smoothBundle) :
    letI : ChartedSpace (ModelProd HB EG) (AdjointBundle (I := IG) torsor) :=
      AdjointBundle.modelChartedSpace (IG := IG) bundle
    letI : IsManifold (IB.prod 𝓘(ℝ, EG)) ∞ (AdjointBundle (I := IG) torsor) :=
      AdjointBundle.modelIsManifold smoothBundle
    ContMDiff (IB.prod 𝓘(ℝ, EG)) (IB.prod 𝓘(ℝ, EG)) ∞
      gauge.inducedAdjointBundleAction := by
  letI : ChartedSpace (ModelProd HB EG) (AdjointBundle (I := IG) torsor) :=
    AdjointBundle.modelChartedSpace (IG := IG) bundle
  letI : IsManifold (IB.prod 𝓘(ℝ, EG)) ∞ (AdjointBundle (I := IG) torsor) :=
    AdjointBundle.modelIsManifold smoothBundle
  intro x
  let chart := bundle.trivializationAt (AdjointBundle.projection torsor x)
  let e := AdjointBundle.modelBundleTrivialization (I := IG) bundle chart
  let F : B × EG → B × EG := fun z =>
    (z.1, lieGroupAdjointCoordinates (I := IG)
      (gauge.associatedGaugeFunction (principalBundleLocalSection chart z.1)) z.2)
  let w := e x
  have hchart : chart ∈ bundle.trivializationAtlas :=
    bundle.trivializationAt_mem_atlas (AdjointBundle.projection torsor x)
  have hx : x ∈ e.source := AdjointBundle.mem_source_bundleTrivializationAt bundle x
  have hw : w ∈ e.target := e.toOpenPartialHomeomorph.map_source hx
  have hFw : F w ∈ e.target := by
    apply e.mem_target.mpr
    exact e.mem_target.mp hw
  have hbase : (F w).1 = w.1 := rfl
  have he : ContMDiffAt (IB.prod 𝓘(ℝ, EG)) (IB.prod 𝓘(ℝ, EG)) ∞ e x :=
    selectedModelBundleTrivialization_contMDiffAt smoothBundle x
  have hF : ContMDiffAt (IB.prod 𝓘(ℝ, EG)) (IB.prod 𝓘(ℝ, EG)) ∞ F w := by
    exact (gauge.inducedAdjointBundleAction_modelFormula_contMDiffOn chart hchart).contMDiffAt
      (e.open_target.mem_nhds hw)
  have heSymm : ContMDiffAt (IB.prod 𝓘(ℝ, EG)) (IB.prod 𝓘(ℝ, EG)) ∞
      e.toOpenPartialHomeomorph.symm (F w) :=
    selectedModelBundleTrivialization_symm_contMDiffAt smoothBundle x (F w) hFw hbase
  have hcomp := heSymm.comp x (hF.comp x he)
  apply hcomp.congr_of_eventuallyEq
  filter_upwards [e.open_source.mem_nhds hx] with y hy
  change gauge.inducedAdjointBundleAction y = e.toOpenPartialHomeomorph.symm (F (e y))
  have hey : e y ∈ e.target := e.toOpenPartialHomeomorph.map_source hy
  have hformula := gauge.inducedAdjointBundleAction_modelBundleTrivialization chart (e y) hey
  change e (gauge.inducedAdjointBundleAction (e.toOpenPartialHomeomorph.symm (e y))) =
    F (e y) at hformula
  have heinv := e.toOpenPartialHomeomorph.left_inv hy
  change e.toOpenPartialHomeomorph.symm (e y) = y at heinv
  rw [heinv] at hformula
  have hactionSource : gauge.inducedAdjointBundleAction y ∈ e.source := by
    rw [e.source_eq]
    change AdjointBundle.projection torsor (gauge.inducedAdjointBundleAction y) ∈ e.baseSet
    rw [gauge.inducedAdjointBundleAction_projection]
    simpa [e.source_eq] using hy
  rw [← hformula]
  have hinv := e.toOpenPartialHomeomorph.left_inv hactionSource
  change e.toOpenPartialHomeomorph.symm (e (gauge.inducedAdjointBundleAction y)) =
    gauge.inducedAdjointBundleAction y at hinv
  exact hinv.symm

end SmoothGaugeTransformation
end
end YangMills.Geometry

namespace YangMills.Geometry
open scoped Manifold ContDiff
noncomputable section
universe uEG uHG uEB uHB uEP uHP uG uB uP
variable
    {EG : Type uEG} {HG : Type uHG} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
    [TopologicalSpace HG] {EB : Type uEB} {HB : Type uHB} [NormedAddCommGroup EB]
    [NormedSpace ℝ EB] [TopologicalSpace HB] {EP : Type uEP} {HP : Type uHP}
    [NormedAddCommGroup EP] [NormedSpace ℝ EP] [TopologicalSpace HP]
    {G : Type uG} {B : Type uB} {P : Type uP} [Group G] [TopologicalSpace G]
    [TopologicalSpace B] [TopologicalSpace P] [IsTopologicalGroup G]
    {IB : ModelWithCorners ℝ EB HB} {IG : ModelWithCorners ℝ EG HG}
    {IP : ModelWithCorners ℝ EP HP} [ChartedSpace HG G] [LieGroup IG ∞ G]
    [ChartedSpace HB B] [IsManifold IB ∞ B] [ChartedSpace HP P] [IsManifold IP ∞ P]
    {torsor : PrincipalBundleTorsorData G B P} {bundle : TopologicalPrincipalBundleData torsor}
    {smoothBundle : SmoothPrincipalBundleData IB IG IP torsor bundle}

namespace SmoothGaugeTransformation

 theorem inducedAdjointBundleAction_inv_contMDiff
    (gauge : SmoothGaugeTransformation smoothBundle) :
    letI : ChartedSpace (ModelProd HB EG) (AdjointBundle (I := IG) torsor) :=
      AdjointBundle.modelChartedSpace (IG := IG) bundle
    letI : IsManifold (IB.prod 𝓘(ℝ, EG)) ∞ (AdjointBundle (I := IG) torsor) :=
      AdjointBundle.modelIsManifold smoothBundle
    ContMDiff (IB.prod 𝓘(ℝ, EG)) (IB.prod 𝓘(ℝ, EG)) ∞
      gauge⁻¹.inducedAdjointBundleAction := by
  exact inducedAdjointBundleAction_contMDiff gauge⁻¹

 def inducedAdjointBundleDiffeomorph
    (gauge : SmoothGaugeTransformation smoothBundle) :
    letI : ChartedSpace (ModelProd HB EG) (AdjointBundle (I := IG) torsor) :=
      AdjointBundle.modelChartedSpace (IG := IG) bundle
    letI : IsManifold (IB.prod 𝓘(ℝ, EG)) ∞ (AdjointBundle (I := IG) torsor) :=
      AdjointBundle.modelIsManifold smoothBundle
    Diffeomorph (IB.prod 𝓘(ℝ, EG)) (IB.prod 𝓘(ℝ, EG))
      (AdjointBundle (I := IG) torsor) (AdjointBundle (I := IG) torsor) ∞ := by
  letI : ChartedSpace (ModelProd HB EG) (AdjointBundle (I := IG) torsor) :=
    AdjointBundle.modelChartedSpace (IG := IG) bundle
  letI : IsManifold (IB.prod 𝓘(ℝ, EG)) ∞ (AdjointBundle (I := IG) torsor) :=
    AdjointBundle.modelIsManifold smoothBundle
  exact Diffeomorph.mk gauge.inducedAdjointBundleHomeomorph.toEquiv
    (inducedAdjointBundleAction_contMDiff gauge)
    (inducedAdjointBundleAction_inv_contMDiff gauge)

end SmoothGaugeTransformation
end
end YangMills.Geometry
