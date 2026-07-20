/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Geometry.PrincipalConnectionAffineGaugeTransformation
import YangMills.Mathematics.SmoothManifoldDifferentialForms
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

namespace YangMills.Geometry

/-!
# Direct smoothness of the associated Maurer--Cartan pullback

Smoothness of the exact left Maurer--Cartan pullback is derived directly from smoothness of the
associated gauge function. The proof uses smooth tangent maps of the gauge function and of
`(g,h) ↦ g⁻¹h`; it requires no supplied principal connection. The unchanged raw carrier is then
packaged as a smooth manifold one-form.

This proves regularity only. The Maurer--Cartan structure equation remains separate.
-/

open Set Function Filter ChartedSpace IsManifold Bundle
open scoped Manifold ContDiff Topology Bundle
open YangMills.Mathematics

universe uEG uHG uEB uHB uEP uHP uG uB uP

noncomputable section

set_option backward.isDefEq.respectTransparency false

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
    [ChartedSpace HB B] [IsManifold IB ∞ B]
    [ChartedSpace HG G] [LieGroup IG ∞ G]
    [ChartedSpace HP P] [IsManifold IP ∞ P]
    {torsor : PrincipalBundleTorsorData G B P}
    {bundle : TopologicalPrincipalBundleData torsor}
    {smoothBundle : SmoothPrincipalBundleData IB IG IP torsor bundle}

/-- Direct, connection-free smoothness of the associated Maurer--Cartan pullback. -/
theorem SmoothGaugeTransformation.associatedMaurerCartanPullback_isSmooth
    (gauge : SmoothGaugeTransformation smoothBundle) :
    gauge.associatedMaurerCartanPullback.IsSmooth (groupLieAlgebraModelEquiv IG) := by
  intro s fields fields_smooth
  let gfun : P → G := gauge.associatedGaugeFunction
  let sourceField : P → TangentBundle IP P := fun p => ⟨p, fields 0 p⟩
  have hsourceField : ContMDiffOn IP IP.tangent ∞ sourceField s := fields_smooth 0
  let dgField : P → TangentBundle IG G := fun p => tangentMap IP IG gfun (sourceField p)
  have hdgField : ContMDiffOn IP IG.tangent ∞ dgField s := by
    have htangent : ContMDiff IP.tangent IG.tangent ∞ (tangentMap IP IG gfun) :=
      gauge.associatedGaugeFunction_contMDiff.contMDiff_tangentMap (by simp)
    exact htangent.comp_contMDiffOn hsourceField
  let zeroAtG : P → TangentBundle IG G := fun p => ⟨gfun p, 0⟩
  have hzeroAtG : ContMDiffOn IP IG.tangent ∞ zeroAtG s := by
    have hzero : ContMDiff IG IG.tangent ∞
        (Bundle.zeroSection EG (TangentSpace IG : G → Type _)) :=
      Bundle.contMDiff_zeroSection ℝ _
    exact hzero.comp_contMDiffOn gauge.associatedGaugeFunction_contMDiff.contMDiffOn
  let pairField : P → (TangentBundle IG G × TangentBundle IG G) :=
    fun p => (zeroAtG p, dgField p)
  have hpairField : ContMDiffOn IP (IG.tangent.prod IG.tangent) ∞ pairField s :=
    hzeroAtG.prodMk hdgField
  let productField : P → TangentBundle (IG.prod IG) (G × G) := fun p =>
    (equivTangentBundleProd IG G IG G).symm (pairField p)
  have hproductField : ContMDiffOn IP (IG.prod IG).tangent ∞ productField s :=
    contMDiff_equivTangentBundleProd_symm.comp_contMDiffOn hpairField
  let difference : G × G → G := fun z => z.1⁻¹ * z.2
  have hdifference : ContMDiff (IG.prod IG) IG ∞ difference :=
    contMDiff_fst.inv.mul contMDiff_snd
  let resultField : P → TangentBundle IG G := fun p =>
    tangentMap (IG.prod IG) IG difference (productField p)
  have hresultField : ContMDiffOn IP IG.tangent ∞ resultField s := by
    have htangent : ContMDiff (IG.prod IG).tangent IG.tangent ∞
        (tangentMap (IG.prod IG) IG difference) :=
      hdifference.contMDiff_tangentMap (by simp)
    exact htangent.comp_contMDiffOn hproductField
  intro p hp
  have htotal := hresultField p hp
  have hfiber := (Bundle.contMDiffWithinAt_totalSpace.mp htotal).2
  have hbase : (resultField p).proj = (1 : G) := by
    simp [resultField, productField, pairField, zeroAtG, dgField, sourceField,
      difference, tangentMap]
  rw [hbase] at hfiber
  apply hfiber.congr_of_eventuallyEq_of_mem _ hp
  filter_upwards [self_mem_nhdsWithin] with q hq
  have hbaseq : (resultField q).proj = (1 : G) := by
    simp [resultField, productField, pairField, zeroAtG, dgField, sourceField,
      difference, tangentMap]
  rw [TangentBundle.trivializationAt_apply, hbaseq]
  change groupLieAlgebraModelEquiv IG
      (gauge.associatedMaurerCartanPullback q (fun i => fields i q)) =
    tangentCoordChange IG (1 : G) (1 : G) (1 : G) (resultField q).2
  rw [tangentCoordChange_self (mem_extChartAt_source (I := IG) (1 : G))]
  simp [resultField, productField, pairField, zeroAtG, dgField, sourceField,
    difference, tangentMap, gfun,
    SmoothGaugeTransformation.associatedMaurerCartanPullback,
    groupLieAlgebraModelEquiv]
  symm
  let g : G := gauge.associatedGaugeFunction q
  let w : EG := mfderiv IP IG gauge.associatedGaugeFunction q (fields 0 q)
  change mfderiv (IG.prod IG) IG (fun z : G × G => z.1⁻¹ * z.2)
      (g, g) (0, w) = mfderiv IG IG (fun y : G => g⁻¹ * y) g w
  have hsplit := mfderiv_prod_eq_add_apply
    (f := fun z : G × G => z.1⁻¹ * z.2) (p := (g, g)) (v := ((0, w) : EG × EG))
    (hdifference.mdifferentiableAt (by simp))
  rw [hsplit]
  simp

/-- Connection-independent smooth-form package for the exact Maurer--Cartan carrier. -/
noncomputable def SmoothGaugeTransformation.associatedMaurerCartanPullbackSmoothForm
    (gauge : SmoothGaugeTransformation smoothBundle) :
    SmoothManifoldDifferentialForm IP P (GroupLieAlgebra IG G)
      (groupLieAlgebraModelEquiv IG) 1 where
  toForm := gauge.associatedMaurerCartanPullback
  smooth := gauge.associatedMaurerCartanPullback_isSmooth

@[simp] theorem SmoothGaugeTransformation.associatedMaurerCartanPullbackSmoothForm_toForm
    (gauge : SmoothGaugeTransformation smoothBundle) :
    gauge.associatedMaurerCartanPullbackSmoothForm.toForm =
      gauge.associatedMaurerCartanPullback := rfl

end
end YangMills.Geometry
