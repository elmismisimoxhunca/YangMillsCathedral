/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Geometry.PrincipalFormLocalLiftSmooth
import YangMills.Geometry.PrincipalTwoFormPointwiseDescent
import YangMills.Geometry.AdjointBundleSmoothDifferentialForm

/-!
# Smooth descent of principal two-forms

A smooth, horizontal, right-adjoint-equivariant principal two-form descends from the exact pointwise
quotient construction to a smooth adjoint-bundle-valued two-form. The key theorem identifies its
fiber coordinate in any designated principal chart, although the pointwise construction internally
selects `trivializationAt`.

No existence of a principal form or structural certificate is asserted here.
-/

namespace YangMills.Geometry

open Set
open scoped Manifold ContDiff Bundle Topology

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
    (smoothBundle : SmoothPrincipalBundleData IB IG IP torsor bundle)

namespace PrincipalTwoForm

/-- In every designated chart, the coordinate of the selected pointwise descent is the model
coordinate of principal-form evaluation at that chart's own local section and exact local lifts. -/
theorem selectedBaseForm_inCoordinates
    (form : YangMills.Mathematics.ManifoldDifferentialForm IP P
      (GroupLieAlgebra IG G) 2)
    (horizontal : PrincipalTwoForm.IsHorizontal smoothBundle form)
    (equivariant : PrincipalTwoForm.IsRightAdEquivariant smoothBundle form)
    (chart : PrincipalBundleLocalTrivialization torsor)
    (chart_mem : chart ∈ bundle.trivializationAtlas)
    {b : B} (hb : b ∈ chart.baseSet)
    (v : Fin 2 → TangentSpace IB b) :
    AdjointBundle.DifferentialForm.inCoordinates
        (selectedBaseForm (IB := IB) (bundle := bundle) form) chart hb v =
      YangMills.Mathematics.groupLieAlgebraModelEquiv IG
        (form (principalBundleLocalSection chart b)
          (fun i => principalBundleLocalTangentLift (IB := IB) (IP := IP)
            chart b (v i))) := by
  letI : AddCommGroup (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
    AdjointBundle.fiberAddCommGroup (I := IG) bundle b
  letI : Module ℝ (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
    AdjointBundle.fiberModule (I := IG) bundle b
  letI : TopologicalSpace (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
    AdjointBundle.fiberTopology (I := IG) bundle b
  rw [AdjointBundle.DifferentialForm.inCoordinates_apply]
  let selectedChart := bundle.trivializationAt b
  let p := principalBundleLocalSection selectedChart b
  let q := principalBundleLocalSection chart b
  have hp : torsor.projection p = b :=
    principalBundleLocalSection_projection selectedChart
      (bundle.mem_baseSet_trivializationAt b)
  have hq : torsor.projection q = b :=
    principalBundleLocalSection_projection chart hb
  obtain ⟨g, hg⟩ := torsor.sameFiber_transitive (hp.trans hq.symm)
  let chartLifts : Fin 2 → TangentSpace IP q :=
    fun i => principalBundleLocalTangentLift (IB := IB) (IP := IP) chart b (v i)
  let otherLifts : Fin 2 → TangentSpace IP (torsor.rightAction p g) :=
    fun i => hg.symm ▸ chartLifts i
  have mfderiv_transport {x y : P} (h : x = y) (w : TangentSpace IP y) :
      mfderiv IP IB torsor.projection x (h.symm ▸ w) =
        mfderiv IP IB torsor.projection y w := by
    subst y
    rfl
  have form_mk_transport {x y : P} (h : x = y)
      (lifts : Fin 2 → TangentSpace IP y) :
      AdjointBundle.mk torsor x
          (form x (fun i => h.symm ▸ lifts i)) =
        AdjointBundle.mk torsor y (form y lifts) := by
    subst y
    rfl
  have hother : ∀ i,
      mfderiv IP IB torsor.projection (torsor.rightAction p g)
          (otherLifts i) = v i := by
    intro i
    change mfderiv IP IB torsor.projection (torsor.rightAction p g)
      (hg.symm ▸ chartLifts i) = v i
    rw [mfderiv_transport hg]
    exact (principalBundleLocalTangentLift_rightInverse
      smoothBundle chart chart_mem hb) (v i)
  have sameProjection : ∀ i,
      mfderiv IP IB torsor.projection (torsor.rightAction p g)
          (otherLifts i) =
        mfderiv IP IB torsor.projection (torsor.rightAction p g)
          (principalRightTranslationDifferential smoothBundle p g
            (principalBundleLocalTangentLift (IB := IB) (IP := IP)
              selectedChart b (v i))) := by
    intro i
    rw [hother i,
      principalBundleProjectionDifferential_rightTranslation_apply]
    exact ((principalBundleLocalTangentLift_rightInverse
      smoothBundle selectedChart
      (bundle.trivializationAt_mem_atlas b)
      (bundle.mem_baseSet_trivializationAt b)) (v i)).symm
  have quotientEq' :=
    selectedBaseForm_quotient_eq_rightRelated smoothBundle form
      horizontal equivariant b v g otherLifts sameProjection
  have quotientEq :
      ((selectedBaseForm (IB := IB) (bundle := bundle) form b) v).1 =
        AdjointBundle.mk torsor q (form q chartLifts) := by
    apply quotientEq'.trans
    exact form_mk_transport hg chartLifts
  let expected : AdjointBundle.Fiber (I := IG) (torsor := torsor) b :=
    ⟨AdjointBundle.mk torsor q (form q chartLifts), by
      rw [AdjointBundle.projection_mk, hq]⟩
  have valueEq :
      (selectedBaseForm (IB := IB) (bundle := bundle) form b) v =
        expected := by
    apply Subtype.ext
    exact quotientEq
  rw [valueEq]
  simpa [expected, q, chartLifts] using
    (AdjointBundle.fiberModelEquiv_localSection_mk
      (bundle := bundle) chart hb (form q chartLifts))

/-- Smoothness of a principal form, together with horizontal and right-equivariant descent laws,
makes its exact selected pointwise descent smooth in every designated adjoint chart. -/
theorem selectedBaseForm_isSmooth
    (form : YangMills.Mathematics.ManifoldDifferentialForm IP P
      (GroupLieAlgebra IG G) 2)
    (form_smooth :
      form.IsSmooth
        (YangMills.Mathematics.groupLieAlgebraModelEquiv IG))
    (horizontal : PrincipalTwoForm.IsHorizontal smoothBundle form)
    (equivariant : PrincipalTwoForm.IsRightAdEquivariant smoothBundle form) :
    AdjointBundle.DifferentialForm.IsSmooth smoothBundle
      (selectedBaseForm (IB := IB) (bundle := bundle) form) := by
  intro chart chart_mem s fields hs fields_smooth
  have evaluationSmooth :=
    principalBundleLocalTangentLift_formEvaluation_contMDiffOn
      (YangMills.Mathematics.groupLieAlgebraModelEquiv IG)
      form form_smooth smoothBundle chart chart_mem hs fields fields_smooth
  refine evaluationSmooth.congr ?_
  intro b hb
  rw [AdjointBundle.DifferentialForm.coordinateEvaluation_eq_inCoordinates
    _ chart fields (hs hb)]
  exact selectedBaseForm_inCoordinates smoothBundle form horizontal equivariant
    chart chart_mem (hs hb) (fun i => fields i b)

/-- The smooth selected descent packaged without changing its pointwise carrier. -/
noncomputable def selectedBaseFormSmooth
    (form : YangMills.Mathematics.ManifoldDifferentialForm IP P
      (GroupLieAlgebra IG G) 2)
    (form_smooth :
      form.IsSmooth
        (YangMills.Mathematics.groupLieAlgebraModelEquiv IG))
    (horizontal : PrincipalTwoForm.IsHorizontal smoothBundle form)
    (equivariant : PrincipalTwoForm.IsRightAdEquivariant smoothBundle form) :
    AdjointBundle.DifferentialForm.Smooth smoothBundle 2 where
  toForm := selectedBaseForm (IB := IB) (bundle := bundle) form
  smooth := selectedBaseForm_isSmooth smoothBundle form form_smooth horizontal equivariant

/-- Packaging the smooth descent preserves the exact selected pointwise form. -/
@[simp]
theorem selectedBaseFormSmooth_toForm
    (form : YangMills.Mathematics.ManifoldDifferentialForm IP P
      (GroupLieAlgebra IG G) 2)
    (form_smooth :
      form.IsSmooth
        (YangMills.Mathematics.groupLieAlgebraModelEquiv IG))
    (horizontal : PrincipalTwoForm.IsHorizontal smoothBundle form)
    (equivariant : PrincipalTwoForm.IsRightAdEquivariant smoothBundle form) :
    (selectedBaseFormSmooth smoothBundle form form_smooth horizontal equivariant).toForm =
      selectedBaseForm (IB := IB) (bundle := bundle) form :=
  rfl

end PrincipalTwoForm

end

end YangMills.Geometry
