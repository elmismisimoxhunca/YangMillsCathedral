/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Geometry.PrincipalFormLiftIndependence
import YangMills.Geometry.PrincipalTwoFormSmoothDescent

/-!
# Arbitrary-degree tensorial principal-form descent

A horizontal, right-adjoint-equivariant smooth Lie-algebra-valued principal form of any degree
descends into the actual dependent-fiber adjoint-bundle differential-form carrier. Lift and
representative independence, arbitrary designated-chart coordinates, and smoothness are derived.
The existing degree-two predicates and selected carrier are definitionally compatible
specializations.

Two degree-independent coordinate/right-translation helpers currently reside in the older
degree-two modules and are reused here; no degree-two theorem is used to prove generic descent.
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

namespace PrincipalForm

variable {k : ℕ}

/-- Generic-degree version of right adjoint equivariance. -/
def IsRightAdEquivariant
    (smoothBundle : SmoothPrincipalBundleData IB IG IP torsor bundle)
    (form : YangMills.Mathematics.ManifoldDifferentialForm IP P
      (GroupLieAlgebra IG G) k) : Prop :=
  ∀ (g : G) (p : P) (v : Fin k → TangentSpace IP p),
    form (torsor.rightAction p g)
        (fun i => principalRightTranslationDifferential smoothBundle p g (v i)) =
      YangMills.Mathematics.lieGroupAdjoint IG g⁻¹ (form p v)



namespace IsRightAdEquivariant

/-- Right-equivariant evaluation at right-related representatives gives the same quotient point. -/
theorem mk_rightTranslation
    (form : YangMills.Mathematics.ManifoldDifferentialForm IP P
      (GroupLieAlgebra IG G) k)
    (equivariant : IsRightAdEquivariant smoothBundle form)
    (p : P) (g : G) (lifts : Fin k → TangentSpace IP p) :
    AdjointBundle.mk torsor (torsor.rightAction p g)
        (form (torsor.rightAction p g)
          (fun i => principalRightTranslationDifferential smoothBundle p g (lifts i))) =
      AdjointBundle.mk torsor p (form p lifts) := by
  rw [equivariant g p lifts]
  exact AdjointBundle.mk_rightAction torsor p (form p lifts) g

/-- Generic representative and lift independence. -/
theorem mk_eq_of_rightTranslation_and_projection_eq
    (form : YangMills.Mathematics.ManifoldDifferentialForm IP P
      (GroupLieAlgebra IG G) k)
    (horizontal : IsHorizontal smoothBundle form)
    (equivariant : IsRightAdEquivariant smoothBundle form)
    (p : P) (g : G)
    (lifts : Fin k → TangentSpace IP p)
    (translatedLifts : Fin k → TangentSpace IP (torsor.rightAction p g))
    (sameProjection : ∀ i,
      mfderiv IP IB torsor.projection (torsor.rightAction p g) (translatedLifts i) =
        mfderiv IP IB torsor.projection (torsor.rightAction p g)
          (principalRightTranslationDifferential smoothBundle p g (lifts i))) :
    AdjointBundle.mk torsor (torsor.rightAction p g)
        (form (torsor.rightAction p g) translatedLifts) =
      AdjointBundle.mk torsor p (form p lifts) := by
  have liftEq := horizontal.eq_of_projection_eq smoothBundle form
    (torsor.rightAction p g) translatedLifts
    (fun i => principalRightTranslationDifferential smoothBundle p g (lifts i)) sameProjection
  rw [liftEq]
  exact equivariant.mk_rightTranslation smoothBundle form p g lifts

end IsRightAdEquivariant

/-- Pointwise selected descent in arbitrary degree. -/
def selectedBaseForm
    (form : YangMills.Mathematics.ManifoldDifferentialForm IP P
      (GroupLieAlgebra IG G) k) :
    AdjointBundle.DifferentialForm (IG := IG) (IB := IB) bundle k :=
  fun b => by
    letI : AddCommGroup (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
      AdjointBundle.fiberAddCommGroup (I := IG) bundle b
    letI : Module ℝ (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
      AdjointBundle.fiberModule (I := IG) bundle b
    letI : TopologicalSpace (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
      AdjointBundle.fiberTopology (I := IG) bundle b
    let chart := bundle.trivializationAt b
    let hb := bundle.mem_baseSet_trivializationAt b
    let p := principalBundleLocalSection chart b
    let lift := principalBundleLocalTangentLift (IB := IB) (IP := IP) chart b
    let lifted := (form p).compContinuousLinearMap lift
    let modelValue :=
      (YangMills.Mathematics.groupLieAlgebraModelEquiv IG).toContinuousLinearMap
        |>.compContinuousAlternatingMap lifted
    exact (AdjointBundle.fiberModelContinuousLinearEquiv (IG := IG) bundle chart hb).symm
      |>.toContinuousLinearMap.compContinuousAlternatingMap modelValue

omit [IsManifold IB ∞ B] [IsManifold IP ∞ P] in
/-- Exact coordinate formula in the internally selected chart. -/
theorem selectedBaseForm_coordinate
    (form : YangMills.Mathematics.ManifoldDifferentialForm IP P
      (GroupLieAlgebra IG G) k)
    (b : B) (v : Fin k → TangentSpace IB b) :
    letI : AddCommGroup (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
      AdjointBundle.fiberAddCommGroup (I := IG) bundle b
    letI : Module ℝ (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
      AdjointBundle.fiberModule (I := IG) bundle b
    letI : TopologicalSpace (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
      AdjointBundle.fiberTopology (I := IG) bundle b
    let chart := bundle.trivializationAt b
    let hb := bundle.mem_baseSet_trivializationAt b
    AdjointBundle.fiberModelContinuousLinearEquiv (IG := IG) bundle chart hb
        ((selectedBaseForm (IB := IB) (bundle := bundle) form b) v) =
      YangMills.Mathematics.groupLieAlgebraModelEquiv IG
        (form (principalBundleLocalSection chart b)
          (fun i => principalBundleLocalTangentLift (IB := IB) (IP := IP) chart b (v i))) := by
  letI : AddCommGroup (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
    AdjointBundle.fiberAddCommGroup (I := IG) bundle b
  letI : Module ℝ (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
    AdjointBundle.fiberModule (I := IG) bundle b
  letI : TopologicalSpace (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
    AdjointBundle.fiberTopology (I := IG) bundle b
  let chart := bundle.trivializationAt b
  let hb := bundle.mem_baseSet_trivializationAt b
  let coordinate := AdjointBundle.fiberModelContinuousLinearEquiv (IG := IG) bundle chart hb
  change coordinate (coordinate.symm
    (YangMills.Mathematics.groupLieAlgebraModelEquiv IG
      (form (principalBundleLocalSection chart b)
        (fun i => principalBundleLocalTangentLift (IB := IB) (IP := IP) chart b (v i))))) = _
  exact coordinate.apply_symm_apply _

omit [IsManifold IB ∞ B] [IsManifold IP ∞ P] in
/-- The selected value has the expected exact quotient representative. -/
theorem selectedBaseForm_quotient
    (form : YangMills.Mathematics.ManifoldDifferentialForm IP P
      (GroupLieAlgebra IG G) k)
    (b : B) (v : Fin k → TangentSpace IB b) :
    ((selectedBaseForm (IB := IB) (bundle := bundle) form b) v).1 =
      AdjointBundle.mk torsor
        (principalBundleLocalSection (bundle.trivializationAt b) b)
        (form (principalBundleLocalSection (bundle.trivializationAt b) b)
          (fun i => principalBundleLocalTangentLift (IB := IB) (IP := IP)
            (bundle.trivializationAt b) b (v i))) := by
  letI : AddCommGroup (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
    AdjointBundle.fiberAddCommGroup (I := IG) bundle b
  letI : Module ℝ (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
    AdjointBundle.fiberModule (I := IG) bundle b
  letI : TopologicalSpace (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
    AdjointBundle.fiberTopology (I := IG) bundle b
  let chart := bundle.trivializationAt b
  let hb := bundle.mem_baseSet_trivializationAt b
  let p := principalBundleLocalSection chart b
  let lifts : Fin k → TangentSpace IP p :=
    fun i => principalBundleLocalTangentLift (IB := IB) (IP := IP) chart b (v i)
  let expected : AdjointBundle.Fiber (I := IG) (torsor := torsor) b :=
    ⟨AdjointBundle.mk torsor p (form p lifts), by
      rw [AdjointBundle.projection_mk, principalBundleLocalSection_projection chart hb]⟩
  have coordinateEq :
      AdjointBundle.fiberModelContinuousLinearEquiv (IG := IG) bundle chart hb
          ((selectedBaseForm (IB := IB) (bundle := bundle) form b) v) =
        AdjointBundle.fiberModelContinuousLinearEquiv (IG := IG) bundle chart hb expected := by
    rw [selectedBaseForm_coordinate]
    exact ((AdjointBundle.fiberModelContinuousLinearEquiv_apply
      (IG := IG) bundle chart hb expected).trans (by
        simpa [expected, p, lifts] using
          (AdjointBundle.fiberModelEquiv_localSection_mk
            (bundle := bundle) chart hb (form p lifts)))).symm
  exact congrArg Subtype.val
    ((AdjointBundle.fiberModelContinuousLinearEquiv (IG := IG) bundle chart hb).injective
      coordinateEq)

/-- Selected descent agrees with any right-related representative and matching lifts. -/
theorem selectedBaseForm_quotient_eq_rightRelated
    (form : YangMills.Mathematics.ManifoldDifferentialForm IP P
      (GroupLieAlgebra IG G) k)
    (horizontal : IsHorizontal smoothBundle form)
    (equivariant : IsRightAdEquivariant smoothBundle form)
    (b : B) (v : Fin k → TangentSpace IB b) (g : G)
    (otherLifts : Fin k → TangentSpace IP
      (torsor.rightAction
        (principalBundleLocalSection (bundle.trivializationAt b) b) g))
    (sameProjection : ∀ i,
      mfderiv IP IB torsor.projection
          (torsor.rightAction
            (principalBundleLocalSection (bundle.trivializationAt b) b) g)
          (otherLifts i) =
        mfderiv IP IB torsor.projection
          (torsor.rightAction
            (principalBundleLocalSection (bundle.trivializationAt b) b) g)
          (principalRightTranslationDifferential smoothBundle
            (principalBundleLocalSection (bundle.trivializationAt b) b) g
            (principalBundleLocalTangentLift (IB := IB) (IP := IP)
              (bundle.trivializationAt b) b (v i)))) :
    ((selectedBaseForm (IB := IB) (bundle := bundle) form b) v).1 =
      AdjointBundle.mk torsor
        (torsor.rightAction
          (principalBundleLocalSection (bundle.trivializationAt b) b) g)
        (form
          (torsor.rightAction
            (principalBundleLocalSection (bundle.trivializationAt b) b) g)
          otherLifts) := by
  rw [selectedBaseForm_quotient]
  exact (equivariant.mk_eq_of_rightTranslation_and_projection_eq smoothBundle form horizontal
    (principalBundleLocalSection (bundle.trivializationAt b) b) g
    (fun i => principalBundleLocalTangentLift (IB := IB) (IP := IP)
      (bundle.trivializationAt b) b (v i)) otherLifts sameProjection).symm

/-- Coordinate formula in every designated chart. -/
theorem selectedBaseForm_inCoordinates
    (form : YangMills.Mathematics.ManifoldDifferentialForm IP P
      (GroupLieAlgebra IG G) k)
    (horizontal : IsHorizontal smoothBundle form)
    (equivariant : IsRightAdEquivariant smoothBundle form)
    (chart : PrincipalBundleLocalTrivialization torsor)
    (chart_mem : chart ∈ bundle.trivializationAtlas)
    {b : B} (hb : b ∈ chart.baseSet)
    (v : Fin k → TangentSpace IB b) :
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
  let chartLifts : Fin k → TangentSpace IP q :=
    fun i => principalBundleLocalTangentLift (IB := IB) (IP := IP) chart b (v i)
  let otherLifts : Fin k → TangentSpace IP (torsor.rightAction p g) :=
    fun i => hg.symm ▸ chartLifts i
  have mfderiv_transport {x y : P} (h : x = y) (w : TangentSpace IP y) :
      mfderiv IP IB torsor.projection x (h.symm ▸ w) =
        mfderiv IP IB torsor.projection y w := by
    subst y
    rfl
  have form_mk_transport {x y : P} (h : x = y)
      (lifts : Fin k → TangentSpace IP y) :
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
      (selectedBaseForm (IB := IB) (bundle := bundle) form b) v = expected := by
    apply Subtype.ext
    exact quotientEq
  rw [valueEq]
  simpa [expected, q, chartLifts] using
    (AdjointBundle.fiberModelEquiv_localSection_mk
      (bundle := bundle) chart hb (form q chartLifts))

/-- Smoothness of the exact selected generic-degree pointwise descent. -/
theorem selectedBaseForm_isSmooth
    (form : YangMills.Mathematics.ManifoldDifferentialForm IP P
      (GroupLieAlgebra IG G) k)
    (form_smooth :
      form.IsSmooth
        (YangMills.Mathematics.groupLieAlgebraModelEquiv IG))
    (horizontal : IsHorizontal smoothBundle form)
    (equivariant : IsRightAdEquivariant smoothBundle form) :
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

/-- Generic-degree smooth descent package. -/
noncomputable def selectedBaseFormSmooth
    (form : YangMills.Mathematics.ManifoldDifferentialForm IP P
      (GroupLieAlgebra IG G) k)
    (form_smooth :
      form.IsSmooth
        (YangMills.Mathematics.groupLieAlgebraModelEquiv IG))
    (horizontal : IsHorizontal smoothBundle form)
    (equivariant : IsRightAdEquivariant smoothBundle form) :
    AdjointBundle.DifferentialForm.Smooth smoothBundle k where
  toForm := selectedBaseForm (IB := IB) (bundle := bundle) form
  smooth := selectedBaseForm_isSmooth smoothBundle form form_smooth horizontal equivariant

@[simp]
theorem selectedBaseFormSmooth_toForm
    (form : YangMills.Mathematics.ManifoldDifferentialForm IP P
      (GroupLieAlgebra IG G) k)
    (form_smooth :
      form.IsSmooth
        (YangMills.Mathematics.groupLieAlgebraModelEquiv IG))
    (horizontal : IsHorizontal smoothBundle form)
    (equivariant : IsRightAdEquivariant smoothBundle form) :
    (selectedBaseFormSmooth smoothBundle form form_smooth horizontal equivariant).toForm =
      selectedBaseForm (IB := IB) (bundle := bundle) form :=
  rfl

/-- The generic horizontal predicate specializes definitionally to the current degree-two API. -/
example
    (form : YangMills.Mathematics.ManifoldDifferentialForm IP P
      (GroupLieAlgebra IG G) 2) :
    IsHorizontal smoothBundle form ↔
      PrincipalTwoForm.IsHorizontal smoothBundle form :=
  Iff.rfl

/-- The generic equivariance predicate specializes definitionally to the current degree-two API. -/
example
    (form : YangMills.Mathematics.ManifoldDifferentialForm IP P
      (GroupLieAlgebra IG G) 2) :
    IsRightAdEquivariant smoothBundle form ↔
      PrincipalTwoForm.IsRightAdEquivariant smoothBundle form :=
  Iff.rfl

/-- The generic selected carrier at degree two is definitionally the existing selected carrier. -/
example
    (form : YangMills.Mathematics.ManifoldDifferentialForm IP P
      (GroupLieAlgebra IG G) 2) :
    selectedBaseForm (IB := IB) (bundle := bundle) form =
      PrincipalTwoForm.selectedBaseForm (IB := IB) (bundle := bundle) form :=
  rfl

end PrincipalForm

end
end YangMills.Geometry
