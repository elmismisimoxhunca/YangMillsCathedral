/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Geometry.PrincipalTwoFormRepresentativeIndependence
import YangMills.Geometry.AdjointBundleDifferentialForm

/-!
# Pointwise descent of horizontal equivariant principal two-forms

A principal two-form is evaluated on the exact tangent lifts from the principal chart selected at
each base point, then transported into the actual dependent adjoint quotient fiber. The resulting
pointwise base form is proved to have the expected quotient representative and, under horizontality
and right adjoint equivariance, to agree with any right-related representative and matching lifts.

Smoothness is deliberately separate here and is derived downstream under the corresponding
principal-form smoothness hypothesis.
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

/-- In a designated chart, the fiber coordinate of the quotient point represented by its local
section and `X` is exactly the declared model coordinate of `X`. -/
theorem AdjointBundle.fiberModelEquiv_localSection_mk
    (chart : PrincipalBundleLocalTrivialization torsor)
    {b : B} (hb : b ∈ chart.baseSet) (X : GroupLieAlgebra IG G) :
    let p := principalBundleLocalSection chart b
    let z : AdjointBundle.Fiber (I := IG) (torsor := torsor) b :=
      ⟨AdjointBundle.mk torsor p X, by
        rw [AdjointBundle.projection_mk, principalBundleLocalSection_projection chart hb]⟩
    AdjointBundle.fiberModelEquiv (I := IG) bundle chart hb z =
      YangMills.Mathematics.groupLieAlgebraModelEquiv IG X := by
  let p := principalBundleLocalSection chart b
  have targetMem := principalBundleLocalSection_pair_mem_target chart hb
  have sourceMem : p ∈ chart.toPartialHomeomorph.source :=
    chart.toPartialHomeomorph.map_target targetMem
  have chart_p : chart.toPartialHomeomorph p = (b, (1 : G)) :=
    chart.toPartialHomeomorph.right_inv targetMem
  change (AdjointBundle.modelBundleTrivialization (I := IG) bundle chart
    (AdjointBundle.mk torsor p X)).2 = _
  rw [AdjointBundle.modelBundleTrivialization_apply,
    AdjointBundle.localCoordinate_mk chart p X sourceMem, chart_p]
  simp

namespace PrincipalTwoForm

/-- Pointwise adjoint-bundle-valued base form obtained from the exact selected local section and its
tangent lift. This definition makes no smoothness claim. -/
def selectedBaseForm
    (form : YangMills.Mathematics.ManifoldDifferentialForm IP P
      (GroupLieAlgebra IG G) 2) :
    AdjointBundle.DifferentialForm (IG := IG) (IB := IB) bundle 2 :=
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
/-- The selected fiber coordinate of the pointwise descended form is exactly the model coordinate of
principal-form evaluation on the selected tangent lifts. -/
theorem selectedBaseForm_coordinate
    (form : YangMills.Mathematics.ManifoldDifferentialForm IP P
      (GroupLieAlgebra IG G) 2)
    (b : B) (v : Fin 2 → TangentSpace IB b) :
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
/-- Forgetting the dependent package gives exactly the expected adjoint quotient representative at
the selected local section. -/
theorem selectedBaseForm_quotient
    (form : YangMills.Mathematics.ManifoldDifferentialForm IP P
      (GroupLieAlgebra IG G) 2)
    (b : B) (v : Fin 2 → TangentSpace IB b) :
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
  let lifts : Fin 2 → TangentSpace IP p :=
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

/-- Under horizontality and right adjoint equivariance, the selected pointwise base value agrees with
any right-related representative and replacement tangent lifts having the translated projections. -/
theorem selectedBaseForm_quotient_eq_rightRelated
    (form : YangMills.Mathematics.ManifoldDifferentialForm IP P
      (GroupLieAlgebra IG G) 2)
    (horizontal : PrincipalTwoForm.IsHorizontal smoothBundle form)
    (equivariant : PrincipalTwoForm.IsRightAdEquivariant smoothBundle form)
    (b : B) (v : Fin 2 → TangentSpace IB b) (g : G)
    (otherLifts : Fin 2 → TangentSpace IP
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

end PrincipalTwoForm

end

end YangMills.Geometry
