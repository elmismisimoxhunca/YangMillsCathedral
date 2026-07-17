/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Geometry.PrincipalTwoFormPointwiseDescent

/-!
# Hostile probes for pointwise descent of principal two-forms
-/

namespace YangMills.Geometry.Probes

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

omit [IsManifold IB ∞ B] [IsManifold IP ∞ P] in
/-- The selected fiber coordinate cannot be disconnected from principal-form evaluation on the
exact selected tangent lifts. -/
theorem replacement_pointwiseDescent_coordinate_blocked
    (form : YangMills.Mathematics.ManifoldDifferentialForm IP P
      (GroupLieAlgebra IG G) 2)
    (b : B) (v : Fin 2 → TangentSpace IB b)
    (mismatch :
      letI : AddCommGroup (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
        AdjointBundle.fiberAddCommGroup (I := IG) bundle b
      letI : Module ℝ (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
        AdjointBundle.fiberModule (I := IG) bundle b
      letI : TopologicalSpace (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
        AdjointBundle.fiberTopology (I := IG) bundle b
      let chart := bundle.trivializationAt b
      let hb := bundle.mem_baseSet_trivializationAt b
      AdjointBundle.fiberModelContinuousLinearEquiv (IG := IG) bundle chart hb
          ((PrincipalTwoForm.selectedBaseForm (IB := IB) (bundle := bundle) form b) v) ≠
        YangMills.Mathematics.groupLieAlgebraModelEquiv IG
          (form (principalBundleLocalSection chart b)
            (fun i => principalBundleLocalTangentLift (IB := IB) (IP := IP) chart b (v i)))) : False := by
  letI : AddCommGroup (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
    AdjointBundle.fiberAddCommGroup (I := IG) bundle b
  letI : Module ℝ (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
    AdjointBundle.fiberModule (I := IG) bundle b
  letI : TopologicalSpace (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
    AdjointBundle.fiberTopology (I := IG) bundle b
  exact mismatch (PrincipalTwoForm.selectedBaseForm_coordinate (bundle := bundle) form b v)

omit [IsManifold IB ∞ B] [IsManifold IP ∞ P] in
/-- Forgetting the dependent package cannot yield a quotient representative unrelated to the
selected local section and lifts. -/
theorem replacement_pointwiseDescent_quotientRepresentative_blocked
    (form : YangMills.Mathematics.ManifoldDifferentialForm IP P
      (GroupLieAlgebra IG G) 2)
    (b : B) (v : Fin 2 → TangentSpace IB b)
    (mismatch :
      ((PrincipalTwoForm.selectedBaseForm (IB := IB) (bundle := bundle) form b) v).1 ≠
        AdjointBundle.mk torsor
          (principalBundleLocalSection (bundle.trivializationAt b) b)
          (form (principalBundleLocalSection (bundle.trivializationAt b) b)
            (fun i => principalBundleLocalTangentLift (IB := IB) (IP := IP)
              (bundle.trivializationAt b) b (v i)))) : False :=
  mismatch (PrincipalTwoForm.selectedBaseForm_quotient (bundle := bundle) form b v)

/-- A horizontal equivariant pointwise descent cannot disagree with a right-related representative
and matching lifts. -/
theorem rightRelated_pointwiseDescent_mismatch_blocked
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
              (bundle.trivializationAt b) b (v i))))
    (mismatch :
      ((PrincipalTwoForm.selectedBaseForm (IB := IB) (bundle := bundle) form b) v).1 ≠
        AdjointBundle.mk torsor
          (torsor.rightAction
            (principalBundleLocalSection (bundle.trivializationAt b) b) g)
          (form
            (torsor.rightAction
              (principalBundleLocalSection (bundle.trivializationAt b) b) g)
            otherLifts)) : False :=
  mismatch (PrincipalTwoForm.selectedBaseForm_quotient_eq_rightRelated smoothBundle form
    horizontal equivariant b v g otherLifts sameProjection)

end

end YangMills.Geometry.Probes
