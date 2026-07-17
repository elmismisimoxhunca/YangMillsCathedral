/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Geometry.PrincipalCurvaturePointwiseDescent

/-!
# Hostile probes for pointwise descent of certified principal curvature
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
    {smoothBundle : SmoothPrincipalBundleData IB IG IP torsor bundle}
    [FiniteDimensional ℝ EG]

/-- The pointwise base curvature cannot be replaced by the descent of an unrelated principal form. -/
theorem unrelated_pointwiseBaseCurvature_blocked
    (connection : PrincipalConnectionData smoothBundle)
    (exterior : PrincipalConnectionExteriorDerivativeData connection)
    (mismatch : connection.pointwiseBaseCurvature exterior ≠
      PrincipalTwoForm.selectedBaseForm (IB := IB) (bundle := bundle)
        (connection.curvatureForm exterior).toForm) : False :=
  mismatch (connection.pointwiseBaseCurvature_eq exterior)

/-- Forgetting the dependent package must yield the exact selected representative of the derived
principal curvature. -/
theorem replacement_pointwiseBaseCurvatureRepresentative_blocked
    (connection : PrincipalConnectionData smoothBundle)
    (exterior : PrincipalConnectionExteriorDerivativeData connection)
    (b : B) (v : Fin 2 → TangentSpace IB b)
    (mismatch : ((connection.pointwiseBaseCurvature exterior b) v).1 ≠
      AdjointBundle.mk torsor
        (principalBundleLocalSection (bundle.trivializationAt b) b)
        ((connection.curvatureForm exterior).toForm
          (principalBundleLocalSection (bundle.trivializationAt b) b)
          (fun i => principalBundleLocalTangentLift (IB := IB) (IP := IP)
            (bundle.trivializationAt b) b (v i)))) : False :=
  mismatch (connection.pointwiseBaseCurvature_quotient exterior b v)

/-- The exact structure certificate cannot fail to identify a right-related presentation of the
same pointwise descended curvature value. -/
theorem rightRelated_pointwiseBaseCurvature_mismatch_blocked
    (connection : PrincipalConnectionData smoothBundle)
    (exterior : PrincipalConnectionExteriorDerivativeData connection)
    (certificate : PrincipalCurvatureStructureCertificate smoothBundle connection exterior)
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
    (mismatch : ((connection.pointwiseBaseCurvature exterior b) v).1 ≠
      AdjointBundle.mk torsor
        (torsor.rightAction
          (principalBundleLocalSection (bundle.trivializationAt b) b) g)
        ((connection.curvatureForm exterior).toForm
          (torsor.rightAction
            (principalBundleLocalSection (bundle.trivializationAt b) b) g)
          otherLifts)) : False :=
  mismatch (connection.pointwiseBaseCurvature_quotient_eq_rightRelated exterior certificate
    b v g otherLifts sameProjection)

/-- Alternation cannot be lost during pointwise curvature descent. -/
theorem nonalternating_pointwiseBaseCurvature_blocked
    (connection : PrincipalConnectionData smoothBundle)
    (exterior : PrincipalConnectionExteriorDerivativeData connection)
    (b : B) (v : TangentSpace IB b)
    (nonzero :
      letI : AddCommGroup (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
        AdjointBundle.fiberAddCommGroup (I := IG) bundle b
      letI : Module ℝ (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
        AdjointBundle.fiberModule (I := IG) bundle b
      letI : TopologicalSpace (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
        AdjointBundle.fiberTopology (I := IG) bundle b
      (connection.pointwiseBaseCurvature exterior b) (fun _ => v) ≠ 0) : False := by
  letI : AddCommGroup (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
    AdjointBundle.fiberAddCommGroup (I := IG) bundle b
  letI : Module ℝ (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
    AdjointBundle.fiberModule (I := IG) bundle b
  letI : TopologicalSpace (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
    AdjointBundle.fiberTopology (I := IG) bundle b
  exact nonzero (connection.pointwiseBaseCurvature_evalTwo_same exterior b v)

end

end YangMills.Geometry.Probes
