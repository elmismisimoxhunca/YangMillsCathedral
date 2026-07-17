/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Geometry.PrincipalTwoFormPointwiseDescent

/-!
# Pointwise descent of certified principal curvature

The generic pointwise descent is specialized to the exact curvature derived from a principal
connection and its exterior-derivative data. A `PrincipalCurvatureStructureCertificate` supplies
horizontality and right adjoint equivariance for that same curvature, yielding presentation
independence in the actual adjoint quotient.

Smoothness of the descended curvature remains pending.
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
    {smoothBundle : SmoothPrincipalBundleData IB IG IP torsor bundle}
    [FiniteDimensional ℝ EG]

namespace PrincipalConnectionData

/-- Pointwise dependent adjoint-bundle-valued curvature obtained from the exact derived principal
curvature. No unrelated principal or base form is accepted. -/
noncomputable def pointwiseBaseCurvature
    (connection : PrincipalConnectionData smoothBundle)
    (exterior : PrincipalConnectionExteriorDerivativeData connection) :
    AdjointBundle.DifferentialForm (IG := IG) (IB := IB) bundle 2 :=
  PrincipalTwoForm.selectedBaseForm (IB := IB) (bundle := bundle)
    (connection.curvatureForm exterior).toForm

/-- The pointwise base curvature is definitionally the generic selected descent of the exact derived
principal curvature, not an unrelated base form. -/
theorem pointwiseBaseCurvature_eq
    (connection : PrincipalConnectionData smoothBundle)
    (exterior : PrincipalConnectionExteriorDerivativeData connection) :
    connection.pointwiseBaseCurvature exterior =
      PrincipalTwoForm.selectedBaseForm (IB := IB) (bundle := bundle)
        (connection.curvatureForm exterior).toForm :=
  rfl

/-- The descended pointwise curvature has exactly the selected local-section quotient
representative of the derived principal curvature. -/
theorem pointwiseBaseCurvature_quotient
    (connection : PrincipalConnectionData smoothBundle)
    (exterior : PrincipalConnectionExteriorDerivativeData connection)
    (b : B) (v : Fin 2 → TangentSpace IB b) :
    ((connection.pointwiseBaseCurvature exterior b) v).1 =
      AdjointBundle.mk torsor
        (principalBundleLocalSection (bundle.trivializationAt b) b)
        ((connection.curvatureForm exterior).toForm
          (principalBundleLocalSection (bundle.trivializationAt b) b)
          (fun i => principalBundleLocalTangentLift (IB := IB) (IP := IP)
            (bundle.trivializationAt b) b (v i))) :=
  PrincipalTwoForm.selectedBaseForm_quotient (bundle := bundle)
    (connection.curvatureForm exterior).toForm b v

/-- A structure certificate for the exact derived curvature makes its pointwise base value agree
with every right-related representative and matching lift tuple. -/
theorem pointwiseBaseCurvature_quotient_eq_rightRelated
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
              (bundle.trivializationAt b) b (v i)))) :
    ((connection.pointwiseBaseCurvature exterior b) v).1 =
      AdjointBundle.mk torsor
        (torsor.rightAction
          (principalBundleLocalSection (bundle.trivializationAt b) b) g)
        ((connection.curvatureForm exterior).toForm
          (torsor.rightAction
            (principalBundleLocalSection (bundle.trivializationAt b) b) g)
          otherLifts) :=
  PrincipalTwoForm.selectedBaseForm_quotient_eq_rightRelated smoothBundle
    (connection.curvatureForm exterior).toForm certificate.horizontal
      certificate.right_ad_equivariant b v g otherLifts sameProjection

/-- The pointwise descended curvature remains alternating. -/
theorem pointwiseBaseCurvature_evalTwo_same
    (connection : PrincipalConnectionData smoothBundle)
    (exterior : PrincipalConnectionExteriorDerivativeData connection)
    (b : B) (v : TangentSpace IB b) :
    letI : AddCommGroup (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
      AdjointBundle.fiberAddCommGroup (I := IG) bundle b
    letI : Module ℝ (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
      AdjointBundle.fiberModule (I := IG) bundle b
    letI : TopologicalSpace (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
      AdjointBundle.fiberTopology (I := IG) bundle b
    (connection.pointwiseBaseCurvature exterior b) (fun _ => v) = 0 := by
  letI : AddCommGroup (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
    AdjointBundle.fiberAddCommGroup (I := IG) bundle b
  letI : Module ℝ (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
    AdjointBundle.fiberModule (I := IG) bundle b
  letI : TopologicalSpace (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
    AdjointBundle.fiberTopology (I := IG) bundle b
  exact AdjointBundle.DifferentialForm.evalTwo_same
    (connection.pointwiseBaseCurvature exterior) b v

end PrincipalConnectionData

end

end YangMills.Geometry
