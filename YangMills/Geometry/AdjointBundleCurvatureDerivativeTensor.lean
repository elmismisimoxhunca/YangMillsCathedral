/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Geometry.AdjointBundleDependentFiberTopologicalModule
import YangMills.Geometry.PrincipalCurvatureSmoothDescent
import Mathlib.Topology.Algebra.Module.Multilinear.Basic

/-!
# Tensor carrier for covariant derivatives of adjoint curvature

Clay's local-observable language includes curvature and its covariant derivatives. Before an
intrinsic connection-induced derivative can be constructed, its output needs an honest dependent
carrier. An order-`n` tensor here is continuously multilinear in `n` derivative slots and remains a
continuous alternating two-form in the curvature slots, valued in the exact dependent adjoint
fiber.

Only order zero is populated: it is definitionally anchored to the exact smoothly descended
curvature of one connection/exterior/certificate chain. Positive-order tensors and a recursive
covariant-derivative operation are deliberately absent, so this module does not claim to have
constructed a covariant derivative tower or Bianchi identity.
-/

namespace YangMills.Geometry

open scoped Manifold ContDiff Bundle Topology

universe uEG uHG uEB uHB uEP uHP uG uB uP

noncomputable section

variable
    {EG : Type uEG} {HG : Type uHG}
    [NormedAddCommGroup EG] [NormedSpace ℝ EG] [TopologicalSpace HG]
    {EB : Type uEB} {HB : Type uHB}
    [NormedAddCommGroup EB] [NormedSpace ℝ EB] [TopologicalSpace HB]
    {G : Type uG} {B : Type uB} {P : Type uP}
    [Group G] [TopologicalSpace G] [TopologicalSpace B] [TopologicalSpace P]
    [IsTopologicalGroup G]
    {IG : ModelWithCorners ℝ EG HG}
    {IB : ModelWithCorners ℝ EB HB}
    [ChartedSpace HG G] [LieGroup IG ∞ G]
    [ChartedSpace HB B]
    {torsor : PrincipalBundleTorsorData G B P}

/-- Pointwise tensor shape of the `n`th covariant derivative of an adjoint-valued curvature
2-form. This is a carrier only; no derivative operation is hidden in the definition. -/
def AdjointBundle.CurvatureDerivativeTensor
    (bundle : TopologicalPrincipalBundleData torsor) (n : ℕ) :=
  (b : B) →
    letI : AddCommGroup (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
      AdjointBundle.fiberAddCommGroup (I := IG) bundle b
    letI : Module ℝ (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
      AdjointBundle.fiberModule (I := IG) bundle b
    letI : TopologicalSpace (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
      AdjointBundle.fiberTopology (I := IG) bundle b
    letI : IsTopologicalAddGroup
        (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
      AdjointBundle.fiberIsTopologicalAddGroup (IG := IG) bundle b
    letI : ContinuousSMul ℝ
        (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
      AdjointBundle.fiberContinuousSMul (IG := IG) bundle b
    ContinuousMultilinearMap ℝ (fun _ : Fin n => TangentSpace IB b)
      (ContinuousAlternatingMap ℝ (TangentSpace IB b)
        (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) (Fin 2))

/-- Embed an exact adjoint-valued two-form as the unique zero-derivative-slot tensor. -/
noncomputable def AdjointBundle.DifferentialForm.toCurvatureDerivativeTensorZero
    (bundle : TopologicalPrincipalBundleData torsor)
    (form : AdjointBundle.DifferentialForm (IG := IG) (IB := IB) bundle 2) :
    AdjointBundle.CurvatureDerivativeTensor (IG := IG) (IB := IB) bundle 0 :=
  fun b => by
    letI : AddCommGroup (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
      AdjointBundle.fiberAddCommGroup (I := IG) bundle b
    letI : Module ℝ (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
      AdjointBundle.fiberModule (I := IG) bundle b
    letI : TopologicalSpace (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
      AdjointBundle.fiberTopology (I := IG) bundle b
    letI : IsTopologicalAddGroup
        (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
      AdjointBundle.fiberIsTopologicalAddGroup (IG := IG) bundle b
    letI : ContinuousSMul ℝ
        (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
      AdjointBundle.fiberContinuousSMul (IG := IG) bundle b
    exact ContinuousMultilinearMap.constOfIsEmpty ℝ
      (fun _ : Fin 0 => TangentSpace IB b) (form b)

/-- Evaluating the zero-slot embedding returns the unchanged two-form at that base point. -/
@[simp]
theorem AdjointBundle.DifferentialForm.toCurvatureDerivativeTensorZero_apply
    (bundle : TopologicalPrincipalBundleData torsor)
    (form : AdjointBundle.DifferentialForm (IG := IG) (IB := IB) bundle 2)
    (b : B) (emptyArguments : Fin 0 → TangentSpace IB b) :
    (AdjointBundle.DifferentialForm.toCurvatureDerivativeTensorZero
      (IG := IG) (IB := IB) bundle form b) emptyArguments = form b :=
  rfl

variable
    {EP : Type uEP} {HP : Type uHP}
    [NormedAddCommGroup EP] [NormedSpace ℝ EP] [TopologicalSpace HP]
    {IP : ModelWithCorners ℝ EP HP}
    [IsManifold IB ∞ B]
    [ChartedSpace HP P] [IsManifold IP ∞ P]
    {bundle : TopologicalPrincipalBundleData torsor}
    {smoothBundle : SmoothPrincipalBundleData IB IG IP torsor bundle}
    [FiniteDimensional ℝ EG]

namespace PrincipalConnectionData

/-- The zero-order curvature-derivative tensor is the exact smoothly descended curvature of the
same connection, certified exterior derivative, and structural certificate. -/
noncomputable def curvatureDerivativeTensorZero
    (connection : PrincipalConnectionData smoothBundle)
    (exterior : PrincipalConnectionExteriorDerivativeData connection)
    (certificate : PrincipalCurvatureStructureCertificate smoothBundle connection exterior) :
    AdjointBundle.CurvatureDerivativeTensor (IG := IG) (IB := IB) bundle 0 :=
  AdjointBundle.DifferentialForm.toCurvatureDerivativeTensorZero
    (IG := IG) (IB := IB) bundle
    (connection.smoothBaseCurvature exterior certificate).toForm

/-- Evaluation exposes the unchanged exact pointwise descended curvature. -/
@[simp]
theorem curvatureDerivativeTensorZero_apply
    (connection : PrincipalConnectionData smoothBundle)
    (exterior : PrincipalConnectionExteriorDerivativeData connection)
    (certificate : PrincipalCurvatureStructureCertificate smoothBundle connection exterior)
    (b : B) (emptyArguments : Fin 0 → TangentSpace IB b) :
    (connection.curvatureDerivativeTensorZero exterior certificate b) emptyArguments =
      connection.pointwiseBaseCurvature exterior b :=
  rfl

end PrincipalConnectionData

end

end YangMills.Geometry
