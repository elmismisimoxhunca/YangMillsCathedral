/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Geometry.AdjointBundleCurvatureDerivativeTensor

/-!
# Hostile probes for curvature-derivative tensor carriers

The probes expose the continuous multilinear/alternating shape and lock order zero to the exact
connection-derived descended curvature. They construct no positive-order derivative tensor.
-/

namespace YangMills.Geometry.AdjointBundleCurvatureDerivativeTensor.Probes

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

omit [IsManifold IB ∞ B] [FiniteDimensional ℝ EG] in
/-- Every order has a genuinely continuous map in its explicit derivative slots. The codomain type
retains the two alternating curvature slots in the exact dependent fiber. -/
theorem exact_derivative_slots_continuous
    (n : ℕ) (tensor : AdjointBundle.CurvatureDerivativeTensor
      (IG := IG) (IB := IB) bundle n) (b : B) :
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
    Continuous (tensor b) := by
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
  exact (tensor b).cont

omit [IsManifold IB ∞ B] [FiniteDimensional ℝ EG] in
/-- After fixing derivative slots, the remaining two curvature slots are jointly continuous. -/
theorem exact_curvature_slots_continuous
    (n : ℕ) (tensor : AdjointBundle.CurvatureDerivativeTensor
      (IG := IG) (IB := IB) bundle n) (b : B)
    (derivativeArguments : Fin n → TangentSpace IB b) :
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
    Continuous (tensor b derivativeArguments) := by
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
  exact (tensor b derivativeArguments).toContinuousMultilinearMap.cont

omit [IsManifold IB ∞ B] [FiniteDimensional ℝ EG] in
/-- Repeating the two curvature-slot vectors forces exact vanishing. -/
theorem repeated_curvature_slot_vanishes
    (n : ℕ) (tensor : AdjointBundle.CurvatureDerivativeTensor
      (IG := IG) (IB := IB) bundle n) (b : B)
    (derivativeArguments : Fin n → TangentSpace IB b)
    (curvatureArguments : Fin 2 → TangentSpace IB b)
    (repeated : curvatureArguments 0 = curvatureArguments 1) :
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
    tensor b derivativeArguments curvatureArguments = 0 := by
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
  exact (tensor b derivativeArguments).map_eq_zero_of_eq
    curvatureArguments repeated (by decide)

/-- The zero-order carrier evaluates to the exact pointwise descended curvature. -/
theorem exact_zero_order_curvature
    (connection : PrincipalConnectionData smoothBundle)
    (exterior : PrincipalConnectionExteriorDerivativeData connection)
    (certificate : PrincipalCurvatureStructureCertificate smoothBundle connection exterior)
    (b : B) (emptyArguments : Fin 0 → TangentSpace IB b) :
    (connection.curvatureDerivativeTensorZero exterior certificate b) emptyArguments =
      connection.pointwiseBaseCurvature exterior b :=
  connection.curvatureDerivativeTensorZero_apply exterior certificate b emptyArguments

/-- A caller-supplied unrelated two-form value cannot replace the exact zero-order anchor. -/
theorem unrelated_zero_order_anchor_blocked
    (connection : PrincipalConnectionData smoothBundle)
    (exterior : PrincipalConnectionExteriorDerivativeData connection)
    (certificate : PrincipalCurvatureStructureCertificate smoothBundle connection exterior)
    (b : B) (emptyArguments : Fin 0 → TangentSpace IB b) :
    letI : AddCommGroup (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
      AdjointBundle.fiberAddCommGroup (I := IG) bundle b
    letI : Module ℝ (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
      AdjointBundle.fiberModule (I := IG) bundle b
    letI : TopologicalSpace (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
      AdjointBundle.fiberTopology (I := IG) bundle b
    ∀ replacement : ContinuousAlternatingMap ℝ (TangentSpace IB b)
        (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) (Fin 2),
      replacement ≠ connection.pointwiseBaseCurvature exterior b →
      replacement ≠
        (connection.curvatureDerivativeTensorZero exterior certificate b) emptyArguments := by
  intro replacement mismatch
  rw [connection.curvatureDerivativeTensorZero_apply exterior certificate b emptyArguments]
  exact mismatch

/-- The zero-derivative-slot evaluation is independent of the unique empty argument tuple. -/
theorem zero_order_has_no_hidden_argument
    (connection : PrincipalConnectionData smoothBundle)
    (exterior : PrincipalConnectionExteriorDerivativeData connection)
    (certificate : PrincipalCurvatureStructureCertificate smoothBundle connection exterior)
    (b : B) (first second : Fin 0 → TangentSpace IB b) :
    (connection.curvatureDerivativeTensorZero exterior certificate b) first =
      (connection.curvatureDerivativeTensorZero exterior certificate b) second := by
  rw [connection.curvatureDerivativeTensorZero_apply exterior certificate b first,
    connection.curvatureDerivativeTensorZero_apply exterior certificate b second]

end

end YangMills.Geometry.AdjointBundleCurvatureDerivativeTensor.Probes
