/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Geometry.AdjointBundlePrincipalCovariantDerivative

/-!
# Smooth same-connection adjoint covariant derivatives

The preceding interface ties Mathlib's intrinsic covariant derivative to the exact principal
connection by the local `d + ad(A)` formula. This module adds Mathlib's standard `C∞` regularity:
a smooth adjoint section is sent to a smooth section of the derivative bundle.

This remains uninhabited acceptance data. It neither constructs a derivative nor extends it to
adjoint-valued differential forms or positive-order curvature tensors.
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

/-- Mathlib's `C∞` covariant-derivative regularity specialized to the exact dependent adjoint
bundle and its named smooth vector-bundle structure. -/
def AdjointBundle.CovariantDerivative.IsSmooth
    (covariantDerivative : AdjointBundle.CovariantDerivative
      (IG := IG) (IB := IB) bundle) : Prop :=
  letI (b : B) : AddCommGroup (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
    AdjointBundle.fiberAddCommGroup (I := IG) bundle b
  letI (b : B) : Module ℝ (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
    AdjointBundle.fiberModule (I := IG) bundle b
  letI (b : B) : TopologicalSpace (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
    AdjointBundle.fiberTopology (I := IG) bundle b
  letI (b : B) : IsTopologicalAddGroup
      (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
    AdjointBundle.fiberIsTopologicalAddGroup (IG := IG) bundle b
  letI (b : B) : ContinuousSMul ℝ
      (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
    AdjointBundle.fiberContinuousSMul (IG := IG) bundle b
  letI : TopologicalSpace
      (Bundle.TotalSpace EG (AdjointBundle.Fiber (I := IG) (torsor := torsor))) :=
    AdjointBundle.dependentTotalSpaceTopology (I := IG) (torsor := torsor)
  letI : FiberBundle EG (AdjointBundle.Fiber (I := IG) (torsor := torsor)) :=
    AdjointBundle.dependentFiberBundle (I := IG) bundle
  letI : VectorBundle ℝ EG (AdjointBundle.Fiber (I := IG) (torsor := torsor)) :=
    AdjointBundle.dependentVectorBundle (I := IG) bundle smoothBundle
  _root_.CovariantDerivative.ContMDiffCovariantDerivative covariantDerivative ∞

/-- Same-connection adjoint covariant-derivative data strengthened by `C∞` output regularity. -/
structure SmoothPrincipalConnectionAdjointCovariantDerivativeData
    (connection : PrincipalConnectionData smoothBundle) where
  /-- Exact Mathlib derivative and local `d + ad(A)` connection formula. -/
  toCovariantDerivativeData :
    PrincipalConnectionAdjointCovariantDerivativeData connection
  /-- Smooth adjoint sections have smooth derivative sections. -/
  smooth : AdjointBundle.CovariantDerivative.IsSmooth
    (smoothBundle := smoothBundle) toCovariantDerivativeData.covariantDerivative

/-- The stored Mathlib regularity gives an exact smooth total-space section of the derivative
bundle for every exact smooth adjoint section. -/
theorem SmoothPrincipalConnectionAdjointCovariantDerivativeData.smooth_output
    {connection : PrincipalConnectionData smoothBundle}
    (data : SmoothPrincipalConnectionAdjointCovariantDerivativeData connection)
    (adjointSection : AdjointBundle.Section (IG := IG) (torsor := torsor))
    (section_smooth : AdjointBundle.Section.IsSmooth smoothBundle adjointSection) :
    letI (b : B) : AddCommGroup (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
      AdjointBundle.fiberAddCommGroup (I := IG) bundle b
    letI (b : B) : Module ℝ (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
      AdjointBundle.fiberModule (I := IG) bundle b
    letI (b : B) : TopologicalSpace (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
      AdjointBundle.fiberTopology (I := IG) bundle b
    letI (b : B) : IsTopologicalAddGroup
        (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
      AdjointBundle.fiberIsTopologicalAddGroup (IG := IG) bundle b
    letI (b : B) : ContinuousSMul ℝ
        (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
      AdjointBundle.fiberContinuousSMul (IG := IG) bundle b
    letI : TopologicalSpace
        (Bundle.TotalSpace EG (AdjointBundle.Fiber (I := IG) (torsor := torsor))) :=
      AdjointBundle.dependentTotalSpaceTopology (I := IG) (torsor := torsor)
    letI : FiberBundle EG (AdjointBundle.Fiber (I := IG) (torsor := torsor)) :=
      AdjointBundle.dependentFiberBundle (I := IG) bundle
    letI : VectorBundle ℝ EG (AdjointBundle.Fiber (I := IG) (torsor := torsor)) :=
      AdjointBundle.dependentVectorBundle (I := IG) bundle smoothBundle
    let derivativeTotal : B →
        Bundle.TotalSpace (EB →L[ℝ] EG)
          (fun b => TangentSpace IB b →L[ℝ]
            AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
      fun b => ⟨b,
        data.toCovariantDerivativeData.covariantDerivative adjointSection b⟩
    ContMDiff IB (IB.prod (modelWithCornersSelf ℝ (EB →L[ℝ] EG))) ∞
      derivativeTotal := by
  letI (b : B) : AddCommGroup (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
    AdjointBundle.fiberAddCommGroup (I := IG) bundle b
  letI (b : B) : Module ℝ (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
    AdjointBundle.fiberModule (I := IG) bundle b
  letI (b : B) : TopologicalSpace (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
    AdjointBundle.fiberTopology (I := IG) bundle b
  letI (b : B) : IsTopologicalAddGroup
      (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
    AdjointBundle.fiberIsTopologicalAddGroup (IG := IG) bundle b
  letI (b : B) : ContinuousSMul ℝ
      (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
    AdjointBundle.fiberContinuousSMul (IG := IG) bundle b
  letI : TopologicalSpace
      (Bundle.TotalSpace EG (AdjointBundle.Fiber (I := IG) (torsor := torsor))) :=
    AdjointBundle.dependentTotalSpaceTopology (I := IG) (torsor := torsor)
  letI : FiberBundle EG (AdjointBundle.Fiber (I := IG) (torsor := torsor)) :=
    AdjointBundle.dependentFiberBundle (I := IG) bundle
  letI : VectorBundle ℝ EG (AdjointBundle.Fiber (I := IG) (torsor := torsor)) :=
    AdjointBundle.dependentVectorBundle (I := IG) bundle smoothBundle
  letI : _root_.CovariantDerivative.ContMDiffCovariantDerivative
      data.toCovariantDerivativeData.covariantDerivative ∞ := data.smooth
  have section_regular :
      ContMDiff IB (IB.prod (modelWithCornersSelf ℝ EG)) (∞ + 1)
        adjointSection.totalSpace := by
    simpa [AdjointBundle.Section.IsSmooth] using section_smooth
  have output :=
    (_root_.CovariantDerivative.ContMDiffCovariantDerivative.contMDiff
      (cov := data.toCovariantDerivativeData.covariantDerivative)
      (k := ∞)).contMDiff section_regular.contMDiffOn
  simpa [contMDiffOn_univ] using output

end

end YangMills.Geometry
