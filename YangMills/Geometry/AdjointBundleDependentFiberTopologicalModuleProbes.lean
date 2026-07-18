/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Geometry.AdjointBundleDependentFiberTopologicalModule

/-!
# Hostile probes for dependent adjoint-fiber topological modules

These probes install the named structures only locally and expose continuity of the exact
quotient-fiber addition, negation, and scalar multiplication. They also lock those operations to the
selected quotient-derived coordinate.
-/

namespace YangMills.Geometry.AdjointBundleDependentFiberTopologicalModule.Probes

open scoped Manifold ContDiff Bundle Topology

universe uEG uHG uEB uHB uG uB uP

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
    (bundle : TopologicalPrincipalBundleData torsor)

/-- Addition in the exact dependent quotient fiber is jointly continuous. -/
theorem exact_fiber_addition_continuous (b : B) :
    letI : AddCommGroup (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
      AdjointBundle.fiberAddCommGroup (I := IG) bundle b
    letI : Module ℝ (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
      AdjointBundle.fiberModule (I := IG) bundle b
    letI : TopologicalSpace (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
      AdjointBundle.fiberTopology (I := IG) bundle b
    Continuous
      (fun pair : (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) ×
          (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) => pair.1 + pair.2) := by
  letI : AddCommGroup (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
    AdjointBundle.fiberAddCommGroup (I := IG) bundle b
  letI : Module ℝ (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
    AdjointBundle.fiberModule (I := IG) bundle b
  letI : TopologicalSpace (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
    AdjointBundle.fiberTopology (I := IG) bundle b
  letI : IsTopologicalAddGroup (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
    AdjointBundle.fiberIsTopologicalAddGroup (IG := IG) bundle b
  exact continuous_add

/-- Negation in the exact dependent quotient fiber is continuous. -/
theorem exact_fiber_negation_continuous (b : B) :
    letI : AddCommGroup (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
      AdjointBundle.fiberAddCommGroup (I := IG) bundle b
    letI : Module ℝ (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
      AdjointBundle.fiberModule (I := IG) bundle b
    letI : TopologicalSpace (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
      AdjointBundle.fiberTopology (I := IG) bundle b
    Continuous
      (fun z : AdjointBundle.Fiber (I := IG) (torsor := torsor) b => -z) := by
  letI : AddCommGroup (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
    AdjointBundle.fiberAddCommGroup (I := IG) bundle b
  letI : Module ℝ (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
    AdjointBundle.fiberModule (I := IG) bundle b
  letI : TopologicalSpace (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
    AdjointBundle.fiberTopology (I := IG) bundle b
  letI : IsTopologicalAddGroup (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
    AdjointBundle.fiberIsTopologicalAddGroup (IG := IG) bundle b
  exact continuous_neg

/-- Scalar multiplication in the exact dependent quotient fiber is jointly continuous. -/
theorem exact_fiber_scalar_multiplication_continuous (b : B) :
    letI : AddCommGroup (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
      AdjointBundle.fiberAddCommGroup (I := IG) bundle b
    letI : Module ℝ (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
      AdjointBundle.fiberModule (I := IG) bundle b
    letI : TopologicalSpace (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
      AdjointBundle.fiberTopology (I := IG) bundle b
    Continuous
      (fun pair : ℝ × AdjointBundle.Fiber (I := IG) (torsor := torsor) b =>
        pair.1 • pair.2) := by
  letI : AddCommGroup (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
    AdjointBundle.fiberAddCommGroup (I := IG) bundle b
  letI : Module ℝ (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
    AdjointBundle.fiberModule (I := IG) bundle b
  letI : TopologicalSpace (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
    AdjointBundle.fiberTopology (I := IG) bundle b
  letI : ContinuousSMul ℝ (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
    AdjointBundle.fiberContinuousSMul (IG := IG) bundle b
  exact continuous_smul

/-- The selected exact coordinate preserves both addition and scalar multiplication. -/
theorem exact_coordinate_add_smul
    (b : B)
    (first second : AdjointBundle.Fiber (I := IG) (torsor := torsor) b)
    (scalar : ℝ) :
    letI : AddCommGroup (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
      AdjointBundle.fiberAddCommGroup (I := IG) bundle b
    letI : Module ℝ (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
      AdjointBundle.fiberModule (I := IG) bundle b
    letI : TopologicalSpace (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
      AdjointBundle.fiberTopology (I := IG) bundle b
    let coordinate := AdjointBundle.fiberModelContinuousLinearEquiv (IG := IG) bundle
      (bundle.trivializationAt b) (bundle.mem_baseSet_trivializationAt b)
    coordinate (first + second) = coordinate first + coordinate second ∧
      coordinate (scalar • first) = scalar • coordinate first := by
  letI : AddCommGroup (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
    AdjointBundle.fiberAddCommGroup (I := IG) bundle b
  letI : Module ℝ (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
    AdjointBundle.fiberModule (I := IG) bundle b
  letI : TopologicalSpace (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
    AdjointBundle.fiberTopology (I := IG) bundle b
  let coordinate := AdjointBundle.fiberModelContinuousLinearEquiv (IG := IG) bundle
    (bundle.trivializationAt b) (bundle.mem_baseSet_trivializationAt b)
  exact ⟨coordinate.map_add first second, coordinate.map_smul scalar first⟩

end

end YangMills.Geometry.AdjointBundleDependentFiberTopologicalModule.Probes
