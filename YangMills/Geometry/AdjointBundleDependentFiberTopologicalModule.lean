/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Geometry.AdjointBundleDifferentialForm

/-!
# Topological-module compatibility on dependent adjoint fibers

The quotient-derived topology and the transported real vector-space operations on each dependent
adjoint fiber were previously named separately. This module proves their compatibility by using the
exact selected fiber coordinate as a continuous linear equivalence with the Lie-algebra model.

The resulting `IsTopologicalAddGroup` and `ContinuousSMul` values are named and are intended for
local installation. No global dependent-fiber instance is introduced.
-/

namespace YangMills.Geometry

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

/-- The quotient-derived topology makes the transported additive group on each exact dependent
adjoint fiber a topological additive group. -/
@[reducible] noncomputable def AdjointBundle.fiberIsTopologicalAddGroup
    (bundle : TopologicalPrincipalBundleData torsor) (b : B) :
    letI : AddCommGroup (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
      AdjointBundle.fiberAddCommGroup (I := IG) bundle b
    letI : Module ℝ (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
      AdjointBundle.fiberModule (I := IG) bundle b
    letI : TopologicalSpace (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
      AdjointBundle.fiberTopology (I := IG) bundle b
    IsTopologicalAddGroup (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) := by
  letI : AddCommGroup (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
    AdjointBundle.fiberAddCommGroup (I := IG) bundle b
  letI : Module ℝ (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
    AdjointBundle.fiberModule (I := IG) bundle b
  letI : TopologicalSpace (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
    AdjointBundle.fiberTopology (I := IG) bundle b
  let coordinate := AdjointBundle.fiberModelContinuousLinearEquiv (IG := IG) bundle
    (bundle.trivializationAt b) (bundle.mem_baseSet_trivializationAt b)
  have continuous_add : Continuous
      (fun pair : (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) ×
          (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) => pair.1 + pair.2) := by
    have transported := coordinate.symm.continuous.comp
      ((coordinate.continuous.comp continuous_fst).add
        (coordinate.continuous.comp continuous_snd))
    convert transported using 1
    funext pair
    simp
  have continuous_neg : Continuous
      (fun z : AdjointBundle.Fiber (I := IG) (torsor := torsor) b => -z) := by
    have transported := coordinate.symm.continuous.comp coordinate.continuous.neg
    convert transported using 1
    funext z
    simp
  letI : ContinuousAdd (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
    ⟨continuous_add⟩
  letI : ContinuousNeg (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
    ⟨continuous_neg⟩
  exact ⟨⟩

/-- The quotient-derived topology makes scalar multiplication on each exact dependent adjoint fiber
continuous for the transported real module structure. -/
@[reducible] noncomputable def AdjointBundle.fiberContinuousSMul
    (bundle : TopologicalPrincipalBundleData torsor) (b : B) :
    letI : AddCommGroup (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
      AdjointBundle.fiberAddCommGroup (I := IG) bundle b
    letI : Module ℝ (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
      AdjointBundle.fiberModule (I := IG) bundle b
    letI : TopologicalSpace (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
      AdjointBundle.fiberTopology (I := IG) bundle b
    ContinuousSMul ℝ (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) := by
  letI : AddCommGroup (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
    AdjointBundle.fiberAddCommGroup (I := IG) bundle b
  letI : Module ℝ (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
    AdjointBundle.fiberModule (I := IG) bundle b
  letI : TopologicalSpace (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
    AdjointBundle.fiberTopology (I := IG) bundle b
  let coordinate := AdjointBundle.fiberModelContinuousLinearEquiv (IG := IG) bundle
    (bundle.trivializationAt b) (bundle.mem_baseSet_trivializationAt b)
  refine ⟨?_⟩
  have continuous_scalar : Continuous
      (fun pair : ℝ × AdjointBundle.Fiber (I := IG) (torsor := torsor) b => pair.1) :=
    continuous_fst
  have continuous_coordinate : Continuous
      (fun pair : ℝ × AdjointBundle.Fiber (I := IG) (torsor := torsor) b =>
        coordinate pair.2) :=
    coordinate.continuous.comp continuous_snd
  have transported := coordinate.symm.continuous.comp
    (continuous_scalar.smul continuous_coordinate)
  convert transported using 1
  funext pair
  simp

end

end YangMills.Geometry
