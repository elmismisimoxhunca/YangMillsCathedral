/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Geometry.AdjointBundleVectorBundle
import Mathlib.Geometry.Manifold.VectorBundle.Basic

/-!
# Smooth vector-bundle transitions for the dependent adjoint bundle

The exact continuous-linear coordinate changes used by the named topological vector bundle are
already smooth on every designated overlap. They therefore supply Mathlib's
`ContMDiffVectorBundle ∞` mixin for the same named fiber algebra, preserved quotient-induced total
topology, and transported atlas.

This file installs no global instance and does not assert a concrete section, connection, curvature,
or Yang--Mills field.
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

/-- Named smooth-vector-bundle mixin for the exact dependent adjoint atlas. -/
@[reducible]
def AdjointBundle.dependentContMDiffVectorBundle :
    letI (b : B) : AddCommGroup (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
      AdjointBundle.fiberAddCommGroup (I := IG) bundle b
    letI (b : B) : Module ℝ (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
      AdjointBundle.fiberModule (I := IG) bundle b
    letI (b : B) : TopologicalSpace (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
      AdjointBundle.fiberTopology (I := IG) bundle b
    letI : TopologicalSpace
        (Bundle.TotalSpace EG (AdjointBundle.Fiber (I := IG) (torsor := torsor))) :=
      AdjointBundle.dependentTotalSpaceTopology (I := IG) (torsor := torsor)
    letI : FiberBundle EG (AdjointBundle.Fiber (I := IG) (torsor := torsor)) :=
      AdjointBundle.dependentFiberBundle (I := IG) bundle
    letI : VectorBundle ℝ EG (AdjointBundle.Fiber (I := IG) (torsor := torsor)) :=
      AdjointBundle.dependentVectorBundle (I := IG) bundle smoothBundle
    ContMDiffVectorBundle ∞ EG (AdjointBundle.Fiber (I := IG) (torsor := torsor)) IB := by
  letI (b : B) : AddCommGroup (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
    AdjointBundle.fiberAddCommGroup (I := IG) bundle b
  letI (b : B) : Module ℝ (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
    AdjointBundle.fiberModule (I := IG) bundle b
  letI (b : B) : TopologicalSpace (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
    AdjointBundle.fiberTopology (I := IG) bundle b
  letI : TopologicalSpace
      (Bundle.TotalSpace EG (AdjointBundle.Fiber (I := IG) (torsor := torsor))) :=
    AdjointBundle.dependentTotalSpaceTopology (I := IG) (torsor := torsor)
  letI : FiberBundle EG (AdjointBundle.Fiber (I := IG) (torsor := torsor)) :=
    AdjointBundle.dependentFiberBundle (I := IG) bundle
  letI : VectorBundle ℝ EG (AdjointBundle.Fiber (I := IG) (torsor := torsor)) :=
    AdjointBundle.dependentVectorBundle (I := IG) bundle smoothBundle
  exact
    { contMDiffOn_coordChangeL := by
        rintro e e' ⟨first, first_mem, rfl⟩ ⟨second, second_mem, rfl⟩
        letI : Bundle.Trivialization.IsLinear ℝ
            (AdjointBundle.dependentModelBundleTrivialization (I := IG) bundle first) :=
          AdjointBundle.dependentModelBundleTrivialization_isLinear (I := IG) bundle first
        letI : Bundle.Trivialization.IsLinear ℝ
            (AdjointBundle.dependentModelBundleTrivialization (I := IG) bundle second) :=
          AdjointBundle.dependentModelBundleTrivialization_isLinear (I := IG) bundle second
        have smooth := adjointBundleTransitionEquiv_contMDiffOn smoothBundle
          first second first_mem second_mem
        refine smooth.congr ?_
        intro b hb
        exact congrArg ContinuousLinearEquiv.toContinuousLinearMap
          (AdjointBundle.dependentModelBundleTrivialization_coordChangeL
            (I := IG) bundle first second hb) }

end

end YangMills.Geometry
