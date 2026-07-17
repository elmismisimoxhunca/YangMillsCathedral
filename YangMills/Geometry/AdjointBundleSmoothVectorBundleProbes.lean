/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Geometry.AdjointBundleSmoothVectorBundle

/-!
# Hostile probes for the dependent adjoint smooth-vector-bundle mixin
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

/-- The named topological vector bundle cannot fail to carry the derived smooth transition mixin. -/
theorem missing_adjointBundle_smoothVectorBundleMixin_blocked
    (failure :
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
      ¬ContMDiffVectorBundle ∞ EG
        (AdjointBundle.Fiber (I := IG) (torsor := torsor)) IB) : False := by
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
  exact failure (AdjointBundle.dependentContMDiffVectorBundle smoothBundle)

/-- No ordered pair of designated atlas charts may have a nonsmooth exact continuous-linear
coordinate-change family. -/
theorem nonsmooth_adjointBundle_vectorCoordinateChange_blocked
    (first second : PrincipalBundleLocalTrivialization torsor)
    (first_mem : first ∈ bundle.trivializationAtlas)
    (second_mem : second ∈ bundle.trivializationAtlas)
    (failure :
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
      letI : ContMDiffVectorBundle ∞ EG
          (AdjointBundle.Fiber (I := IG) (torsor := torsor)) IB :=
        AdjointBundle.dependentContMDiffVectorBundle smoothBundle
      let firstTriv := AdjointBundle.dependentModelBundleTrivialization (I := IG) bundle first
      let secondTriv := AdjointBundle.dependentModelBundleTrivialization (I := IG) bundle second
      letI : MemTrivializationAtlas firstTriv := ⟨⟨first, first_mem, rfl⟩⟩
      letI : MemTrivializationAtlas secondTriv := ⟨⟨second, second_mem, rfl⟩⟩
      ¬ContMDiffOn IB 𝓘(ℝ, EG →L[ℝ] EG) ∞
        (fun b : B => (firstTriv.coordChangeL ℝ secondTriv b : EG →L[ℝ] EG))
        (first.baseSet ∩ second.baseSet)) : False := by
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
  letI : ContMDiffVectorBundle ∞ EG
      (AdjointBundle.Fiber (I := IG) (torsor := torsor)) IB :=
    AdjointBundle.dependentContMDiffVectorBundle smoothBundle
  let firstTriv := AdjointBundle.dependentModelBundleTrivialization (I := IG) bundle first
  let secondTriv := AdjointBundle.dependentModelBundleTrivialization (I := IG) bundle second
  letI : MemTrivializationAtlas firstTriv := ⟨⟨first, first_mem, rfl⟩⟩
  letI : MemTrivializationAtlas secondTriv := ⟨⟨second, second_mem, rfl⟩⟩
  exact failure (ContMDiffVectorBundle.contMDiffOn_coordChangeL firstTriv secondTriv)

end

end YangMills.Geometry.Probes
