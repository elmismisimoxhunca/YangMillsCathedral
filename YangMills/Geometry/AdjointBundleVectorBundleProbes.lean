/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Geometry.AdjointBundleVectorBundle

/-!
# Hostile probes for the named dependent adjoint vector bundle
-/

namespace YangMills.Geometry.Probes

open Set
open scoped Manifold ContDiff Bundle Topology

universe uE uH uG uB uP

noncomputable section

variable
    {E : Type uE} {H : Type uH}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
    {G : Type uG} {B : Type uB} {P : Type uP}
    [Group G] [TopologicalSpace G] [TopologicalSpace B] [TopologicalSpace P]
    [IsTopologicalGroup G]
    {I : ModelWithCorners ℝ E H}
    [ChartedSpace H G] [LieGroup I ∞ G]
    {torsor : PrincipalBundleTorsorData G B P}
    (bundle : TopologicalPrincipalBundleData torsor)

/-- A designated transported chart cannot be nonlinear for the selected fiber algebra. -/
theorem nonlinear_adjointBundle_designatedChart_blocked
    (chart : PrincipalBundleLocalTrivialization torsor)
    (failure :
      letI (b : B) : AddCommGroup (AdjointBundle.Fiber (I := I) (torsor := torsor) b) :=
        AdjointBundle.fiberAddCommGroup (I := I) bundle b
      letI (b : B) : Module ℝ (AdjointBundle.Fiber (I := I) (torsor := torsor) b) :=
        AdjointBundle.fiberModule (I := I) bundle b
      letI : TopologicalSpace
          (Bundle.TotalSpace E (AdjointBundle.Fiber (I := I) (torsor := torsor))) :=
        AdjointBundle.dependentTotalSpaceTopology (I := I) (torsor := torsor)
      ¬Bundle.Trivialization.IsLinear ℝ
        (AdjointBundle.dependentModelBundleTrivialization (I := I) bundle chart)) : False := by
  letI (b : B) : AddCommGroup (AdjointBundle.Fiber (I := I) (torsor := torsor) b) :=
    AdjointBundle.fiberAddCommGroup (I := I) bundle b
  letI (b : B) : Module ℝ (AdjointBundle.Fiber (I := I) (torsor := torsor) b) :=
    AdjointBundle.fiberModule (I := I) bundle b
  letI : TopologicalSpace
      (Bundle.TotalSpace E (AdjointBundle.Fiber (I := I) (torsor := torsor))) :=
    AdjointBundle.dependentTotalSpaceTopology (I := I) (torsor := torsor)
  exact failure
    (AdjointBundle.dependentModelBundleTrivialization_isLinear (I := I) bundle chart)

/-- Mathlib's coordinate change cannot be replaced by a different operator or the reverse
transition on an overlap. -/
theorem wrong_adjointBundle_vectorCoordinateChange_blocked
    (first second : PrincipalBundleLocalTrivialization torsor)
    {b : B} (hb : b ∈ first.baseSet ∩ second.baseSet)
    (mismatch :
      letI (x : B) : AddCommGroup (AdjointBundle.Fiber (I := I) (torsor := torsor) x) :=
        AdjointBundle.fiberAddCommGroup (I := I) bundle x
      letI (x : B) : Module ℝ (AdjointBundle.Fiber (I := I) (torsor := torsor) x) :=
        AdjointBundle.fiberModule (I := I) bundle x
      letI : TopologicalSpace
          (Bundle.TotalSpace E (AdjointBundle.Fiber (I := I) (torsor := torsor))) :=
        AdjointBundle.dependentTotalSpaceTopology (I := I) (torsor := torsor)
      let firstTriv := AdjointBundle.dependentModelBundleTrivialization (I := I) bundle first
      let secondTriv := AdjointBundle.dependentModelBundleTrivialization (I := I) bundle second
      letI : Bundle.Trivialization.IsLinear ℝ firstTriv :=
        AdjointBundle.dependentModelBundleTrivialization_isLinear (I := I) bundle first
      letI : Bundle.Trivialization.IsLinear ℝ secondTriv :=
        AdjointBundle.dependentModelBundleTrivialization_isLinear (I := I) bundle second
      Bundle.Trivialization.coordChangeL ℝ firstTriv secondTriv b ≠
        adjointBundleTransitionEquiv (IG := I) first second b) : False := by
  letI (x : B) : AddCommGroup (AdjointBundle.Fiber (I := I) (torsor := torsor) x) :=
    AdjointBundle.fiberAddCommGroup (I := I) bundle x
  letI (x : B) : Module ℝ (AdjointBundle.Fiber (I := I) (torsor := torsor) x) :=
    AdjointBundle.fiberModule (I := I) bundle x
  letI : TopologicalSpace
      (Bundle.TotalSpace E (AdjointBundle.Fiber (I := I) (torsor := torsor))) :=
    AdjointBundle.dependentTotalSpaceTopology (I := I) (torsor := torsor)
  exact mismatch
    (AdjointBundle.dependentModelBundleTrivialization_coordChangeL
      (I := I) bundle first second hb)

universe uEB uHB uEP uHP

/-- Two designated atlas charts cannot have a discontinuous operator-valued coordinate change once
smooth principal-bundle data are supplied. -/
theorem discontinuous_adjointBundle_vectorCoordinateChange_blocked
    {EB : Type uEB} {HB : Type uHB}
    [NormedAddCommGroup EB] [NormedSpace ℝ EB] [TopologicalSpace HB]
    {EP : Type uEP} {HP : Type uHP}
    [NormedAddCommGroup EP] [NormedSpace ℝ EP] [TopologicalSpace HP]
    {IB : ModelWithCorners ℝ EB HB} {IP : ModelWithCorners ℝ EP HP}
    [ChartedSpace HB B] [IsManifold IB ∞ B]
    [ChartedSpace HP P] [IsManifold IP ∞ P]
    (smoothBundle : SmoothPrincipalBundleData IB I IP torsor bundle)
    (first second : PrincipalBundleLocalTrivialization torsor)
    (first_mem : first ∈ bundle.trivializationAtlas)
    (second_mem : second ∈ bundle.trivializationAtlas)
    (failure :
      letI (x : B) : AddCommGroup (AdjointBundle.Fiber (I := I) (torsor := torsor) x) :=
        AdjointBundle.fiberAddCommGroup (I := I) bundle x
      letI (x : B) : Module ℝ (AdjointBundle.Fiber (I := I) (torsor := torsor) x) :=
        AdjointBundle.fiberModule (I := I) bundle x
      letI (x : B) : TopologicalSpace (AdjointBundle.Fiber (I := I) (torsor := torsor) x) :=
        AdjointBundle.fiberTopology (I := I) bundle x
      letI : TopologicalSpace
          (Bundle.TotalSpace E (AdjointBundle.Fiber (I := I) (torsor := torsor))) :=
        AdjointBundle.dependentTotalSpaceTopology (I := I) (torsor := torsor)
      letI : FiberBundle E (AdjointBundle.Fiber (I := I) (torsor := torsor)) :=
        AdjointBundle.dependentFiberBundle (I := I) bundle
      letI : VectorBundle ℝ E (AdjointBundle.Fiber (I := I) (torsor := torsor)) :=
        AdjointBundle.dependentVectorBundle (I := I) bundle smoothBundle
      let firstTriv := AdjointBundle.dependentModelBundleTrivialization (I := I) bundle first
      let secondTriv := AdjointBundle.dependentModelBundleTrivialization (I := I) bundle second
      letI : MemTrivializationAtlas firstTriv := ⟨⟨first, first_mem, rfl⟩⟩
      letI : MemTrivializationAtlas secondTriv := ⟨⟨second, second_mem, rfl⟩⟩
      ¬ContinuousOn (fun b =>
          (Bundle.Trivialization.coordChangeL ℝ firstTriv secondTriv b : E →L[ℝ] E))
        (first.baseSet ∩ second.baseSet)) : False := by
  letI (x : B) : AddCommGroup (AdjointBundle.Fiber (I := I) (torsor := torsor) x) :=
    AdjointBundle.fiberAddCommGroup (I := I) bundle x
  letI (x : B) : Module ℝ (AdjointBundle.Fiber (I := I) (torsor := torsor) x) :=
    AdjointBundle.fiberModule (I := I) bundle x
  letI (x : B) : TopologicalSpace (AdjointBundle.Fiber (I := I) (torsor := torsor) x) :=
    AdjointBundle.fiberTopology (I := I) bundle x
  letI : TopologicalSpace
      (Bundle.TotalSpace E (AdjointBundle.Fiber (I := I) (torsor := torsor))) :=
    AdjointBundle.dependentTotalSpaceTopology (I := I) (torsor := torsor)
  letI : FiberBundle E (AdjointBundle.Fiber (I := I) (torsor := torsor)) :=
    AdjointBundle.dependentFiberBundle (I := I) bundle
  letI : VectorBundle ℝ E (AdjointBundle.Fiber (I := I) (torsor := torsor)) :=
    AdjointBundle.dependentVectorBundle (I := I) bundle smoothBundle
  let firstTriv := AdjointBundle.dependentModelBundleTrivialization (I := I) bundle first
  let secondTriv := AdjointBundle.dependentModelBundleTrivialization (I := I) bundle second
  letI : MemTrivializationAtlas firstTriv := ⟨⟨first, first_mem, rfl⟩⟩
  letI : MemTrivializationAtlas secondTriv := ⟨⟨second, second_mem, rfl⟩⟩
  exact failure (VectorBundle.continuousOn_coordChange' firstTriv secondTriv)

end

end YangMills.Geometry.Probes
