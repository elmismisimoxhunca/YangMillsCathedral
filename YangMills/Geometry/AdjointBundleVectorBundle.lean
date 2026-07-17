/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Geometry.AdjointBundleFiberBundle
import YangMills.Geometry.SmoothAdjointBundleTransition
import Mathlib.Topology.VectorBundle.Basic

/-!
# A named topological vector bundle for the dependent adjoint bundle

Every transported dependent trivialization is linear for the previously selected fiber algebra. Its
Mathlib coordinate change is exactly the derived adjoint transition, whose operator-valued family is
smooth and hence continuous. These facts package the preserved quotient-induced topology and exact
transported atlas as a named `VectorBundle` value.

No `VectorPrebundle`, replacement topology, global instance, or smooth-vector-bundle mixin is
introduced here.
-/

namespace YangMills.Geometry

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

/-- Every transported designated dependent trivialization is linear for the named fiber algebra. -/
theorem AdjointBundle.dependentModelBundleTrivialization_isLinear
    (chart : PrincipalBundleLocalTrivialization torsor) :
    letI (b : B) : AddCommGroup (AdjointBundle.Fiber (I := I) (torsor := torsor) b) :=
      AdjointBundle.fiberAddCommGroup (I := I) bundle b
    letI (b : B) : Module ℝ (AdjointBundle.Fiber (I := I) (torsor := torsor) b) :=
      AdjointBundle.fiberModule (I := I) bundle b
    letI : TopologicalSpace
        (Bundle.TotalSpace E (AdjointBundle.Fiber (I := I) (torsor := torsor))) :=
      AdjointBundle.dependentTotalSpaceTopology (I := I) (torsor := torsor)
    Bundle.Trivialization.IsLinear ℝ
      (AdjointBundle.dependentModelBundleTrivialization (I := I) bundle chart) := by
  letI (b : B) : AddCommGroup (AdjointBundle.Fiber (I := I) (torsor := torsor) b) :=
    AdjointBundle.fiberAddCommGroup (I := I) bundle b
  letI (b : B) : Module ℝ (AdjointBundle.Fiber (I := I) (torsor := torsor) b) :=
    AdjointBundle.fiberModule (I := I) bundle b
  letI : TopologicalSpace
      (Bundle.TotalSpace E (AdjointBundle.Fiber (I := I) (torsor := torsor))) :=
    AdjointBundle.dependentTotalSpaceTopology (I := I) (torsor := torsor)
  constructor
  intro b hb
  let L := AdjointBundle.fiberModelLinearEquiv (I := I) bundle chart hb
  have coordinate_eq :
      (fun x : AdjointBundle.Fiber (I := I) (torsor := torsor) b =>
        ((AdjointBundle.dependentModelBundleTrivialization (I := I) bundle chart)
          ⟨b, x⟩).2) = L := by
    funext x
    exact (AdjointBundle.fiberModelLinearEquiv_apply (I := I) bundle chart hb x).symm
  rw [coordinate_eq]
  exact L.isLinear

/-- Mathlib's first-to-second coordinate change for the dependent trivializations is exactly the
previously derived continuous-linear adjoint transition, in the same direction. -/
theorem AdjointBundle.dependentModelBundleTrivialization_coordChangeL
    (first second : PrincipalBundleLocalTrivialization torsor)
    {b : B} (hb : b ∈ first.baseSet ∩ second.baseSet) :
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
    Bundle.Trivialization.coordChangeL ℝ firstTriv secondTriv b =
      adjointBundleTransitionEquiv (IG := I) first second b := by
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
  ext X
  rw [Bundle.Trivialization.coordChangeL_apply' firstTriv secondTriv hb X]
  change (AdjointBundle.modelBundleTrivialization (I := I) bundle second
    ((AdjointBundle.modelBundleTrivialization (I := I) bundle first).toOpenPartialHomeomorph.symm
      (b, X))).2 = _
  rw [adjointBundleModelTransition_eq (I := I) bundle first second (b, X)]
  · rfl
  · rw [adjointBundleOverlapDomain_eq (I := I) first second]
    exact ⟨hb, Set.mem_univ X⟩

universe uEB uHB uEP uHP

/-- Named Mathlib vector-bundle structure on the preserved dependent adjoint bundle. Operator-norm
continuity is derived from the smooth principal-bundle transition data. -/
@[reducible]
def AdjointBundle.dependentVectorBundle
    {EB : Type uEB} {HB : Type uHB}
    [NormedAddCommGroup EB] [NormedSpace ℝ EB] [TopologicalSpace HB]
    {EP : Type uEP} {HP : Type uHP}
    [NormedAddCommGroup EP] [NormedSpace ℝ EP] [TopologicalSpace HP]
    {IB : ModelWithCorners ℝ EB HB} {IP : ModelWithCorners ℝ EP HP}
    [ChartedSpace HB B] [IsManifold IB ∞ B]
    [ChartedSpace HP P] [IsManifold IP ∞ P]
    (smoothBundle : SmoothPrincipalBundleData IB I IP torsor bundle) :
    letI (b : B) : AddCommGroup (AdjointBundle.Fiber (I := I) (torsor := torsor) b) :=
      AdjointBundle.fiberAddCommGroup (I := I) bundle b
    letI (b : B) : Module ℝ (AdjointBundle.Fiber (I := I) (torsor := torsor) b) :=
      AdjointBundle.fiberModule (I := I) bundle b
    letI (b : B) : TopologicalSpace (AdjointBundle.Fiber (I := I) (torsor := torsor) b) :=
      AdjointBundle.fiberTopology (I := I) bundle b
    letI : TopologicalSpace
        (Bundle.TotalSpace E (AdjointBundle.Fiber (I := I) (torsor := torsor))) :=
      AdjointBundle.dependentTotalSpaceTopology (I := I) (torsor := torsor)
    letI : FiberBundle E (AdjointBundle.Fiber (I := I) (torsor := torsor)) :=
      AdjointBundle.dependentFiberBundle (I := I) bundle
    VectorBundle ℝ E (AdjointBundle.Fiber (I := I) (torsor := torsor)) := by
  letI (b : B) : AddCommGroup (AdjointBundle.Fiber (I := I) (torsor := torsor) b) :=
    AdjointBundle.fiberAddCommGroup (I := I) bundle b
  letI (b : B) : Module ℝ (AdjointBundle.Fiber (I := I) (torsor := torsor) b) :=
    AdjointBundle.fiberModule (I := I) bundle b
  letI (b : B) : TopologicalSpace (AdjointBundle.Fiber (I := I) (torsor := torsor) b) :=
    AdjointBundle.fiberTopology (I := I) bundle b
  letI : TopologicalSpace
      (Bundle.TotalSpace E (AdjointBundle.Fiber (I := I) (torsor := torsor))) :=
    AdjointBundle.dependentTotalSpaceTopology (I := I) (torsor := torsor)
  letI : FiberBundle E (AdjointBundle.Fiber (I := I) (torsor := torsor)) :=
    AdjointBundle.dependentFiberBundle (I := I) bundle
  exact
    { trivialization_linear' := by
        rintro e ⟨chart, _chart_mem, rfl⟩
        exact AdjointBundle.dependentModelBundleTrivialization_isLinear (I := I) bundle chart
      continuousOn_coordChange' := by
        rintro e e' ⟨first, first_mem, rfl⟩ ⟨second, second_mem, rfl⟩
        letI : Bundle.Trivialization.IsLinear ℝ
            (AdjointBundle.dependentModelBundleTrivialization (I := I) bundle first) :=
          AdjointBundle.dependentModelBundleTrivialization_isLinear (I := I) bundle first
        letI : Bundle.Trivialization.IsLinear ℝ
            (AdjointBundle.dependentModelBundleTrivialization (I := I) bundle second) :=
          AdjointBundle.dependentModelBundleTrivialization_isLinear (I := I) bundle second
        have smooth := adjointBundleTransitionEquiv_contMDiffOn smoothBundle
          first second first_mem second_mem
        refine smooth.continuousOn.congr ?_
        intro b hb
        exact congrArg ContinuousLinearEquiv.toContinuousLinearMap
          (AdjointBundle.dependentModelBundleTrivialization_coordChangeL
            (I := I) bundle first second hb) }

end

end YangMills.Geometry
