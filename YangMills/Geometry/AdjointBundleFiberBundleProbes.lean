/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Geometry.AdjointBundleFiberBundle

/-!
# Hostile probes for the topology-coherent dependent adjoint fiber bundle
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

/-- No fiber inclusion may induce a topology different from its selected-coordinate topology. -/
theorem noninducing_adjointBundle_fiberInclusion_blocked (b : B)
    (failure :
      letI : TopologicalSpace (AdjointBundle.Fiber (I := I) (torsor := torsor) b) :=
        AdjointBundle.fiberTopology (I := I) bundle b
      letI : TopologicalSpace
          (Bundle.TotalSpace E (AdjointBundle.Fiber (I := I) (torsor := torsor))) :=
        AdjointBundle.dependentTotalSpaceTopology (I := I) (torsor := torsor)
      ¬Topology.IsInducing (@Bundle.TotalSpace.mk B E
        (AdjointBundle.Fiber (I := I) (torsor := torsor)) b)) : False := by
  letI : TopologicalSpace (AdjointBundle.Fiber (I := I) (torsor := torsor) b) :=
    AdjointBundle.fiberTopology (I := I) bundle b
  letI : TopologicalSpace
      (Bundle.TotalSpace E (AdjointBundle.Fiber (I := I) (torsor := torsor))) :=
    AdjointBundle.dependentTotalSpaceTopology (I := I) (torsor := torsor)
  exact failure (AdjointBundle.isInducing_totalSpaceMk (I := I) bundle b)

/-- The named fiber bundle must select the transported principal chart at each base point. -/
theorem replacement_adjointBundle_fiberBundleChart_blocked (b : B)
    (mismatch :
      letI : TopologicalSpace
          (Bundle.TotalSpace E (AdjointBundle.Fiber (I := I) (torsor := torsor))) :=
        AdjointBundle.dependentTotalSpaceTopology (I := I) (torsor := torsor)
      letI (x : B) : TopologicalSpace
          (AdjointBundle.Fiber (I := I) (torsor := torsor) x) :=
        AdjointBundle.fiberTopology (I := I) bundle x
      letI : FiberBundle E (AdjointBundle.Fiber (I := I) (torsor := torsor)) :=
        AdjointBundle.dependentFiberBundle (I := I) bundle
      FiberBundle.trivializationAt E
          (AdjointBundle.Fiber (I := I) (torsor := torsor)) b ≠
        AdjointBundle.dependentModelBundleTrivialization (I := I) bundle
          (bundle.trivializationAt b)) : False := by
  letI : TopologicalSpace
      (Bundle.TotalSpace E (AdjointBundle.Fiber (I := I) (torsor := torsor))) :=
    AdjointBundle.dependentTotalSpaceTopology (I := I) (torsor := torsor)
  letI (x : B) : TopologicalSpace
      (AdjointBundle.Fiber (I := I) (torsor := torsor) x) :=
    AdjointBundle.fiberTopology (I := I) bundle x
  letI : FiberBundle E (AdjointBundle.Fiber (I := I) (torsor := torsor)) :=
    AdjointBundle.dependentFiberBundle (I := I) bundle
  exact mismatch rfl

/-- The selected transported chart cannot be absent from the named fiber-bundle atlas. -/
theorem missing_adjointBundle_selectedChartFromAtlas_blocked (b : B)
    (missing :
      letI : TopologicalSpace
          (Bundle.TotalSpace E (AdjointBundle.Fiber (I := I) (torsor := torsor))) :=
        AdjointBundle.dependentTotalSpaceTopology (I := I) (torsor := torsor)
      letI (x : B) : TopologicalSpace
          (AdjointBundle.Fiber (I := I) (torsor := torsor) x) :=
        AdjointBundle.fiberTopology (I := I) bundle x
      letI : FiberBundle E (AdjointBundle.Fiber (I := I) (torsor := torsor)) :=
        AdjointBundle.dependentFiberBundle (I := I) bundle
      AdjointBundle.dependentModelBundleTrivialization (I := I) bundle
          (bundle.trivializationAt b) ∉
        FiberBundle.trivializationAtlas E
          (AdjointBundle.Fiber (I := I) (torsor := torsor))) : False := by
  letI : TopologicalSpace
      (Bundle.TotalSpace E (AdjointBundle.Fiber (I := I) (torsor := torsor))) :=
    AdjointBundle.dependentTotalSpaceTopology (I := I) (torsor := torsor)
  letI (x : B) : TopologicalSpace
      (AdjointBundle.Fiber (I := I) (torsor := torsor) x) :=
    AdjointBundle.fiberTopology (I := I) bundle x
  letI : FiberBundle E (AdjointBundle.Fiber (I := I) (torsor := torsor)) :=
    AdjointBundle.dependentFiberBundle (I := I) bundle
  exact missing ⟨bundle.trivializationAt b, bundle.trivializationAt_mem_atlas b, rfl⟩

end

end YangMills.Geometry.Probes
