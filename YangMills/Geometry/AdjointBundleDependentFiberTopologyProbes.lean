/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Geometry.AdjointBundleDependentFiberTopology

/-!
# Hostile probes for dependent-total-space topology coherence
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

omit [TopologicalSpace B] [IsTopologicalGroup G] in
/-- The named topology cannot differ from the topology induced by the exact forgetting map. -/
theorem disconnected_adjointBundle_dependentTopology_blocked
    (mismatch : AdjointBundle.dependentTotalSpaceTopology (I := I) (torsor := torsor) ≠
      TopologicalSpace.induced
        (AdjointBundle.totalSpaceToQuotient (I := I) (torsor := torsor)) inferInstance) : False :=
  mismatch rfl

omit [TopologicalSpace B] [IsTopologicalGroup G] in
/-- The topology-coherence homeomorphism cannot use a disconnected forward map. -/
theorem disconnected_adjointBundle_dependentHomeomorph_blocked
    (z : Bundle.TotalSpace E (AdjointBundle.Fiber (I := I) (torsor := torsor)))
    (mismatch : AdjointBundle.dependentTotalSpaceHomeomorphQuotient
      (I := I) (torsor := torsor) z ≠
        AdjointBundle.totalSpaceToQuotient (I := I) (torsor := torsor) z) : False :=
  mismatch (AdjointBundle.dependentTotalSpaceHomeomorphQuotient_apply
    (I := I) (torsor := torsor) z)

omit [TopologicalSpace B] [IsTopologicalGroup G] in
/-- The topology-coherence homeomorphism cannot move the bundle base. -/
theorem baseMoving_adjointBundle_dependentHomeomorph_blocked
    (z : Bundle.TotalSpace E (AdjointBundle.Fiber (I := I) (torsor := torsor)))
    (mismatch : AdjointBundle.projection torsor
      (AdjointBundle.dependentTotalSpaceHomeomorphQuotient
        (I := I) (torsor := torsor) z) ≠ z.proj) : False :=
  mismatch (AdjointBundle.projection_dependentTotalSpaceHomeomorphQuotient
    (I := I) (torsor := torsor) z)

omit [TopologicalSpace B] [IsTopologicalGroup G] in
/-- Under the named topology, forgetting to the quotient cannot fail continuity. -/
theorem discontinuous_adjointBundle_dependent_forgetting_blocked
    (discontinuous :
      letI : TopologicalSpace
          (Bundle.TotalSpace E (AdjointBundle.Fiber (I := I) (torsor := torsor))) :=
        AdjointBundle.dependentTotalSpaceTopology (I := I) (torsor := torsor)
      ¬Continuous (AdjointBundle.totalSpaceToQuotient (I := I) (torsor := torsor))) : False := by
  letI : TopologicalSpace
      (Bundle.TotalSpace E (AdjointBundle.Fiber (I := I) (torsor := torsor))) :=
    AdjointBundle.dependentTotalSpaceTopology (I := I) (torsor := torsor)
  exact discontinuous
    (AdjointBundle.dependentTotalSpaceHomeomorphQuotient
      (I := I) (torsor := torsor)).continuous

end

end YangMills.Geometry.Probes
