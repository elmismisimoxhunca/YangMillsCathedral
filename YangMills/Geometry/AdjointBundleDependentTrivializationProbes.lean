/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Geometry.AdjointBundleDependentTrivialization

/-!
# Hostile probes for dependent adjoint trivializations
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

/-- A dependent fiber topology cannot be disconnected from its selected exact coordinate. -/
theorem disconnected_adjointBundle_fiberTopology_blocked (b : B)
    (mismatch : AdjointBundle.fiberTopology (I := I) bundle b ≠
      TopologicalSpace.induced
        (AdjointBundle.selectedFiberModelEquiv (I := I) bundle b) inferInstance) : False :=
  mismatch rfl

/-- The selected fiber homeomorphism cannot use a replacement forward map. -/
theorem disconnected_adjointBundle_selectedFiberHomeomorph_blocked
    (b : B) (z : AdjointBundle.Fiber (I := I) (torsor := torsor) b)
    (mismatch : AdjointBundle.selectedFiberModelHomeomorph (I := I) bundle b z ≠
      AdjointBundle.selectedFiberModelEquiv (I := I) bundle b z) : False :=
  mismatch rfl

/-- Transport to the dependent total space cannot alter the quotient-derived chart coordinate. -/
theorem replacement_adjointBundle_dependentTrivialization_blocked
    (chart : PrincipalBundleLocalTrivialization torsor)
    (z : Bundle.TotalSpace E (AdjointBundle.Fiber (I := I) (torsor := torsor)))
    (mismatch : AdjointBundle.dependentModelBundleTrivialization
      (I := I) bundle chart z ≠
        AdjointBundle.modelBundleTrivialization (I := I) bundle chart
          (AdjointBundle.totalSpaceToQuotient (I := I) (torsor := torsor) z)) : False :=
  mismatch (AdjointBundle.dependentModelBundleTrivialization_apply
    (I := I) bundle chart z)

/-- Transported dependent trivializations cannot silently change their base domains. -/
theorem baseSetChanging_adjointBundle_dependentTrivialization_blocked
    (chart : PrincipalBundleLocalTrivialization torsor)
    (mismatch :
      letI : TopologicalSpace
          (Bundle.TotalSpace E (AdjointBundle.Fiber (I := I) (torsor := torsor))) :=
        AdjointBundle.dependentTotalSpaceTopology (I := I) (torsor := torsor)
      (AdjointBundle.dependentModelBundleTrivialization
        (I := I) bundle chart).baseSet ≠ chart.baseSet) : False := by
  letI : TopologicalSpace
      (Bundle.TotalSpace E (AdjointBundle.Fiber (I := I) (torsor := torsor))) :=
    AdjointBundle.dependentTotalSpaceTopology (I := I) (torsor := torsor)
  exact mismatch (AdjointBundle.dependentModelBundleTrivialization_baseSet
    (I := I) bundle chart)

end

end YangMills.Geometry.Probes
