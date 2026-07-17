/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Geometry.AdjointBundleLocalTrivialization

/-!
# Hostile probes for topological adjoint-bundle trivializations
-/

namespace YangMills.Geometry.Probes

open Set
open scoped Manifold ContDiff

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
    (chart : PrincipalBundleLocalTrivialization torsor)
    (adjointRegularity : YangMills.Mathematics.ContinuousLieGroupAdjointData
      (I := I) (G := G))

/-- A certified local coordinate cannot fail continuity on its natural associated source. -/
theorem discontinuous_adjointBundle_localCoordinate_blocked
    (bundle : TopologicalPrincipalBundleData torsor)
    (adjointRegularity : YangMills.Mathematics.ContinuousLieGroupAdjointData
      (I := I) (G := G))
    (discontinuous : ¬ContinuousOn (AdjointBundle.localCoordinate (I := I) chart)
      (AdjointBundle.localSource (I := I) chart)) : False :=
  discontinuous (AdjointBundle.localCoordinate_continuousOn chart bundle adjointRegularity)

omit [IsTopologicalGroup G] in
/-- The inverse coordinate map cannot fail continuity on `baseSet × g`. -/
theorem discontinuous_adjointBundle_localInverse_blocked
    (discontinuous : ¬ContinuousOn
      (AdjointBundle.localCoordinateInverse (I := I) chart)
      (AdjointBundle.localTarget (I := I) chart)) : False :=
  discontinuous (AdjointBundle.localCoordinateInverse_continuousOn chart)

/-- The packaged partial homeomorphism cannot silently use a smaller or unrelated source. -/
theorem malformed_adjointBundle_trivialization_source_blocked
    (mismatch : (AdjointBundle.localTrivialization (I := I) chart bundle adjointRegularity).source ≠
      AdjointBundle.projection torsor ⁻¹' chart.baseSet) : False :=
  mismatch rfl

/-- The packaged partial homeomorphism cannot silently use a smaller or unrelated target. -/
theorem malformed_adjointBundle_trivialization_target_blocked
    (mismatch : (AdjointBundle.localTrivialization (I := I) chart bundle adjointRegularity).target ≠
      chart.baseSet ×ˢ (Set.univ : Set (GroupLieAlgebra I G))) : False :=
  mismatch rfl

/-- The forward map remains the exact quotient coordinate map, not a caller-selected map. -/
theorem disconnected_adjointBundle_trivialization_forward_blocked
    (z : AdjointBundle (I := I) torsor)
    (mismatch :
      AdjointBundle.localTrivialization (I := I) chart bundle adjointRegularity z ≠
        AdjointBundle.localCoordinate (I := I) chart z) : False :=
  mismatch rfl

/-- The inverse remains the exact representative map based at group coordinate `1`. -/
theorem disconnected_adjointBundle_trivialization_inverse_blocked
    (w : B × GroupLieAlgebra I G)
    (mismatch :
      (AdjointBundle.localTrivialization (I := I) chart bundle adjointRegularity).symm w ≠
        AdjointBundle.localCoordinateInverse (I := I) chart w) : False :=
  mismatch rfl

end

end YangMills.Geometry.Probes
