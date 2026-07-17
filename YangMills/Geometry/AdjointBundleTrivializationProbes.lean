/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Geometry.AdjointBundleTrivialization

/-!
# Hostile probes for adjoint-bundle trivialization packaging
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

/-- Promotion cannot change the principal chart's base set. -/
theorem malformed_adjointBundle_bundleTrivialization_baseSet_blocked
    (mismatch : (AdjointBundle.bundleTrivialization (I := I) bundle chart).baseSet ≠
      chart.baseSet) : False :=
  mismatch rfl

/-- Promotion cannot shrink or disconnect the quotient source. -/
theorem malformed_adjointBundle_bundleTrivialization_source_blocked
    (mismatch : (AdjointBundle.bundleTrivialization (I := I) bundle chart).source ≠
      AdjointBundle.projection torsor ⁻¹' chart.baseSet) : False :=
  mismatch rfl

/-- Promotion cannot change the full model fiber in the target. -/
theorem malformed_adjointBundle_bundleTrivialization_target_blocked
    (mismatch : (AdjointBundle.bundleTrivialization (I := I) bundle chart).target ≠
      chart.baseSet ×ˢ (Set.univ : Set (GroupLieAlgebra I G))) : False :=
  mismatch rfl

/-- The promoted forward map remains the representative-independent quotient coordinate. -/
theorem disconnected_adjointBundle_bundleTrivialization_forward_blocked
    (z : AdjointBundle (I := I) torsor)
    (mismatch : AdjointBundle.bundleTrivialization (I := I) bundle chart z ≠
      AdjointBundle.localCoordinate (I := I) chart z) : False :=
  mismatch rfl

/-- The model-coordinate promotion cannot bypass the explicit tangent-model equivalence. -/
theorem disconnected_adjointBundle_modelTrivialization_blocked
    (z : AdjointBundle (I := I) torsor)
    (mismatch : AdjointBundle.modelBundleTrivialization (I := I) bundle chart z ≠
      ((AdjointBundle.localCoordinate (I := I) chart z).1,
        YangMills.Mathematics.groupLieAlgebraModelEquiv (G := G) I
          (AdjointBundle.localCoordinate (I := I) chart z).2)) : False :=
  mismatch (AdjointBundle.modelBundleTrivialization_apply (I := I) bundle chart z)

/-- The promoted inverse remains the canonical representative map. -/
theorem disconnected_adjointBundle_bundleTrivialization_inverse_blocked
    (z : B × GroupLieAlgebra I G)
    (mismatch :
      (AdjointBundle.bundleTrivialization (I := I) bundle chart).toOpenPartialHomeomorph.symm z ≠
        AdjointBundle.localCoordinateInverse (I := I) chart z) : False :=
  mismatch rfl

/-- Selected associated trivializations cannot miss any quotient point. -/
theorem uncovered_adjointBundle_point_blocked
    (z : AdjointBundle (I := I) torsor)
    (missing : z ∉ (AdjointBundle.bundleTrivialization (I := I) bundle
      (bundle.trivializationAt (AdjointBundle.projection torsor z))).source) : False :=
  missing (AdjointBundle.mem_source_bundleTrivializationAt (I := I) bundle z)

/-- The selected associated atlas cannot have an empty union of sources over an inhabited quotient. -/
theorem empty_adjointBundle_trivialization_cover_blocked
    [Nonempty (AdjointBundle (I := I) torsor)]
    (emptyCover : ⋃ b : B, (AdjointBundle.bundleTrivialization (I := I) bundle
      (bundle.trivializationAt b)).source = (∅ : Set (AdjointBundle (I := I) torsor))) : False := by
  rw [AdjointBundle.iUnion_source_bundleTrivializationAt (I := I) bundle] at emptyCover
  have member : Classical.choice ‹Nonempty (AdjointBundle (I := I) torsor)› ∈
      (Set.univ : Set (AdjointBundle (I := I) torsor)) := Set.mem_univ _
  rw [emptyCover] at member
  exact member

end

end YangMills.Geometry.Probes
