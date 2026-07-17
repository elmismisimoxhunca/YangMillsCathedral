/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Geometry.AdjointBundleLocalTrivialization
import Mathlib.Topology.FiberBundle.Trivialization

/-!
# Adjoint-bundle trivializations in Mathlib's bundle interface

The existing local homeomorphisms on the actual adjoint orbit quotient are promoted to Mathlib
`Bundle.Trivialization`s. This retains the quotient carrier and quotient topology while exposing the
exact projection, base set, source, target, and local fiber coordinate expected by later reusable
fiberwise-linear atlas infrastructure.

This module does not install a `FiberBundle`, `VectorBundle`, charted manifold, or smooth vector
bundle structure. Those require further overlap and dependent-fiber infrastructure.
-/

namespace YangMills.Geometry

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

/-- The canonical associated local homeomorphism, promoted without changing maps or topology to
Mathlib's generic bundle-trivialization interface. -/
def AdjointBundle.bundleTrivialization :
    Bundle.Trivialization (GroupLieAlgebra I G)
      (AdjointBundle.projection (I := I) torsor) where
  toOpenPartialHomeomorph :=
    AdjointBundle.canonicalLocalTrivialization (I := I) (G := G)
      (torsor := torsor) chart bundle
  baseSet := chart.baseSet
  open_baseSet := chart.isOpen_baseSet
  source_eq := rfl
  target_eq := rfl
  proj_toFun := fun z hz =>
    AdjointBundle.localCoordinate_fst (I := I) chart z hz

/-- The promoted trivialization transported explicitly from the intrinsic tangent Lie algebra to
the declared normed model. This avoids relying on the implementation-level definitional equality of
tangent fibers with their model. -/
def AdjointBundle.modelBundleTrivialization :
    Bundle.Trivialization E (AdjointBundle.projection (I := I) torsor) :=
  (AdjointBundle.bundleTrivialization (I := I) bundle chart).transFiberHomeomorph
    (YangMills.Mathematics.groupLieAlgebraModelEquiv (G := G) I).toHomeomorph

/-- The bundle trivialization uses the exact quotient local-coordinate map. -/
@[simp]
theorem AdjointBundle.bundleTrivialization_apply
    (z : AdjointBundle (I := I) torsor) :
    AdjointBundle.bundleTrivialization (I := I) bundle chart z =
      AdjointBundle.localCoordinate (I := I) chart z :=
  rfl

/-- The model-coordinate trivialization applies the explicit tangent-model bridge to the intrinsic
fiber coordinate. -/
@[simp]
theorem AdjointBundle.modelBundleTrivialization_apply
    (z : AdjointBundle (I := I) torsor) :
    AdjointBundle.modelBundleTrivialization (I := I) bundle chart z =
      ((AdjointBundle.localCoordinate (I := I) chart z).1,
        YangMills.Mathematics.groupLieAlgebraModelEquiv (G := G) I
          (AdjointBundle.localCoordinate (I := I) chart z).2) := by
  rw [AdjointBundle.modelBundleTrivialization,
    Bundle.Trivialization.transFiberHomeomorph_apply]
  rfl

/-- Its inverse is the exact canonical representative map based at group coordinate `1`. -/
@[simp]
theorem AdjointBundle.bundleTrivialization_symm_apply
    (z : B × GroupLieAlgebra I G) :
    (AdjointBundle.bundleTrivialization (I := I) bundle chart).toOpenPartialHomeomorph.symm z =
      AdjointBundle.localCoordinateInverse (I := I) chart z :=
  rfl

/-- The selected associated trivialization covers the requested base point. -/
theorem AdjointBundle.mem_baseSet_bundleTrivializationAt (b : B) :
    b ∈ (AdjointBundle.bundleTrivialization (I := I) bundle
      (bundle.trivializationAt b)).baseSet :=
  bundle.mem_baseSet_trivializationAt b

/-- The selected associated trivialization covers every point of the adjoint quotient. -/
theorem AdjointBundle.mem_source_bundleTrivializationAt
    (z : AdjointBundle (I := I) torsor) :
    z ∈ (AdjointBundle.bundleTrivialization (I := I) bundle
      (bundle.trivializationAt (AdjointBundle.projection torsor z))).source := by
  rw [(AdjointBundle.bundleTrivialization (I := I) bundle _).source_eq]
  exact bundle.mem_baseSet_trivializationAt (AdjointBundle.projection torsor z)

/-- The selected associated trivializations cover the entire quotient carrier. -/
theorem AdjointBundle.iUnion_source_bundleTrivializationAt :
    ⋃ b : B, (AdjointBundle.bundleTrivialization (I := I) bundle
      (bundle.trivializationAt b)).source = Set.univ := by
  apply Set.eq_univ_of_forall
  intro z
  exact Set.mem_iUnion.mpr
    ⟨AdjointBundle.projection torsor z,
      AdjointBundle.mem_source_bundleTrivializationAt (I := I) bundle z⟩

end

end YangMills.Geometry
