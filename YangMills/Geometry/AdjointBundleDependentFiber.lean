/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Geometry.AdjointBundleSmoothAtlas
import Mathlib.Topology.FiberBundle.Basic

/-!
# Dependent fibers of the adjoint quotient

Mathlib's `FiberBundle` and `VectorBundle` interfaces use a dependent family over the base. This
module forms that family directly from the already fixed adjoint orbit quotient and proves that its
`Bundle.TotalSpace` is canonically equivalent, as a base-preserving carrier, to the quotient.

This is a set-level bridge only. No topology is installed on the dependent total space, no topology
equality or homeomorphism is asserted, and no `FiberBundle` or `VectorBundle` is claimed.
-/

namespace YangMills.Geometry

open Set
open scoped Manifold ContDiff Bundle

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

/-- The fiber of the actual adjoint orbit quotient over `b`. -/
def AdjointBundle.Fiber (b : B) :=
  {z : AdjointBundle (I := I) torsor // AdjointBundle.projection torsor z = b}

/-- Forget the dependent-fiber packaging while retaining the same adjoint quotient point. -/
def AdjointBundle.totalSpaceToQuotient :
    Bundle.TotalSpace E (AdjointBundle.Fiber (I := I) (torsor := torsor)) →
      AdjointBundle (I := I) torsor :=
  fun z => z.snd.1

/-- Package an adjoint quotient point in the fiber over its actual projection. -/
def AdjointBundle.quotientToTotalSpace
    (z : AdjointBundle (I := I) torsor) :
    Bundle.TotalSpace E (AdjointBundle.Fiber (I := I) (torsor := torsor)) :=
  ⟨AdjointBundle.projection torsor z, ⟨z, rfl⟩⟩

omit [TopologicalSpace B] [TopologicalSpace P] [IsTopologicalGroup G] in
/-- Forgetting a packaged quotient point returns that exact point. -/
@[simp]
theorem AdjointBundle.totalSpaceToQuotient_quotientToTotalSpace
    (z : AdjointBundle (I := I) torsor) :
    AdjointBundle.totalSpaceToQuotient (I := I) (torsor := torsor)
      (AdjointBundle.quotientToTotalSpace (I := I) (torsor := torsor) z) = z :=
  rfl

omit [TopologicalSpace B] [TopologicalSpace P] [IsTopologicalGroup G] in
/-- Repackaging a dependent total-space point returns the same dependent pair, including its base. -/
@[simp]
theorem AdjointBundle.quotientToTotalSpace_totalSpaceToQuotient
    (z : Bundle.TotalSpace E (AdjointBundle.Fiber (I := I) (torsor := torsor))) :
    AdjointBundle.quotientToTotalSpace (I := I) (torsor := torsor)
      (AdjointBundle.totalSpaceToQuotient (I := I) (torsor := torsor) z) = z := by
  rcases z with ⟨b, ⟨z, hz⟩⟩
  simp only [AdjointBundle.quotientToTotalSpace, AdjointBundle.totalSpaceToQuotient]
  subst b
  rfl

omit [IsTopologicalGroup G] in
/-- Canonical carrier equivalence between the dependent total space and the original orbit quotient. -/
def AdjointBundle.totalSpaceEquivQuotient :
    Bundle.TotalSpace E (AdjointBundle.Fiber (I := I) (torsor := torsor)) ≃
      AdjointBundle (I := I) torsor where
  toFun := AdjointBundle.totalSpaceToQuotient (I := I) (torsor := torsor)
  invFun := AdjointBundle.quotientToTotalSpace (I := I) (torsor := torsor)
  left_inv := AdjointBundle.quotientToTotalSpace_totalSpaceToQuotient (I := I) (torsor := torsor)
  right_inv := AdjointBundle.totalSpaceToQuotient_quotientToTotalSpace (I := I) (torsor := torsor)

omit [TopologicalSpace B] [TopologicalSpace P] [IsTopologicalGroup G] in
/-- The carrier equivalence preserves the declared base projection exactly. -/
@[simp]
theorem AdjointBundle.projection_totalSpaceEquivQuotient
    (z : Bundle.TotalSpace E (AdjointBundle.Fiber (I := I) (torsor := torsor))) :
    AdjointBundle.projection torsor
      (AdjointBundle.totalSpaceEquivQuotient (I := I) (torsor := torsor) z) = z.proj :=
  z.snd.2

omit [TopologicalSpace B] [TopologicalSpace P] [IsTopologicalGroup G] in
/-- Every dependent adjoint fiber is nonempty, derived from the already proved surjectivity of the
adjoint quotient projection. -/
theorem AdjointBundle.fiber_nonempty (b : B) :
    Nonempty (AdjointBundle.Fiber (I := I) (torsor := torsor) b) := by
  obtain ⟨z, hz⟩ := AdjointBundle.projection_surjective (I := I) torsor b
  exact ⟨⟨z, hz⟩⟩

end

end YangMills.Geometry
