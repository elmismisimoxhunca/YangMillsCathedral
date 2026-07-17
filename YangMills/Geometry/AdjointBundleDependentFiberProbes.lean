/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Geometry.AdjointBundleDependentFiber

/-!
# Hostile probes for the dependent-fiber carrier bridge
-/

namespace YangMills.Geometry.Probes

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

omit [TopologicalSpace B] [TopologicalSpace P] [IsTopologicalGroup G] in
/-- The carrier equivalence cannot move a dependent point to another base fiber. -/
theorem baseMoving_adjointBundle_totalSpaceEquiv_blocked
    (z : Bundle.TotalSpace E (AdjointBundle.Fiber (I := I) (torsor := torsor)))
    (mismatch : AdjointBundle.projection torsor
      (AdjointBundle.totalSpaceEquivQuotient (I := I) (torsor := torsor) z) ≠ z.proj) : False :=
  mismatch (AdjointBundle.projection_totalSpaceEquivQuotient
    (I := I) (torsor := torsor) z)

omit [TopologicalSpace B] [TopologicalSpace P] [IsTopologicalGroup G] in
/-- Quotient-to-total-space followed by forgetting cannot change the quotient point. -/
theorem broken_adjointBundle_quotient_roundTrip_blocked
    (z : AdjointBundle (I := I) torsor)
    (mismatch : AdjointBundle.totalSpaceToQuotient (I := I) (torsor := torsor)
      (AdjointBundle.quotientToTotalSpace (I := I) (torsor := torsor) z) ≠ z) : False :=
  mismatch (AdjointBundle.totalSpaceToQuotient_quotientToTotalSpace
    (I := I) (torsor := torsor) z)

omit [TopologicalSpace B] [TopologicalSpace P] [IsTopologicalGroup G] in
/-- The bridge cannot identify two distinct dependent total-space points. -/
theorem noninjective_adjointBundle_totalSpace_bridge_blocked
    (x y : Bundle.TotalSpace E (AdjointBundle.Fiber (I := I) (torsor := torsor)))
    (same : AdjointBundle.totalSpaceToQuotient (I := I) (torsor := torsor) x =
      AdjointBundle.totalSpaceToQuotient (I := I) (torsor := torsor) y)
    (different : x ≠ y) : False :=
  different ((AdjointBundle.totalSpaceEquivQuotient (I := I) (torsor := torsor)).injective same)

omit [TopologicalSpace B] [TopologicalSpace P] [IsTopologicalGroup G] in
/-- No dependent adjoint fiber can be empty. -/
theorem empty_adjointBundle_dependentFiber_blocked
    (b : B) (emptyFiber : IsEmpty (AdjointBundle.Fiber (I := I) (torsor := torsor) b)) : False := by
  letI := emptyFiber
  exact IsEmpty.false (Classical.choice (AdjointBundle.fiber_nonempty (I := I) (torsor := torsor) b))

end

end YangMills.Geometry.Probes
