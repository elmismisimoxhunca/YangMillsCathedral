/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Geometry.AdjointBundleDependentFiber
import Mathlib.Topology.Homeomorph.Defs

/-!
# Topology coherence for the dependent adjoint total space

The dependent total-space carrier receives the topology induced by its canonical equivalence to the
already topologized adjoint orbit quotient. With this explicitly named topology, the carrier
equivalence is a homeomorphism by construction. Thus the dependent presentation cannot introduce a
competing topology.

The topology and homeomorphism are named values, not global instances. No `FiberBundle`,
`VectorBundle`, fiber algebra, or smooth bundle is claimed here.
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

/-- The unique topology deliberately chosen here: pull back the established quotient topology along
the canonical dependent-total-space equivalence. -/
@[reducible]
def AdjointBundle.dependentTotalSpaceTopology :
    TopologicalSpace
      (Bundle.TotalSpace E (AdjointBundle.Fiber (I := I) (torsor := torsor))) :=
  TopologicalSpace.induced
    (AdjointBundle.totalSpaceToQuotient (I := I) (torsor := torsor)) inferInstance

/-- Under the named induced topology, the dependent total-space carrier is homeomorphic to the
original orbit quotient by the exact carrier equivalence. -/
def AdjointBundle.dependentTotalSpaceHomeomorphQuotient :
    @Homeomorph
      (Bundle.TotalSpace E (AdjointBundle.Fiber (I := I) (torsor := torsor)))
      (AdjointBundle (I := I) torsor)
      (AdjointBundle.dependentTotalSpaceTopology (I := I) (torsor := torsor))
      inferInstance := by
  letI : TopologicalSpace
      (Bundle.TotalSpace E (AdjointBundle.Fiber (I := I) (torsor := torsor))) :=
    AdjointBundle.dependentTotalSpaceTopology (I := I) (torsor := torsor)
  exact (AdjointBundle.totalSpaceEquivQuotient
    (I := I) (torsor := torsor)).toHomeomorphOfIsInducing
      (Topology.IsInducing.induced _)

omit [TopologicalSpace B] [IsTopologicalGroup G] in
/-- The homeomorphism's forward map is exactly dependent-package forgetting. -/
@[simp]
theorem AdjointBundle.dependentTotalSpaceHomeomorphQuotient_apply
    (z : Bundle.TotalSpace E (AdjointBundle.Fiber (I := I) (torsor := torsor))) :
    AdjointBundle.dependentTotalSpaceHomeomorphQuotient (I := I) (torsor := torsor) z =
      AdjointBundle.totalSpaceToQuotient (I := I) (torsor := torsor) z :=
  rfl

omit [TopologicalSpace B] [IsTopologicalGroup G] in
/-- Its inverse is exactly quotient-point dependent packaging. -/
@[simp]
theorem AdjointBundle.dependentTotalSpaceHomeomorphQuotient_symm_apply
    (z : AdjointBundle (I := I) torsor) :
    letI : TopologicalSpace
        (Bundle.TotalSpace E (AdjointBundle.Fiber (I := I) (torsor := torsor))) :=
      AdjointBundle.dependentTotalSpaceTopology (I := I) (torsor := torsor)
    (AdjointBundle.dependentTotalSpaceHomeomorphQuotient
      (I := I) (torsor := torsor)).symm z =
      AdjointBundle.quotientToTotalSpace (I := I) (torsor := torsor) z :=
  rfl

omit [TopologicalSpace B] [IsTopologicalGroup G] in
/-- The homeomorphism preserves the bundle base exactly. -/
@[simp]
theorem AdjointBundle.projection_dependentTotalSpaceHomeomorphQuotient
    (z : Bundle.TotalSpace E (AdjointBundle.Fiber (I := I) (torsor := torsor))) :
    AdjointBundle.projection torsor
      (AdjointBundle.dependentTotalSpaceHomeomorphQuotient
        (I := I) (torsor := torsor) z) = z.proj :=
  z.snd.2

end

end YangMills.Geometry
