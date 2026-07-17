/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Geometry.AdjointBundleLocalCoordinates

/-!
# Hostile probes for adjoint-bundle local coordinates
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
    (chart : PrincipalBundleLocalTrivialization torsor)

omit [IsTopologicalGroup G] in
/-- Local coordinates cannot depend on the selected representative of a diagonal orbit. -/
theorem representative_dependent_adjointBundle_coordinate_blocked
    {x y : P × GroupLieAlgebra I G}
    (related : adjointBundleOrbitRelation torsor x y)
    (mismatch :
      adjointBundleChartRepresentative (I := I) chart x ≠
        adjointBundleChartRepresentative (I := I) chart y) : False :=
  mismatch (adjointBundleChartRepresentative_invariant (I := I) chart related)

omit [IsTopologicalGroup G] in
/-- The total representative function's off-source extension is pinned to zero and cannot smuggle
unrelated local data into the quotient lift. -/
theorem malformed_adjointBundle_offSource_extension_blocked
    (p : P) (X : GroupLieAlgebra I G)
    (hp : p ∉ chart.toPartialHomeomorph.source)
    (mismatch :
      adjointBundleChartRepresentative (I := I) chart (p, X) ≠
        (torsor.projection p, 0)) : False :=
  mismatch (by simp [adjointBundleChartRepresentative, hp])

omit [IsTopologicalGroup G] in
/-- On the chart source, the fiber coordinate must use `Ad(k)`, not an unrelated value. -/
theorem malformed_adjointBundle_localCoordinate_formula_blocked
    (p : P) (X : GroupLieAlgebra I G)
    (hp : p ∈ chart.toPartialHomeomorph.source)
    (mismatch :
      AdjointBundle.localCoordinate (I := I) chart (AdjointBundle.mk torsor p X) ≠
        (torsor.projection p,
          YangMills.Mathematics.lieGroupAdjoint I (chart p).2 X)) : False :=
  mismatch (AdjointBundle.localCoordinate_mk chart p X hp)

omit [IsTopologicalGroup G] in
/-- Local coordinates cannot move the associated-bundle base. -/
theorem base_moving_adjointBundle_localCoordinate_blocked
    (z : AdjointBundle (I := I) torsor)
    (hz : AdjointBundle.projection torsor z ∈ chart.baseSet)
    (mismatch :
      (AdjointBundle.localCoordinate (I := I) chart z).1 ≠
        AdjointBundle.projection torsor z) : False :=
  mismatch (AdjointBundle.localCoordinate_fst chart z hz)

omit [IsTopologicalGroup G] in
/-- The inverse law on the associated source rejects a coordinate map disconnected from its
quotient class. -/
theorem malformed_adjointBundle_local_leftInverse_blocked
    (z : AdjointBundle (I := I) torsor)
    (hz : AdjointBundle.projection torsor z ∈ chart.baseSet)
    (mismatch :
      AdjointBundle.localCoordinateInverse (I := I) chart
          (AdjointBundle.localCoordinate (I := I) chart z) ≠ z) : False :=
  mismatch (AdjointBundle.localCoordinateInverse_localCoordinate chart z hz)

omit [IsTopologicalGroup G] in
/-- The inverse law on `baseSet × g` rejects malformed inverse representatives. -/
theorem malformed_adjointBundle_local_rightInverse_blocked
    (z : B × GroupLieAlgebra I G) (hz : z.1 ∈ chart.baseSet)
    (mismatch :
      AdjointBundle.localCoordinate (I := I) chart
          (AdjointBundle.localCoordinateInverse (I := I) chart z) ≠ z) : False :=
  mismatch (AdjointBundle.localCoordinate_localCoordinateInverse chart z hz)

end

end YangMills.Geometry.Probes
