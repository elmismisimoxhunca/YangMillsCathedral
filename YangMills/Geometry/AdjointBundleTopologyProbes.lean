/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Geometry.AdjointBundleTopology

/-!
# Hostile probes for the adjoint-bundle quotient topology
-/

namespace YangMills.Geometry.Probes

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
    {bundle : TopologicalPrincipalBundleData torsor}

omit [TopologicalSpace B] [IsTopologicalGroup G] in
/-- The representative map cannot fail to be a quotient map for the declared topology. -/
theorem malformed_adjointBundle_quotientTopology_blocked
    (notQuotient : ¬Topology.IsQuotientMap
      (fun z : P × GroupLieAlgebra I G => AdjointBundle.mk torsor z.1 z.2)) : False :=
  notQuotient (AdjointBundle.mk_isQuotientMap (I := I) (torsor := torsor))

/-- The associated projection cannot be disconnected from principal-bundle continuity. -/
theorem discontinuous_adjointBundle_projection_blocked
    (bundle : TopologicalPrincipalBundleData torsor)
    (discontinuous : ¬Continuous
      (AdjointBundle.projection torsor : AdjointBundle (I := I) torsor → B)) : False :=
  discontinuous (AdjointBundle.projection_continuous (I := I) bundle)

/-- The associated projection must induce exactly the declared base topology. -/
theorem nonquotient_adjointBundle_projection_blocked
    (bundle : TopologicalPrincipalBundleData torsor)
    (notQuotient : ¬Topology.IsQuotientMap
      (AdjointBundle.projection torsor : AdjointBundle (I := I) torsor → B)) : False :=
  notQuotient (AdjointBundle.projection_isQuotientMap (I := I) bundle)

omit [TopologicalSpace B] [TopologicalSpace P] [IsTopologicalGroup G] in
/-- An empty associated fiber is impossible because every principal fiber supplies a zero class. -/
theorem empty_adjointBundle_fiber_blocked
    (b : B)
    (emptyFiber : ¬∃ z : AdjointBundle (I := I) torsor,
      AdjointBundle.projection torsor z = b) : False :=
  emptyFiber (AdjointBundle.projection_surjective (I := I) torsor b)

omit [TopologicalSpace B] [TopologicalSpace P] [IsTopologicalGroup G] in
/-- The zero-class comparison map cannot cover a different base map. -/
theorem base_moving_adjointBundle_zeroClass_blocked
    (p : P)
    (mismatch :
      AdjointBundle.projection torsor (AdjointBundle.zeroClass (I := I) torsor p) ≠
        torsor.projection p) : False :=
  mismatch (AdjointBundle.projection_zeroClass (I := I) torsor p)

end

end YangMills.Geometry.Probes
