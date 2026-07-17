/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Geometry.AdjointBundle

/-!
# Hostile probes for the set-level adjoint bundle
-/

namespace YangMills.Geometry.Probes

open scoped Manifold ContDiff

universe uE uH uG uB uP

noncomputable section

variable
    {E : Type uE} {H : Type uH}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
    {G : Type uG} {B : Type uB} {P : Type uP}
    [Group G] [TopologicalSpace G]
    {I : ModelWithCorners ℝ E H}
    [ChartedSpace H G] [LieGroup I ∞ G]
    {torsor : PrincipalBundleTorsorData G B P}

/-- The diagonal action cannot violate the principal right-action multiplication order. -/
theorem malformed_adjointBundle_action_order_blocked
    (z : P × GroupLieAlgebra I G) (g h : G)
    (mismatch :
      adjointBundleRightAction torsor (adjointBundleRightAction torsor z g) h ≠
        adjointBundleRightAction torsor z (g * h)) : False :=
  mismatch (adjointBundleRightAction_mul torsor z g h)

/-- The quotient must identify the exact `Ad(g⁻¹)` diagonal representative. -/
theorem missing_adjointBundle_identification_blocked
    (p : P) (X : GroupLieAlgebra I G) (g : G)
    (mismatch :
      AdjointBundle.mk torsor (torsor.rightAction p g)
          (YangMills.Mathematics.lieGroupAdjoint I g⁻¹ X) ≠
        AdjointBundle.mk torsor p X) : False :=
  mismatch (AdjointBundle.mk_rightAction torsor p X g)

/-- Equality of classes cannot be asserted without an actual same-orbit witness carrying the exact
inverse-adjoint value equation. -/
theorem disconnected_adjointBundle_equality_blocked
    (p q : P) (X Y : GroupLieAlgebra I G)
    (equal : AdjointBundle.mk torsor p X = AdjointBundle.mk torsor q Y)
    (noOrbit : ¬∃ g : G,
      torsor.rightAction p g = q ∧
        YangMills.Mathematics.lieGroupAdjoint I g⁻¹ X = Y) : False :=
  noOrbit ((AdjointBundle.mk_eq_mk_iff torsor p q X Y).mp equal)

/-- The quotient projection cannot be disconnected from the original principal projection. -/
theorem malformed_adjointBundle_projection_blocked
    (p : P) (X : GroupLieAlgebra I G)
    (mismatch :
      AdjointBundle.projection torsor (AdjointBundle.mk torsor p X) ≠
        torsor.projection p) : False :=
  mismatch (AdjointBundle.projection_mk torsor p X)

/-- The associated-bundle projection cannot move when a representative is changed diagonally. -/
theorem base_moving_adjointBundle_representative_blocked
    (p : P) (X : GroupLieAlgebra I G) (g : G)
    (baseMoves :
      AdjointBundle.projection torsor
          (AdjointBundle.mk torsor (torsor.rightAction p g)
            (YangMills.Mathematics.lieGroupAdjoint I g⁻¹ X)) ≠
        AdjointBundle.projection torsor (AdjointBundle.mk torsor p X)) : False :=
  baseMoves (congrArg (AdjointBundle.projection torsor)
    (AdjointBundle.mk_rightAction torsor p X g))

end

end YangMills.Geometry.Probes
