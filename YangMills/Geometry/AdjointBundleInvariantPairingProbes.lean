/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Geometry.AdjointBundleInvariantPairing

/-!
# Hostile probes for the invariant adjoint-fiber pairing
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
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [TopologicalSpace B] [TopologicalSpace P]
    {I : ModelWithCorners ℝ E H}
    [ChartedSpace H G] [LieGroup I ∞ G]
    {torsor : PrincipalBundleTorsorData G B P}
    (bundle : TopologicalPrincipalBundleData torsor)
    (inner : InvariantInnerProductData (I := I) (G := G))

/-- A designated chart cannot change the scalar pairing on an actual adjoint fiber. -/
theorem chart_dependent_adjointFiberPairing_blocked
    (chart : PrincipalBundleLocalTrivialization torsor)
    {b : B} (hb : b ∈ chart.baseSet)
    (X Y : AdjointBundle.Fiber (I := I) (torsor := torsor) b)
    (mismatch :
      AdjointBundle.fiberPairingInChart bundle inner chart hb X Y ≠
        AdjointBundle.fiberPairing bundle inner b X Y) : False :=
  mismatch (AdjointBundle.fiberPairingInChart_eq bundle inner chart hb X Y)

/-- The induced quadratic value cannot be negative. -/
theorem negative_adjointFiberQuadratic_blocked
    (b : B) (X : AdjointBundle.Fiber (I := I) (torsor := torsor) b)
    (negative : AdjointBundle.fiberPairing bundle inner b X X < 0) : False :=
  (not_lt_of_ge (AdjointBundle.fiberPairing_self_nonnegative bundle inner b X)) negative

/-- Positive definiteness prevents a nonzero dependent-fiber value from having zero quadratic
value. -/
theorem degenerate_adjointFiberPairing_blocked
    (b : B) (X : AdjointBundle.Fiber (I := I) (torsor := torsor) b)
    (nonzero :
      letI : AddCommGroup (AdjointBundle.Fiber (I := I) (torsor := torsor) b) :=
        AdjointBundle.fiberAddCommGroup (I := I) bundle b
      X ≠ 0)
    (zeroQuadratic : AdjointBundle.fiberPairing bundle inner b X X = 0) : False := by
  letI : AddCommGroup (AdjointBundle.Fiber (I := I) (torsor := torsor) b) :=
    AdjointBundle.fiberAddCommGroup (I := I) bundle b
  letI : Module ℝ (AdjointBundle.Fiber (I := I) (torsor := torsor) b) :=
    AdjointBundle.fiberModule (I := I) bundle b
  exact nonzero ((AdjointBundle.fiberPairing_self_eq_zero_iff bundle inner b X).mp zeroQuadratic)

end

end YangMills.Geometry.Probes
