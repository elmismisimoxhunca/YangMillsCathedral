/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Geometry.AdjointBundleFiberLinearity
import YangMills.Geometry.InvariantInnerProduct

/-!
# Invariant pairing on adjoint-bundle fibers

An adjoint-invariant positive pairing on the gauge Lie algebra induces a pairing on each actual
adjoint quotient fiber. The definition uses the exact selected fiber coordinate, and invariance
proves that every designated principal chart computes the same scalar.

The pairing remains named data rather than a global inner-product instance, so different physical
normalizations can coexist.
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
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [TopologicalSpace B] [TopologicalSpace P]
    {I : ModelWithCorners ℝ E H}
    [ChartedSpace H G] [LieGroup I ∞ G]
    {torsor : PrincipalBundleTorsorData G B P}
    (bundle : TopologicalPrincipalBundleData torsor)

namespace AdjointBundle

/-- The invariant Lie-algebra pairing transported to one actual dependent adjoint fiber through its
exact selected quotient coordinate. -/
def fiberPairing
    (inner : InvariantInnerProductData (I := I) (G := G))
    (b : B) (X Y : AdjointBundle.Fiber (I := I) (torsor := torsor) b) : ℝ :=
  inner.pairing
    ((YangMills.Mathematics.groupLieAlgebraModelEquiv I).symm
      (AdjointBundle.selectedFiberModelEquiv (I := I) bundle b X))
    ((YangMills.Mathematics.groupLieAlgebraModelEquiv I).symm
      (AdjointBundle.selectedFiberModelEquiv (I := I) bundle b Y))

/-- The same fiber pairing computed in an arbitrary designated principal chart. -/
def fiberPairingInChart
    (inner : InvariantInnerProductData (I := I) (G := G))
    (chart : PrincipalBundleLocalTrivialization torsor)
    {b : B} (hb : b ∈ chart.baseSet)
    (X Y : AdjointBundle.Fiber (I := I) (torsor := torsor) b) : ℝ :=
  inner.pairing
    ((YangMills.Mathematics.groupLieAlgebraModelEquiv I).symm
      (AdjointBundle.fiberModelEquiv (I := I) bundle chart hb X))
    ((YangMills.Mathematics.groupLieAlgebraModelEquiv I).symm
      (AdjointBundle.fiberModelEquiv (I := I) bundle chart hb Y))

/-- Adjoint invariance makes the fiber pairing independent of the designated chart used to compute
it. -/
theorem fiberPairingInChart_eq
    (inner : InvariantInnerProductData (I := I) (G := G))
    (chart : PrincipalBundleLocalTrivialization torsor)
    {b : B} (hb : b ∈ chart.baseSet)
    (X Y : AdjointBundle.Fiber (I := I) (torsor := torsor) b) :
    fiberPairingInChart bundle inner chart hb X Y =
      fiberPairing bundle inner b X Y := by
  rw [fiberPairingInChart, fiberPairing]
  rw [AdjointBundle.fiberModelEquiv_eq_coordinateChange bundle chart hb X]
  rw [AdjointBundle.fiberModelEquiv_eq_coordinateChange bundle chart hb Y]
  exact inner.adjoint_invariant _ _ _

/-- The induced fiber pairing is symmetric. -/
theorem fiberPairing_symmetric
    (inner : InvariantInnerProductData (I := I) (G := G))
    (b : B) (X Y : AdjointBundle.Fiber (I := I) (torsor := torsor) b) :
    fiberPairing bundle inner b X Y = fiberPairing bundle inner b Y X :=
  inner.symmetric _ _

/-- The quadratic value of the induced fiber pairing is nonnegative. -/
theorem fiberPairing_self_nonnegative
    (inner : InvariantInnerProductData (I := I) (G := G))
    (b : B) (X : AdjointBundle.Fiber (I := I) (torsor := torsor) b) :
    0 ≤ fiberPairing bundle inner b X X :=
  inner.quadratic_nonnegative _

/-- The induced quadratic value vanishes exactly at the named zero of the actual dependent quotient
fiber. -/
@[simp]
theorem fiberPairing_self_eq_zero_iff
    (inner : InvariantInnerProductData (I := I) (G := G))
    (b : B) (X : AdjointBundle.Fiber (I := I) (torsor := torsor) b) :
    letI : AddCommGroup (AdjointBundle.Fiber (I := I) (torsor := torsor) b) :=
      AdjointBundle.fiberAddCommGroup (I := I) bundle b
    letI : Module ℝ (AdjointBundle.Fiber (I := I) (torsor := torsor) b) :=
      AdjointBundle.fiberModule (I := I) bundle b
    fiberPairing bundle inner b X X = 0 ↔ X = 0 := by
  letI : AddCommGroup (AdjointBundle.Fiber (I := I) (torsor := torsor) b) :=
    AdjointBundle.fiberAddCommGroup (I := I) bundle b
  letI : Module ℝ (AdjointBundle.Fiber (I := I) (torsor := torsor) b) :=
    AdjointBundle.fiberModule (I := I) bundle b
  change inner.quadratic
    ((YangMills.Mathematics.groupLieAlgebraModelEquiv I).symm
      (AdjointBundle.selectedFiberModelEquiv (I := I) bundle b X)) = 0 ↔ X = 0
  rw [inner.quadratic_eq_zero_iff]
  constructor
  · intro h
    apply (AdjointBundle.selectedFiberLinearEquiv (I := I) bundle b).injective
    rw [map_zero]
    exact (YangMills.Mathematics.groupLieAlgebraModelEquiv I).symm.injective h
  · rintro rfl
    change (AdjointBundle.selectedFiberLinearEquiv (I := I) bundle b) 0 = 0
    exact map_zero _

end AdjointBundle

end

end YangMills.Geometry
