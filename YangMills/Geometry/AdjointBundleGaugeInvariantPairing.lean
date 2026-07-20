/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Geometry.AdjointBundleGaugeContinuousLinear
import YangMills.Geometry.AdjointBundleInvariantPairing

/-!
# Gauge invariance of the adjoint-fiber pairing

The covariant induced gauge action has selected fiber coordinate `Ad(g_ϕ(s(b)))`. Applying the
adjoint invariance of the exact Lie-algebra pairing to both arguments proves that the descended
fiber pairing, and hence its quadratic value, are unchanged.

This is a pointwise fiber theorem. It does not by itself prove invariance of curvature contractions,
densities, integrals, actions, or interpreted observables.
-/

namespace YangMills.Geometry

open scoped Manifold ContDiff

universe uEG uHG uEB uHB uEP uHP uG uB uP

noncomputable section

variable
    {EG : Type uEG} {HG : Type uHG}
    [NormedAddCommGroup EG] [NormedSpace ℝ EG] [TopologicalSpace HG]
    {EB : Type uEB} {HB : Type uHB}
    [NormedAddCommGroup EB] [NormedSpace ℝ EB] [TopologicalSpace HB]
    {EP : Type uEP} {HP : Type uHP}
    [NormedAddCommGroup EP] [NormedSpace ℝ EP] [TopologicalSpace HP]
    {G : Type uG} {B : Type uB} {P : Type uP}
    [Group G] [TopologicalSpace G] [TopologicalSpace B] [TopologicalSpace P]
    [IsTopologicalGroup G]
    {IB : ModelWithCorners ℝ EB HB}
    {IG : ModelWithCorners ℝ EG HG}
    {IP : ModelWithCorners ℝ EP HP}
    [ChartedSpace HB B] [IsManifold IB ∞ B]
    [ChartedSpace HG G] [LieGroup IG ∞ G]
    [ChartedSpace HP P] [IsManifold IP ∞ P]
    {torsor : PrincipalBundleTorsorData G B P}
    {bundle : TopologicalPrincipalBundleData torsor}
    {smoothBundle : SmoothPrincipalBundleData IB IG IP torsor bundle}

/-- The invariant adjoint-fiber pairing is unchanged when both arguments are transformed by the
same covariant induced gauge action. -/
theorem AdjointBundle.fiberPairing_inducedAdjointFiberAction
    (inner : InvariantInnerProductData (I := IG) (G := G))
    (gauge : SmoothGaugeTransformation smoothBundle) (b : B)
    (X Y : AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :
    AdjointBundle.fiberPairing bundle inner b
        (gauge.inducedAdjointFiberAction b X)
        (gauge.inducedAdjointFiberAction b Y) =
      AdjointBundle.fiberPairing bundle inner b X Y := by
  letI : AddCommGroup (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
    AdjointBundle.fiberAddCommGroup (I := IG) bundle b
  letI : Module ℝ (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
    AdjointBundle.fiberModule (I := IG) bundle b
  letI : TopologicalSpace (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
    AdjointBundle.fiberTopology (I := IG) bundle b
  let chart := bundle.trivializationAt b
  let hb := bundle.mem_baseSet_trivializationAt b
  let coordinate :=
    AdjointBundle.fiberModelContinuousLinearEquiv (IG := IG) (bundle := bundle) chart hb
  let p := principalBundleLocalSection chart b
  let g := gauge.associatedGaugeFunction p
  have hX :
      AdjointBundle.selectedFiberModelEquiv (I := IG) bundle b
          (gauge.inducedAdjointFiberAction b X) =
        YangMills.Mathematics.lieGroupAdjointCoordinatesEquiv (I := IG) g
          (AdjointBundle.selectedFiberModelEquiv (I := IG) bundle b X) := by
    simpa [AdjointBundle.selectedFiberModelEquiv, coordinate, chart, hb, p, g] using
      (inducedAdjointFiberAction_coordinate gauge b X)
  have hY :
      AdjointBundle.selectedFiberModelEquiv (I := IG) bundle b
          (gauge.inducedAdjointFiberAction b Y) =
        YangMills.Mathematics.lieGroupAdjointCoordinatesEquiv (I := IG) g
          (AdjointBundle.selectedFiberModelEquiv (I := IG) bundle b Y) := by
    simpa [AdjointBundle.selectedFiberModelEquiv, coordinate, chart, hb, p, g] using
      (inducedAdjointFiberAction_coordinate gauge b Y)
  unfold AdjointBundle.fiberPairing
  rw [hX, hY]
  change inner.pairing
      (YangMills.Mathematics.lieGroupAdjoint IG g
        ((YangMills.Mathematics.groupLieAlgebraModelEquiv IG).symm
          (AdjointBundle.selectedFiberModelEquiv (I := IG) bundle b X)))
      (YangMills.Mathematics.lieGroupAdjoint IG g
        ((YangMills.Mathematics.groupLieAlgebraModelEquiv IG).symm
          (AdjointBundle.selectedFiberModelEquiv (I := IG) bundle b Y))) =
    inner.pairing
      ((YangMills.Mathematics.groupLieAlgebraModelEquiv IG).symm
        (AdjointBundle.selectedFiberModelEquiv (I := IG) bundle b X))
      ((YangMills.Mathematics.groupLieAlgebraModelEquiv IG).symm
        (AdjointBundle.selectedFiberModelEquiv (I := IG) bundle b Y))
  exact inner.adjoint_invariant g _ _

/-- The quadratic self-pairing is invariant under the covariant induced gauge action. -/
theorem AdjointBundle.fiberPairing_self_inducedAdjointFiberAction
    (inner : InvariantInnerProductData (I := IG) (G := G))
    (gauge : SmoothGaugeTransformation smoothBundle) (b : B)
    (X : AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :
    AdjointBundle.fiberPairing bundle inner b
        (gauge.inducedAdjointFiberAction b X)
        (gauge.inducedAdjointFiberAction b X) =
      AdjointBundle.fiberPairing bundle inner b X X :=
  AdjointBundle.fiberPairing_inducedAdjointFiberAction inner gauge b X X

end

end YangMills.Geometry
