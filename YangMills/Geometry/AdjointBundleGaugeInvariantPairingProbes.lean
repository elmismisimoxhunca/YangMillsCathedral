/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Geometry.AdjointBundleGaugeInvariantPairing

/-!
# Hostile probes for gauge invariance of the adjoint-fiber pairing
-/

namespace YangMills.Geometry.AdjointBundleGaugeInvariantPairing.Probes

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

/-- Both arguments of the exact fiber pairing transform together. -/
theorem exact_pairing_invariance
    (inner : InvariantInnerProductData (I := IG) (G := G))
    (gauge : SmoothGaugeTransformation smoothBundle) (b : B)
    (X Y : AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :
    AdjointBundle.fiberPairing bundle inner b
        (gauge.inducedAdjointFiberAction b X)
        (gauge.inducedAdjointFiberAction b Y) =
      AdjointBundle.fiberPairing bundle inner b X Y :=
  AdjointBundle.fiberPairing_inducedAdjointFiberAction inner gauge b X Y

/-- The exact quadratic fiber value is gauge invariant. -/
theorem exact_quadratic_invariance
    (inner : InvariantInnerProductData (I := IG) (G := G))
    (gauge : SmoothGaugeTransformation smoothBundle) (b : B)
    (X : AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :
    AdjointBundle.fiberPairing bundle inner b
        (gauge.inducedAdjointFiberAction b X)
        (gauge.inducedAdjointFiberAction b X) =
      AdjointBundle.fiberPairing bundle inner b X X :=
  AdjointBundle.fiberPairing_self_inducedAdjointFiberAction inner gauge b X

/-- A claimed change of the simultaneously transformed pairing is inconsistent. -/
theorem changed_pairing_blocked
    (inner : InvariantInnerProductData (I := IG) (G := G))
    (gauge : SmoothGaugeTransformation smoothBundle) (b : B)
    (X Y : AdjointBundle.Fiber (I := IG) (torsor := torsor) b)
    (wrong :
      AdjointBundle.fiberPairing bundle inner b
          (gauge.inducedAdjointFiberAction b X)
          (gauge.inducedAdjointFiberAction b Y) ≠
        AdjointBundle.fiberPairing bundle inner b X Y) : False :=
  wrong (AdjointBundle.fiberPairing_inducedAdjointFiberAction inner gauge b X Y)

/-- A claimed change of the transformed quadratic value is inconsistent. -/
theorem changed_quadratic_blocked
    (inner : InvariantInnerProductData (I := IG) (G := G))
    (gauge : SmoothGaugeTransformation smoothBundle) (b : B)
    (X : AdjointBundle.Fiber (I := IG) (torsor := torsor) b)
    (wrong :
      AdjointBundle.fiberPairing bundle inner b
          (gauge.inducedAdjointFiberAction b X)
          (gauge.inducedAdjointFiberAction b X) ≠
        AdjointBundle.fiberPairing bundle inner b X X) : False :=
  wrong (AdjointBundle.fiberPairing_self_inducedAdjointFiberAction inner gauge b X)

end

end YangMills.Geometry.AdjointBundleGaugeInvariantPairing.Probes
