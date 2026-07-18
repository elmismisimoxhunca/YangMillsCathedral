/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Geometry.AdjointBundleInvariantPairing

/-!
# Bilinear-map packaging of the invariant adjoint-fiber pairing

The exact selected quotient coordinate is already a linear equivalence for the named transported
fiber structures. Composing it with the explicit model/Lie-algebra equivalence gives a linear
identification with the gauge Lie algebra. The invariant pairing can therefore be packaged as an
iterated `LinearMap` on each actual dependent adjoint fiber.

The resulting linear map is proved to evaluate to the previously established quotient-coherent
`AdjointBundle.fiberPairing`; it is not a replacement pairing or a global inner-product instance.
-/

namespace YangMills.Geometry

open scoped ContDiff Manifold

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

/-- The actual dependent adjoint fiber identified linearly with the gauge Lie algebra through the
exact selected quotient coordinate and the explicit model transport. -/
def selectedFiberLieAlgebraLinearEquiv (b : B) :
    letI : AddCommGroup (AdjointBundle.Fiber (I := I) (torsor := torsor) b) :=
      AdjointBundle.fiberAddCommGroup (I := I) bundle b
    letI : Module ℝ (AdjointBundle.Fiber (I := I) (torsor := torsor) b) :=
      AdjointBundle.fiberModule (I := I) bundle b
    AdjointBundle.Fiber (I := I) (torsor := torsor) b ≃ₗ[ℝ] GroupLieAlgebra I G := by
  letI : AddCommGroup (AdjointBundle.Fiber (I := I) (torsor := torsor) b) :=
    AdjointBundle.fiberAddCommGroup (I := I) bundle b
  letI : Module ℝ (AdjointBundle.Fiber (I := I) (torsor := torsor) b) :=
    AdjointBundle.fiberModule (I := I) bundle b
  exact (AdjointBundle.selectedFiberLinearEquiv (I := I) bundle b).trans
    (YangMills.Mathematics.groupLieAlgebraModelEquiv I).symm.toLinearEquiv

/-- The packaged fiber/Lie-algebra equivalence retains the exact selected quotient coordinate. -/
@[simp]
theorem selectedFiberLieAlgebraLinearEquiv_apply
    (b : B) (X : AdjointBundle.Fiber (I := I) (torsor := torsor) b) :
    letI : AddCommGroup (AdjointBundle.Fiber (I := I) (torsor := torsor) b) :=
      AdjointBundle.fiberAddCommGroup (I := I) bundle b
    letI : Module ℝ (AdjointBundle.Fiber (I := I) (torsor := torsor) b) :=
      AdjointBundle.fiberModule (I := I) bundle b
    selectedFiberLieAlgebraLinearEquiv bundle b X =
      (YangMills.Mathematics.groupLieAlgebraModelEquiv I).symm
        (AdjointBundle.selectedFiberModelEquiv (I := I) bundle b X) := by
  rfl

/-- The invariant pairing packaged as a bilinear map on one actual dependent adjoint fiber. -/
def fiberPairingLinearMap
    (inner : InvariantInnerProductData (I := I) (G := G)) (b : B) :
    letI : AddCommGroup (AdjointBundle.Fiber (I := I) (torsor := torsor) b) :=
      AdjointBundle.fiberAddCommGroup (I := I) bundle b
    letI : Module ℝ (AdjointBundle.Fiber (I := I) (torsor := torsor) b) :=
      AdjointBundle.fiberModule (I := I) bundle b
    AdjointBundle.Fiber (I := I) (torsor := torsor) b →ₗ[ℝ]
      AdjointBundle.Fiber (I := I) (torsor := torsor) b →ₗ[ℝ] ℝ := by
  letI : AddCommGroup (AdjointBundle.Fiber (I := I) (torsor := torsor) b) :=
    AdjointBundle.fiberAddCommGroup (I := I) bundle b
  letI : Module ℝ (AdjointBundle.Fiber (I := I) (torsor := torsor) b) :=
    AdjointBundle.fiberModule (I := I) bundle b
  let coordinate := selectedFiberLieAlgebraLinearEquiv (I := I) bundle b
  exact LinearMap.mk₂ ℝ
    (fun X Y => inner.pairing (coordinate X) (coordinate Y))
    (fun _ _ _ => by simp) (fun _ _ _ => by simp)
    (fun _ _ _ => by simp) (fun _ _ _ => by simp)

/-- Bilinear-map packaging does not change the established quotient-coherent fiber pairing. -/
@[simp]
theorem fiberPairingLinearMap_apply
    (inner : InvariantInnerProductData (I := I) (G := G)) (b : B)
    (X Y : AdjointBundle.Fiber (I := I) (torsor := torsor) b) :
    letI : AddCommGroup (AdjointBundle.Fiber (I := I) (torsor := torsor) b) :=
      AdjointBundle.fiberAddCommGroup (I := I) bundle b
    letI : Module ℝ (AdjointBundle.Fiber (I := I) (torsor := torsor) b) :=
      AdjointBundle.fiberModule (I := I) bundle b
    fiberPairingLinearMap bundle inner b X Y = fiberPairing bundle inner b X Y := by
  rfl

end AdjointBundle

end

end YangMills.Geometry
