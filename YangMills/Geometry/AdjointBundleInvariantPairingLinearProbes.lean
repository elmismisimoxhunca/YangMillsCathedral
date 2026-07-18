/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Geometry.AdjointBundleInvariantPairingLinear

/-!
# Hostile probes for bilinear adjoint-fiber pairing packaging
-/

namespace YangMills.Geometry.Probes

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
    (inner : InvariantInnerProductData (I := I) (G := G))

/-- The fiber/Lie-algebra linear equivalence cannot replace the exact selected quotient coordinate. -/
theorem selectedFiberLieAlgebraCoordinate_replacement_blocked
    (b : B) (X : AdjointBundle.Fiber (I := I) (torsor := torsor) b)
    (mismatch :
      letI : AddCommGroup (AdjointBundle.Fiber (I := I) (torsor := torsor) b) :=
        AdjointBundle.fiberAddCommGroup (I := I) bundle b
      letI : Module ℝ (AdjointBundle.Fiber (I := I) (torsor := torsor) b) :=
        AdjointBundle.fiberModule (I := I) bundle b
      AdjointBundle.selectedFiberLieAlgebraLinearEquiv bundle b X ≠
        (YangMills.Mathematics.groupLieAlgebraModelEquiv I).symm
          (AdjointBundle.selectedFiberModelEquiv (I := I) bundle b X)) : False := by
  letI : AddCommGroup (AdjointBundle.Fiber (I := I) (torsor := torsor) b) :=
    AdjointBundle.fiberAddCommGroup (I := I) bundle b
  letI : Module ℝ (AdjointBundle.Fiber (I := I) (torsor := torsor) b) :=
    AdjointBundle.fiberModule (I := I) bundle b
  exact mismatch (AdjointBundle.selectedFiberLieAlgebraLinearEquiv_apply bundle b X)

/-- Bilinear packaging cannot change the exact quotient-coherent fiber pairing. -/
theorem fiberPairingLinearMap_replacement_blocked
    (b : B) (X Y : AdjointBundle.Fiber (I := I) (torsor := torsor) b)
    (mismatch :
      letI : AddCommGroup (AdjointBundle.Fiber (I := I) (torsor := torsor) b) :=
        AdjointBundle.fiberAddCommGroup (I := I) bundle b
      letI : Module ℝ (AdjointBundle.Fiber (I := I) (torsor := torsor) b) :=
        AdjointBundle.fiberModule (I := I) bundle b
      AdjointBundle.fiberPairingLinearMap bundle inner b X Y ≠
        AdjointBundle.fiberPairing bundle inner b X Y) : False := by
  letI : AddCommGroup (AdjointBundle.Fiber (I := I) (torsor := torsor) b) :=
    AdjointBundle.fiberAddCommGroup (I := I) bundle b
  letI : Module ℝ (AdjointBundle.Fiber (I := I) (torsor := torsor) b) :=
    AdjointBundle.fiberModule (I := I) bundle b
  exact mismatch (AdjointBundle.fiberPairingLinearMap_apply bundle inner b X Y)

/-- Positive rescaling cannot change the exact dependent-fiber pairing by any factor other than
the supplied scalar. -/
theorem malformed_fiberPairingScale_blocked
    (scalar : ℝ) (scalar_pos : 0 < scalar) (b : B)
    (mismatch :
      letI : AddCommGroup (AdjointBundle.Fiber (I := I) (torsor := torsor) b) :=
        AdjointBundle.fiberAddCommGroup (I := I) bundle b
      letI : Module ℝ (AdjointBundle.Fiber (I := I) (torsor := torsor) b) :=
        AdjointBundle.fiberModule (I := I) bundle b
      AdjointBundle.fiberPairingLinearMap
          bundle (inner.positiveScale scalar scalar_pos) b ≠
        scalar • AdjointBundle.fiberPairingLinearMap bundle inner b) : False := by
  letI : AddCommGroup (AdjointBundle.Fiber (I := I) (torsor := torsor) b) :=
    AdjointBundle.fiberAddCommGroup (I := I) bundle b
  letI : Module ℝ (AdjointBundle.Fiber (I := I) (torsor := torsor) b) :=
    AdjointBundle.fiberModule (I := I) bundle b
  exact mismatch
    (AdjointBundle.fiberPairingLinearMap_positiveScale
      bundle inner scalar scalar_pos b)

/-- The packaged pairing cannot fail additivity in its first argument. -/
theorem nonadditive_fiberPairingLinearMap_blocked
    (b : B) (X Y Z : AdjointBundle.Fiber (I := I) (torsor := torsor) b)
    (mismatch :
      letI : AddCommGroup (AdjointBundle.Fiber (I := I) (torsor := torsor) b) :=
        AdjointBundle.fiberAddCommGroup (I := I) bundle b
      letI : Module ℝ (AdjointBundle.Fiber (I := I) (torsor := torsor) b) :=
        AdjointBundle.fiberModule (I := I) bundle b
      AdjointBundle.fiberPairingLinearMap bundle inner b (X + Y) Z ≠
        AdjointBundle.fiberPairingLinearMap bundle inner b X Z +
          AdjointBundle.fiberPairingLinearMap bundle inner b Y Z) : False := by
  letI : AddCommGroup (AdjointBundle.Fiber (I := I) (torsor := torsor) b) :=
    AdjointBundle.fiberAddCommGroup (I := I) bundle b
  letI : Module ℝ (AdjointBundle.Fiber (I := I) (torsor := torsor) b) :=
    AdjointBundle.fiberModule (I := I) bundle b
  apply mismatch
  exact congrArg (fun linear => linear Z)
    (map_add (AdjointBundle.fiberPairingLinearMap bundle inner b) X Y)

end

end YangMills.Geometry.Probes
