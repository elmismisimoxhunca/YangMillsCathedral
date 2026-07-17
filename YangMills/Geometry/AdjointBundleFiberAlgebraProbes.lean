/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Geometry.AdjointBundleFiberAlgebra

/-!
# Hostile probes for dependent adjoint-fiber algebra
-/

namespace YangMills.Geometry.Probes

open Set
open scoped Manifold ContDiff Bundle

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
    (bundle : TopologicalPrincipalBundleData torsor)

/-- A fiber coordinate followed by its inverse cannot change the fiber point. -/
theorem broken_adjointBundle_fiberModelEquiv_roundTrip_blocked
    (chart : PrincipalBundleLocalTrivialization torsor)
    {b : B} (hb : b ∈ chart.baseSet)
    (z : AdjointBundle.Fiber (I := I) (torsor := torsor) b)
    (mismatch : (AdjointBundle.fiberModelEquiv (I := I) bundle chart hb).symm
      (AdjointBundle.fiberModelEquiv (I := I) bundle chart hb z) ≠ z) : False :=
  mismatch ((AdjointBundle.fiberModelEquiv (I := I) bundle chart hb).symm_apply_apply z)

/-- Under the named transported structures, the selected coordinate must preserve addition. -/
theorem nonadditive_adjointBundle_selectedFiberCoordinate_blocked (b : B) :
    letI : AddCommGroup (AdjointBundle.Fiber (I := I) (torsor := torsor) b) :=
      AdjointBundle.fiberAddCommGroup (I := I) bundle b
    letI : Module ℝ (AdjointBundle.Fiber (I := I) (torsor := torsor) b) :=
      AdjointBundle.fiberModule (I := I) bundle b
    ∀ x y : AdjointBundle.Fiber (I := I) (torsor := torsor) b,
      AdjointBundle.selectedFiberModelEquiv (I := I) bundle b (x + y) =
        AdjointBundle.selectedFiberModelEquiv (I := I) bundle b x +
          AdjointBundle.selectedFiberModelEquiv (I := I) bundle b y := by
  letI : AddCommGroup (AdjointBundle.Fiber (I := I) (torsor := torsor) b) :=
    AdjointBundle.fiberAddCommGroup (I := I) bundle b
  letI : Module ℝ (AdjointBundle.Fiber (I := I) (torsor := torsor) b) :=
    AdjointBundle.fiberModule (I := I) bundle b
  intro x y
  exact (AdjointBundle.selectedFiberLinearEquiv (I := I) bundle b).map_add x y

/-- The same selected coordinate must preserve real scalar multiplication. -/
theorem nonscalar_adjointBundle_selectedFiberCoordinate_blocked (b : B) :
    letI : AddCommGroup (AdjointBundle.Fiber (I := I) (torsor := torsor) b) :=
      AdjointBundle.fiberAddCommGroup (I := I) bundle b
    letI : Module ℝ (AdjointBundle.Fiber (I := I) (torsor := torsor) b) :=
      AdjointBundle.fiberModule (I := I) bundle b
    ∀ (c : ℝ) (x : AdjointBundle.Fiber (I := I) (torsor := torsor) b),
      AdjointBundle.selectedFiberModelEquiv (I := I) bundle b (c • x) =
        c • AdjointBundle.selectedFiberModelEquiv (I := I) bundle b x := by
  letI : AddCommGroup (AdjointBundle.Fiber (I := I) (torsor := torsor) b) :=
    AdjointBundle.fiberAddCommGroup (I := I) bundle b
  letI : Module ℝ (AdjointBundle.Fiber (I := I) (torsor := torsor) b) :=
    AdjointBundle.fiberModule (I := I) bundle b
  intro c x
  exact (AdjointBundle.selectedFiberLinearEquiv (I := I) bundle b).map_smul c x

/-- The selected coordinate cannot send fiber zero to a nonzero model vector. -/
theorem nonzero_adjointBundle_selectedFiberZero_blocked (b : B) :
    letI : AddCommGroup (AdjointBundle.Fiber (I := I) (torsor := torsor) b) :=
      AdjointBundle.fiberAddCommGroup (I := I) bundle b
    letI : Module ℝ (AdjointBundle.Fiber (I := I) (torsor := torsor) b) :=
      AdjointBundle.fiberModule (I := I) bundle b
    AdjointBundle.selectedFiberModelEquiv (I := I) bundle b
      (0 : AdjointBundle.Fiber (I := I) (torsor := torsor) b) = 0 := by
  letI : AddCommGroup (AdjointBundle.Fiber (I := I) (torsor := torsor) b) :=
    AdjointBundle.fiberAddCommGroup (I := I) bundle b
  letI : Module ℝ (AdjointBundle.Fiber (I := I) (torsor := torsor) b) :=
    AdjointBundle.fiberModule (I := I) bundle b
  exact (AdjointBundle.selectedFiberLinearEquiv (I := I) bundle b).map_zero

end

end YangMills.Geometry.Probes
