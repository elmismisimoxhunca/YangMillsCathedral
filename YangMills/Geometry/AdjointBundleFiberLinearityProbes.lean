/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Geometry.AdjointBundleFiberLinearity

/-!
# Hostile probes for designated adjoint-fiber coordinate linearity
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

/-- An arbitrary designated coordinate cannot be disconnected from its derived linear equivalence. -/
theorem nonlinearReplacement_adjointBundle_fiberCoordinate_blocked
    (chart : PrincipalBundleLocalTrivialization torsor)
    {b : B} (hb : b ∈ chart.baseSet)
    (z : AdjointBundle.Fiber (I := I) (torsor := torsor) b)
    (mismatch :
      letI : AddCommGroup (AdjointBundle.Fiber (I := I) (torsor := torsor) b) :=
        AdjointBundle.fiberAddCommGroup (I := I) bundle b
      letI : Module ℝ (AdjointBundle.Fiber (I := I) (torsor := torsor) b) :=
        AdjointBundle.fiberModule (I := I) bundle b
      AdjointBundle.fiberModelLinearEquiv (I := I) bundle chart hb z ≠
        AdjointBundle.fiberModelEquiv (I := I) bundle chart hb z) : False := by
  letI : AddCommGroup (AdjointBundle.Fiber (I := I) (torsor := torsor) b) :=
    AdjointBundle.fiberAddCommGroup (I := I) bundle b
  letI : Module ℝ (AdjointBundle.Fiber (I := I) (torsor := torsor) b) :=
    AdjointBundle.fiberModule (I := I) bundle b
  exact mismatch (AdjointBundle.fiberModelLinearEquiv_apply
    (I := I) bundle chart hb z)

/-- Every designated quotient-derived coordinate must preserve fiber addition. -/
theorem nonadditive_adjointBundle_arbitraryFiberCoordinate_blocked
    (chart : PrincipalBundleLocalTrivialization torsor)
    {b : B} (hb : b ∈ chart.baseSet) :
    letI : AddCommGroup (AdjointBundle.Fiber (I := I) (torsor := torsor) b) :=
      AdjointBundle.fiberAddCommGroup (I := I) bundle b
    letI : Module ℝ (AdjointBundle.Fiber (I := I) (torsor := torsor) b) :=
      AdjointBundle.fiberModule (I := I) bundle b
    ∀ x y, AdjointBundle.fiberModelEquiv (I := I) bundle chart hb (x + y) =
      AdjointBundle.fiberModelEquiv (I := I) bundle chart hb x +
        AdjointBundle.fiberModelEquiv (I := I) bundle chart hb y := by
  letI : AddCommGroup (AdjointBundle.Fiber (I := I) (torsor := torsor) b) :=
    AdjointBundle.fiberAddCommGroup (I := I) bundle b
  letI : Module ℝ (AdjointBundle.Fiber (I := I) (torsor := torsor) b) :=
    AdjointBundle.fiberModule (I := I) bundle b
  intro x y
  rw [← AdjointBundle.fiberModelLinearEquiv_apply (I := I) bundle chart hb,
    ← AdjointBundle.fiberModelLinearEquiv_apply (I := I) bundle chart hb,
    ← AdjointBundle.fiberModelLinearEquiv_apply (I := I) bundle chart hb]
  exact map_add _ x y

/-- Every designated quotient-derived coordinate must preserve real scalar multiplication. -/
theorem nonscalar_adjointBundle_arbitraryFiberCoordinate_blocked
    (chart : PrincipalBundleLocalTrivialization torsor)
    {b : B} (hb : b ∈ chart.baseSet) :
    letI : AddCommGroup (AdjointBundle.Fiber (I := I) (torsor := torsor) b) :=
      AdjointBundle.fiberAddCommGroup (I := I) bundle b
    letI : Module ℝ (AdjointBundle.Fiber (I := I) (torsor := torsor) b) :=
      AdjointBundle.fiberModule (I := I) bundle b
    ∀ (c : ℝ) x, AdjointBundle.fiberModelEquiv (I := I) bundle chart hb (c • x) =
      c • AdjointBundle.fiberModelEquiv (I := I) bundle chart hb x := by
  letI : AddCommGroup (AdjointBundle.Fiber (I := I) (torsor := torsor) b) :=
    AdjointBundle.fiberAddCommGroup (I := I) bundle b
  letI : Module ℝ (AdjointBundle.Fiber (I := I) (torsor := torsor) b) :=
    AdjointBundle.fiberModule (I := I) bundle b
  intro c x
  rw [← AdjointBundle.fiberModelLinearEquiv_apply (I := I) bundle chart hb,
    ← AdjointBundle.fiberModelLinearEquiv_apply (I := I) bundle chart hb]
  exact map_smul _ c x

end

end YangMills.Geometry.Probes
