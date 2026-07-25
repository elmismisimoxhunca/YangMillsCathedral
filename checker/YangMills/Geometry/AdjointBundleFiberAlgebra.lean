/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Geometry.AdjointBundleDependentFiberTopology
import Mathlib.Algebra.Module.Equiv.Basic

/-!
# Linear algebra on dependent adjoint fibers

Each dependent quotient fiber is identified with the declared Lie-algebra model through a chosen
designated associated trivialization. The principal bundle's selected chart at each base point then
transports the real vector-space structure to that fiber.

All structures are named values, not global instances, because the selected atlas is explicit data.
No `FiberBundle`, `VectorBundle`, or smooth bundle is installed here.
-/

namespace YangMills.Geometry

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

/-- Fiber coordinate equivalence induced by any designated chart whose base set contains `b`. -/
def AdjointBundle.fiberModelEquiv
    (chart : PrincipalBundleLocalTrivialization torsor)
    {b : B} (hb : b ∈ chart.baseSet) :
    AdjointBundle.Fiber (I := I) (torsor := torsor) b ≃ E where
  toFun z := (AdjointBundle.modelBundleTrivialization (I := I) bundle chart z.1).2
  invFun X := by
    let e := AdjointBundle.modelBundleTrivialization (I := I) bundle chart
    let z := e.toOpenPartialHomeomorph.symm (b, X)
    have targetMem : (b, X) ∈ e.target := e.mem_target.mpr hb
    exact ⟨z, e.proj_symm_apply targetMem⟩
  left_inv z := by
    let e := AdjointBundle.modelBundleTrivialization (I := I) bundle chart
    have sourceMem : z.1 ∈ e.source := by
      apply e.mem_source.mpr
      rw [z.2]
      exact hb
    apply Subtype.ext
    change e.toOpenPartialHomeomorph.symm (b, (e z.1).2) = z.1
    have pair_eq : (b, (e z.1).2) = e z.1 := by
      apply Prod.ext
      · calc
          b = AdjointBundle.projection torsor z.1 := z.2.symm
          _ = (e z.1).1 := (e.coe_fst sourceMem).symm
      · rfl
    calc
      e.toOpenPartialHomeomorph.symm (b, (e z.1).2) =
          e.toOpenPartialHomeomorph.symm (e z.1) := congrArg _ pair_eq
      _ = z.1 := e.toOpenPartialHomeomorph.left_inv sourceMem
  right_inv X := by
    let e := AdjointBundle.modelBundleTrivialization (I := I) bundle chart
    have targetMem : (b, X) ∈ e.target := e.mem_target.mpr hb
    change (e (e.toOpenPartialHomeomorph.symm (b, X))).2 = X
    exact congrArg Prod.snd (e.toOpenPartialHomeomorph.right_inv targetMem)

/-- The fiber equivalence selected canonically from the principal bundle's explicit atlas data. -/
def AdjointBundle.selectedFiberModelEquiv (b : B) :
    AdjointBundle.Fiber (I := I) (torsor := torsor) b ≃ E :=
  AdjointBundle.fiberModelEquiv (I := I) bundle (bundle.trivializationAt b)
    (bundle.mem_baseSet_trivializationAt b)

/-- Named additive commutative group structure transported from the model through the selected
fiber equivalence. -/
@[reducible]
def AdjointBundle.fiberAddCommGroup (b : B) :
    AddCommGroup (AdjointBundle.Fiber (I := I) (torsor := torsor) b) :=
  (AdjointBundle.selectedFiberModelEquiv (I := I) bundle b).addCommGroup

/-- Named real module structure transported through the same selected fiber equivalence. -/
@[reducible]
def AdjointBundle.fiberModule (b : B) :
    @Module ℝ (AdjointBundle.Fiber (I := I) (torsor := torsor) b) _
      (AdjointBundle.fiberAddCommGroup (I := I) bundle b).toAddCommMonoid := by
  letI : AddCommGroup (AdjointBundle.Fiber (I := I) (torsor := torsor) b) :=
    AdjointBundle.fiberAddCommGroup (I := I) bundle b
  exact (AdjointBundle.selectedFiberModelEquiv (I := I) bundle b).module ℝ

/-- With the named transported structures installed locally, the selected fiber coordinate is a
linear equivalence to the declared model. -/
def AdjointBundle.selectedFiberLinearEquiv (b : B) :
    letI : AddCommGroup (AdjointBundle.Fiber (I := I) (torsor := torsor) b) :=
      AdjointBundle.fiberAddCommGroup (I := I) bundle b
    letI : Module ℝ (AdjointBundle.Fiber (I := I) (torsor := torsor) b) :=
      AdjointBundle.fiberModule (I := I) bundle b
    AdjointBundle.Fiber (I := I) (torsor := torsor) b ≃ₗ[ℝ] E := by
  letI : AddCommGroup (AdjointBundle.Fiber (I := I) (torsor := torsor) b) :=
    AdjointBundle.fiberAddCommGroup (I := I) bundle b
  letI : Module ℝ (AdjointBundle.Fiber (I := I) (torsor := torsor) b) :=
    AdjointBundle.fiberModule (I := I) bundle b
  exact (AdjointBundle.selectedFiberModelEquiv (I := I) bundle b).linearEquiv ℝ

end

end YangMills.Geometry
