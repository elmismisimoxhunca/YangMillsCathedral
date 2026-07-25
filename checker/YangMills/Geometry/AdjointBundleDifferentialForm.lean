/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Geometry.AdjointBundleVectorBundle
import Mathlib.Analysis.Normed.Module.Alternating.Basic

/-!
# Pointwise adjoint-bundle-valued differential forms

This file defines the pointwise carrier `Ωᵏ(B; ad P)`: at each base point, a continuous alternating
map from tangent vectors into the actual dependent fiber of the adjoint orbit quotient. Designated
fiber coordinates are first packaged as continuous linear equivalences whose underlying map remains
exactly the quotient-derived coordinate.

Smoothness, covariant differentiation, and descent of principal curvature are deliberately not
claimed here.
-/

namespace YangMills.Geometry

open Set
open scoped Manifold ContDiff Bundle Topology

universe uEG uHG uEB uHB uG uB uP

noncomputable section

variable
    {EG : Type uEG} {HG : Type uHG}
    [NormedAddCommGroup EG] [NormedSpace ℝ EG] [TopologicalSpace HG]
    {EB : Type uEB} {HB : Type uHB}
    [NormedAddCommGroup EB] [NormedSpace ℝ EB] [TopologicalSpace HB]
    {G : Type uG} {B : Type uB} {P : Type uP}
    [Group G] [TopologicalSpace G] [TopologicalSpace B] [TopologicalSpace P]
    [IsTopologicalGroup G]
    {IG : ModelWithCorners ℝ EG HG}
    {IB : ModelWithCorners ℝ EB HB}
    [ChartedSpace HG G] [LieGroup IG ∞ G]
    [ChartedSpace HB B]
    {torsor : PrincipalBundleTorsorData G B P}
    (bundle : TopologicalPrincipalBundleData torsor)

/-- The exact designated fiber coordinate as a continuous linear equivalence for the named fiber
algebra and topology. -/
def AdjointBundle.fiberModelContinuousLinearEquiv
    (chart : PrincipalBundleLocalTrivialization torsor)
    {b : B} (hb : b ∈ chart.baseSet) :
    letI : AddCommGroup (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
      AdjointBundle.fiberAddCommGroup (I := IG) bundle b
    letI : Module ℝ (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
      AdjointBundle.fiberModule (I := IG) bundle b
    letI : TopologicalSpace (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
      AdjointBundle.fiberTopology (I := IG) bundle b
    AdjointBundle.Fiber (I := IG) (torsor := torsor) b ≃L[ℝ] EG := by
  letI (x : B) : AddCommGroup (AdjointBundle.Fiber (I := IG) (torsor := torsor) x) :=
    AdjointBundle.fiberAddCommGroup (I := IG) bundle x
  letI (x : B) : Module ℝ (AdjointBundle.Fiber (I := IG) (torsor := torsor) x) :=
    AdjointBundle.fiberModule (I := IG) bundle x
  letI (x : B) : TopologicalSpace (AdjointBundle.Fiber (I := IG) (torsor := torsor) x) :=
    AdjointBundle.fiberTopology (I := IG) bundle x
  letI : TopologicalSpace
      (Bundle.TotalSpace EG (AdjointBundle.Fiber (I := IG) (torsor := torsor))) :=
    AdjointBundle.dependentTotalSpaceTopology (I := IG) (torsor := torsor)
  letI : FiberBundle EG (AdjointBundle.Fiber (I := IG) (torsor := torsor)) :=
    AdjointBundle.dependentFiberBundle (I := IG) bundle
  let e := AdjointBundle.dependentModelBundleTrivialization (I := IG) bundle chart
  letI : Bundle.Trivialization.IsLinear ℝ e :=
    AdjointBundle.dependentModelBundleTrivialization_isLinear (I := IG) bundle chart
  exact e.continuousLinearEquivAt ℝ b hb

/-- The continuous-linear packaging has the unchanged quotient-derived coordinate as its underlying
map. -/
@[simp]
theorem AdjointBundle.fiberModelContinuousLinearEquiv_apply
    (chart : PrincipalBundleLocalTrivialization torsor)
    {b : B} (hb : b ∈ chart.baseSet)
    (z : AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :
    letI : AddCommGroup (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
      AdjointBundle.fiberAddCommGroup (I := IG) bundle b
    letI : Module ℝ (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
      AdjointBundle.fiberModule (I := IG) bundle b
    letI : TopologicalSpace (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
      AdjointBundle.fiberTopology (I := IG) bundle b
    AdjointBundle.fiberModelContinuousLinearEquiv (IG := IG) bundle chart hb z =
      AdjointBundle.fiberModelEquiv (I := IG) bundle chart hb z := by
  letI : AddCommGroup (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
    AdjointBundle.fiberAddCommGroup (I := IG) bundle b
  letI : Module ℝ (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
    AdjointBundle.fiberModule (I := IG) bundle b
  letI : TopologicalSpace (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
    AdjointBundle.fiberTopology (I := IG) bundle b
  rfl

/-- A degree-`k` pointwise differential form on the base with values in the actual dependent adjoint
bundle fiber. Smoothness is intentionally separate. -/
def AdjointBundle.DifferentialForm (k : ℕ) :=
  (b : B) →
    letI : AddCommGroup (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
      AdjointBundle.fiberAddCommGroup (I := IG) bundle b
    letI : Module ℝ (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
      AdjointBundle.fiberModule (I := IG) bundle b
    letI : TopologicalSpace (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
      AdjointBundle.fiberTopology (I := IG) bundle b
    ContinuousAlternatingMap ℝ (TangentSpace IB b)
      (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) (Fin k)

namespace AdjointBundle.DifferentialForm

variable {bundle} {k : ℕ}

/-- Coordinate a pointwise adjoint-bundle-valued form in one designated exact fiber chart. -/
def inCoordinates
    (form : AdjointBundle.DifferentialForm (IG := IG) (IB := IB) bundle k)
    (chart : PrincipalBundleLocalTrivialization torsor)
    {b : B} (hb : b ∈ chart.baseSet) :
    ContinuousAlternatingMap ℝ (TangentSpace IB b) EG (Fin k) := by
  letI : AddCommGroup (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
    AdjointBundle.fiberAddCommGroup (I := IG) bundle b
  letI : Module ℝ (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
    AdjointBundle.fiberModule (I := IG) bundle b
  letI : TopologicalSpace (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
    AdjointBundle.fiberTopology (I := IG) bundle b
  let coordinate :=
    AdjointBundle.fiberModelContinuousLinearEquiv (IG := IG) bundle chart hb
  exact coordinate.toContinuousLinearMap.compContinuousAlternatingMap (form b)

/-- Evaluation in a designated coordinate is exactly coordinate evaluation of the original quotient
fiber value. -/
@[simp]
theorem inCoordinates_apply
    (form : AdjointBundle.DifferentialForm (IG := IG) (IB := IB) bundle k)
    (chart : PrincipalBundleLocalTrivialization torsor)
    {b : B} (hb : b ∈ chart.baseSet)
    (v : Fin k → TangentSpace IB b) :
    inCoordinates form chart hb v =
      AdjointBundle.fiberModelEquiv (I := IG) bundle chart hb ((form b) v) := by
  letI : AddCommGroup (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
    AdjointBundle.fiberAddCommGroup (I := IG) bundle b
  letI : Module ℝ (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
    AdjointBundle.fiberModule (I := IG) bundle b
  letI : TopologicalSpace (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
    AdjointBundle.fiberTopology (I := IG) bundle b
  rfl

/-- Every value lies over the input base point by construction of the dependent codomain. -/
theorem projection_apply
    (form : AdjointBundle.DifferentialForm (IG := IG) (IB := IB) bundle k)
    (b : B) (v : Fin k → TangentSpace IB b) :
    AdjointBundle.projection torsor (((form b) v).1) = b :=
  ((form b) v).2

/-- The pointwise zero adjoint-bundle-valued form. -/
def zero (bundle : TopologicalPrincipalBundleData torsor) (k : ℕ) :
    AdjointBundle.DifferentialForm (IG := IG) (IB := IB) bundle k :=
  fun b => by
    letI : AddCommGroup (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
      AdjointBundle.fiberAddCommGroup (I := IG) bundle b
    letI : Module ℝ (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
      AdjointBundle.fiberModule (I := IG) bundle b
    letI : TopologicalSpace (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
      AdjointBundle.fiberTopology (I := IG) bundle b
    exact 0

/-- The named zero form evaluates to the named zero in every dependent fiber. -/
@[simp]
theorem zero_apply
    (bundle : TopologicalPrincipalBundleData torsor) (k : ℕ)
    (b : B) (v : Fin k → TangentSpace IB b) :
    letI : AddCommGroup (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
      AdjointBundle.fiberAddCommGroup (I := IG) bundle b
    letI : Module ℝ (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
      AdjointBundle.fiberModule (I := IG) bundle b
    letI : TopologicalSpace (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
      AdjointBundle.fiberTopology (I := IG) bundle b
    (zero (IG := IG) (IB := IB) bundle k b) v = 0 := by
  rfl

/-- A degree-two adjoint-bundle-valued form vanishes on a repeated tangent vector. -/
theorem evalTwo_same
    (form : AdjointBundle.DifferentialForm (IG := IG) (IB := IB) bundle 2)
    (b : B) (v : TangentSpace IB b) :
    letI : AddCommGroup (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
      AdjointBundle.fiberAddCommGroup (I := IG) bundle b
    letI : Module ℝ (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
      AdjointBundle.fiberModule (I := IG) bundle b
    letI : TopologicalSpace (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
      AdjointBundle.fiberTopology (I := IG) bundle b
    (form b) (fun _ => v) = 0 := by
  letI : AddCommGroup (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
    AdjointBundle.fiberAddCommGroup (I := IG) bundle b
  letI : Module ℝ (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
    AdjointBundle.fiberModule (I := IG) bundle b
  letI : TopologicalSpace (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
    AdjointBundle.fiberTopology (I := IG) bundle b
  exact (form b).map_eq_zero_of_eq (fun _ => v) (i := 0) (j := 1) rfl (by decide)

end AdjointBundle.DifferentialForm

end

end YangMills.Geometry
