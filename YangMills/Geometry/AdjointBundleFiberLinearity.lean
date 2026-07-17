/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Geometry.AdjointBundleFiberAlgebra
import YangMills.Geometry.AdjointBundleTransition

/-!
# Linearity of all designated adjoint-fiber coordinates

The fiber coordinate from any designated associated chart is compared to the selected coordinate at
the same base point. Their change is exactly the adjoint linear equivalence derived from the
principal overlap transition. Consequently every designated fiber coordinate is linear for the named
transported fiber structures.

No `FiberBundle`, `VectorBundle`, or smooth bundle is installed in this file.
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

/-- Linear change from the selected fiber coordinate at `b` to a requested designated chart. -/
def AdjointBundle.fiberCoordinateChangeLinearEquiv
    (chart : PrincipalBundleLocalTrivialization torsor) (b : B) : E ≃ₗ[ℝ] E :=
  (YangMills.Mathematics.lieGroupAdjointCoordinatesEquiv (I := I)
    (principalBundleTransition (bundle.trivializationAt b) chart (b, (1 : G))).2).toLinearEquiv

set_option backward.isDefEq.respectTransparency false in
/-- Every chart coordinate is exactly the selected coordinate followed by the derived adjoint
linear transition. -/
theorem AdjointBundle.fiberModelEquiv_eq_coordinateChange
    (chart : PrincipalBundleLocalTrivialization torsor)
    {b : B} (hb : b ∈ chart.baseSet)
    (z : AdjointBundle.Fiber (I := I) (torsor := torsor) b) :
    AdjointBundle.fiberModelEquiv (I := I) bundle chart hb z =
      AdjointBundle.fiberCoordinateChangeLinearEquiv (I := I) bundle chart b
        (AdjointBundle.selectedFiberModelEquiv (I := I) bundle b z) := by
  let selected := bundle.trivializationAt b
  let selectedCoordinate :=
    AdjointBundle.selectedFiberModelEquiv (I := I) bundle b z
  have overlap : (b, selectedCoordinate) ∈
      (adjointBundleOverlapDomain (I := I) selected chart : Set (B × E)) := by
    rw [adjointBundleOverlapDomain_eq (I := I) selected chart]
    exact ⟨⟨bundle.mem_baseSet_trivializationAt b, hb⟩, Set.mem_univ _⟩
  have transition := adjointBundleModelTransition_eq (I := I) bundle selected chart
    (b, selectedCoordinate) overlap
  have selectedInverse :
      (AdjointBundle.modelBundleTrivialization (I := I) bundle selected).toOpenPartialHomeomorph.symm
        (b, selectedCoordinate) = z.1 := by
    have roundTrip :=
      (AdjointBundle.selectedFiberModelEquiv (I := I) bundle b).symm_apply_apply z
    exact congrArg Subtype.val roundTrip
  have fiberTransition := congrArg Prod.snd transition
  rw [selectedInverse] at fiberTransition
  exact fiberTransition

/-- Every designated chart coordinate, not only the selected one, is a real linear equivalence for
the named transported structure on the dependent fiber. -/
def AdjointBundle.fiberModelLinearEquiv
    (chart : PrincipalBundleLocalTrivialization torsor)
    {b : B} (_hb : b ∈ chart.baseSet) :
    letI : AddCommGroup (AdjointBundle.Fiber (I := I) (torsor := torsor) b) :=
      AdjointBundle.fiberAddCommGroup (I := I) bundle b
    letI : Module ℝ (AdjointBundle.Fiber (I := I) (torsor := torsor) b) :=
      AdjointBundle.fiberModule (I := I) bundle b
    AdjointBundle.Fiber (I := I) (torsor := torsor) b ≃ₗ[ℝ] E := by
  letI : AddCommGroup (AdjointBundle.Fiber (I := I) (torsor := torsor) b) :=
    AdjointBundle.fiberAddCommGroup (I := I) bundle b
  letI : Module ℝ (AdjointBundle.Fiber (I := I) (torsor := torsor) b) :=
    AdjointBundle.fiberModule (I := I) bundle b
  exact (AdjointBundle.selectedFiberLinearEquiv (I := I) bundle b).trans
    (AdjointBundle.fiberCoordinateChangeLinearEquiv (I := I) bundle chart b)

/-- The underlying map of the packaged linear equivalence is the original quotient-derived chart
coordinate, rather than a replacement map. -/
@[simp]
theorem AdjointBundle.fiberModelLinearEquiv_apply
    (chart : PrincipalBundleLocalTrivialization torsor)
    {b : B} (hb : b ∈ chart.baseSet)
    (z : AdjointBundle.Fiber (I := I) (torsor := torsor) b) :
    letI : AddCommGroup (AdjointBundle.Fiber (I := I) (torsor := torsor) b) :=
      AdjointBundle.fiberAddCommGroup (I := I) bundle b
    letI : Module ℝ (AdjointBundle.Fiber (I := I) (torsor := torsor) b) :=
      AdjointBundle.fiberModule (I := I) bundle b
    AdjointBundle.fiberModelLinearEquiv (I := I) bundle chart hb z =
      AdjointBundle.fiberModelEquiv (I := I) bundle chart hb z := by
  letI : AddCommGroup (AdjointBundle.Fiber (I := I) (torsor := torsor) b) :=
    AdjointBundle.fiberAddCommGroup (I := I) bundle b
  letI : Module ℝ (AdjointBundle.Fiber (I := I) (torsor := torsor) b) :=
    AdjointBundle.fiberModule (I := I) bundle b
  symm
  exact AdjointBundle.fiberModelEquiv_eq_coordinateChange
    (I := I) bundle chart hb z

end

end YangMills.Geometry
