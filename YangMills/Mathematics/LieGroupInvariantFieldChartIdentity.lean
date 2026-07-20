/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Mathematics.LieGroupChartMultiplication

/-!
# Identity-point chart coordinates of invariant Lie-group fields

The two selected partial derivatives of identity-centered chart multiplication are normalized on the
exact product corner range. Schwarz cancellation then gives a zero within-range bracket for those
partial fields. At the chart center, Mathlib's pullback coordinates of the left-invariant field and
the project's right-invariant field agree with the corresponding partials. These are pointwise
identifications only; neighborhood field equality and intrinsic invariant-field commutation remain
open.
-/

namespace YangMills.Mathematics

open Function Bundle Set ChartedSpace
open scoped Manifold ContDiff

universe uE uH uG
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {E : Type uE} {H : Type uH}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H)
    {G : Type uG} [Group G] [TopologicalSpace G]
    [ChartedSpace H G] [LieGroup I ∞ G]

theorem centeredChartMul_second_normalization
    (X : E) :
    let c := extChartAt I (1 : G)
    let a := c (1 : G)
    let F := fun z : E × E => c (c.symm z.1 * c.symm z.2)
    fderivWithin ℝ F (range I ×ˢ range I) (a, a) (0, X) = X := by
  dsimp
  let c := extChartAt I (1 : G)
  let a := c (1 : G)
  let F := fun z : E × E => c (c.symm z.1 * c.symm z.2)
  let S := range I ×ˢ range I
  have ha : a ∈ range I := extChartAt_target_subset_range (1 : G) (mem_extChartAt_target 1)
  have hF : DifferentiableWithinAt ℝ F S (a, a) :=
    (contDiffWithinAt_extChartAt_mul_identity I).differentiableWithinAt (by norm_num)
  have hq : HasFDerivWithinAt (fun y : E => (a, y))
      (ContinuousLinearMap.inr ℝ E E) (range I) a :=
    (by fun_prop : HasFDerivAt (fun y : E => (a, y))
      (ContinuousLinearMap.inr ℝ E E) a).hasFDerivWithinAt
  have hmaps : MapsTo (fun y : E => (a, y)) (range I) S := fun _ hy => ⟨ha, hy⟩
  have hcomp := hF.hasFDerivWithinAt.comp a hq hmaps
  have huniq : UniqueDiffWithinAt ℝ (range I) a := I.uniqueDiffOn a ha
  have heq := hcomp.fderivWithin huniq
  have hround : (fun y : E => F (a, y)) = fun y => c (c.symm y) := by
    funext y
    simp [F, a, c]
  have hroundDeriv :
      fderivWithin ℝ (fun y : E => F (a, y)) (range I) a =
        ContinuousLinearMap.id ℝ E := by
    rw [hround]
    exact fderivWithin_extChartAt_comp_extChartAt_symm_range
  have happ := congrArg (fun L : E →L[ℝ] E => L X) heq
  change (fderivWithin ℝ (fun y : E => F (a, y)) (range I) a) X = _ at happ
  rw [hroundDeriv] at happ
  change fderivWithin ℝ F S (a, a) (0, X) = X
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply,
    ContinuousLinearMap.id_apply] using happ.symm

theorem centeredChartMul_first_normalization
    (Y : E) :
    let c := extChartAt I (1 : G)
    let a := c (1 : G)
    let F := fun z : E × E => c (c.symm z.1 * c.symm z.2)
    fderivWithin ℝ F (range I ×ˢ range I) (a, a) (Y, 0) = Y := by
  dsimp
  let c := extChartAt I (1 : G)
  let a := c (1 : G)
  let F := fun z : E × E => c (c.symm z.1 * c.symm z.2)
  let S := range I ×ˢ range I
  have ha : a ∈ range I := extChartAt_target_subset_range (1 : G) (mem_extChartAt_target 1)
  have hF : DifferentiableWithinAt ℝ F S (a, a) :=
    (contDiffWithinAt_extChartAt_mul_identity I).differentiableWithinAt (by norm_num)
  have hq : HasFDerivWithinAt (fun y : E => (y, a))
      (ContinuousLinearMap.inl ℝ E E) (range I) a :=
    (by fun_prop : HasFDerivAt (fun y : E => (y, a))
      (ContinuousLinearMap.inl ℝ E E) a).hasFDerivWithinAt
  have hmaps : MapsTo (fun y : E => (y, a)) (range I) S := fun _ hy => ⟨hy, ha⟩
  have hcomp := hF.hasFDerivWithinAt.comp (f := fun y : E => (y, a)) a hq hmaps
  have huniq : UniqueDiffWithinAt ℝ (range I) a := I.uniqueDiffOn a ha
  have heq := hcomp.fderivWithin huniq
  have hround : (fun y : E => F (y, a)) = fun y => c (c.symm y) := by
    funext y
    simp [F, a, c]
  have hroundDeriv :
      fderivWithin ℝ (fun y : E => F (y, a)) (range I) a =
        ContinuousLinearMap.id ℝ E := by
    rw [hround]
    exact fderivWithin_extChartAt_comp_extChartAt_symm_range
  have happ := congrArg (fun L : E →L[ℝ] E => L Y) heq
  change (fderivWithin ℝ (fun y : E => F (y, a)) (range I) a) Y = _ at happ
  rw [hroundDeriv] at happ
  change fderivWithin ℝ F S (a, a) (Y, 0) = Y
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply,
    ContinuousLinearMap.id_apply] using happ.symm

/-- At the identity chart center, the exact opposite partial fields of centered multiplication
have zero within-range bracket, with their first derivatives normalized canonically. -/
theorem centeredChartMul_partialFields_lieBracketWithin_identity
    (X Y : E) :
    let c := extChartAt I (1 : G)
    let a := c (1 : G)
    let F := fun z : E × E => c (c.symm z.1 * c.symm z.2)
    VectorField.lieBracketWithin ℝ
      (fun x => fderivWithin ℝ F (range I ×ˢ range I) (x, a) (0, X))
      (fun x => fderivWithin ℝ F (range I ×ˢ range I) (a, x) (Y, 0))
      (range I) a = 0 := by
  dsimp
  let c := extChartAt I (1 : G)
  let a := c (1 : G)
  let F := fun z : E × E => c (c.symm z.1 * c.symm z.2)
  have ha : a ∈ range I := extChartAt_target_subset_range (1 : G) (mem_extChartAt_target 1)
  have hrange : (a, a) ∈ range (I.prod I) := by
    rw [ModelWithCorners.range_prod]
    exact ⟨ha, ha⟩
  have haa : (a, a) ∈ closure (interior (range I ×ˢ range I)) := by
    rw [← ModelWithCorners.range_prod]
    exact (I.prod I).range_subset_closure_interior hrange
  exact lieBracketWithin_mixed_partial_eq_zero F (range I) a X Y I.uniqueDiffOn ha haa
    (contDiffWithinAt_extChartAt_mul_identity I)
    (centeredChartMul_second_normalization I X)
    (centeredChartMul_first_normalization I Y)

/-- The Mathlib `mpullbackWithin` coordinate of a left-invariant generator has the exact generator
value at the identity-centered chart point. -/
theorem extChartCoordinateField_mulInvariantVectorField_identity
    (X : GroupLieAlgebra I G) :
    extChartCoordinateField I (1 : G) (mulInvariantVectorField X)
        ((extChartAt I (1 : G)) 1) = groupLieAlgebraModelEquiv I X := by
  unfold extChartCoordinateField VectorField.mpullbackWithin
  rw [extChartAt_to_inv]
  calc
    (mfderivWithin (modelWithCornersSelf ℝ E) I (extChartAt I (1 : G)).symm
      (range I) ((extChartAt I (1 : G)) 1)).inverse (mulInvariantVectorField X 1) =
        mulInvariantVectorField X 1 :=
      mfderivWithin_extChartAt_symm_inverse_apply (v := mulInvariantVectorField X 1)
    _ = X := by
      unfold mulInvariantVectorField
      rw [show (fun h : G => (1 : G) * h) = id by funext h; simp, mfderiv_id]
      rfl
    _ = groupLieAlgebraModelEquiv I X := rfl

/-- The project right-invariant field has the same exact centered coordinate normalization. -/
theorem extChartCoordinateField_mulRightInvariantVectorField_identity
    (Y : GroupLieAlgebra I G) :
    extChartCoordinateField I (1 : G) (mulRightInvariantVectorField I Y)
        ((extChartAt I (1 : G)) 1) = groupLieAlgebraModelEquiv I Y := by
  unfold extChartCoordinateField VectorField.mpullbackWithin
  rw [extChartAt_to_inv]
  calc
    (mfderivWithin (modelWithCornersSelf ℝ E) I (extChartAt I (1 : G)).symm
      (range I) ((extChartAt I (1 : G)) 1)).inverse (mulRightInvariantVectorField I Y 1) =
        mulRightInvariantVectorField I Y 1 :=
      mfderivWithin_extChartAt_symm_inverse_apply (v := mulRightInvariantVectorField I Y 1)
    _ = Y := by
      unfold mulRightInvariantVectorField
      rw [show (fun h : G => h * (1 : G)) = id by funext h; simp, mfderiv_id]
      rfl
    _ = groupLieAlgebraModelEquiv I Y := rfl

/-- Exact identity-point identification of Mathlib's chart pullback of the left-invariant field
with the second partial of centered chart multiplication, retaining the product model range. -/
theorem extChartCoordinateField_mulInvariantVectorField_eq_secondPartial_identity
    (X : GroupLieAlgebra I G) :
    let c := extChartAt I (1 : G)
    let a := c (1 : G)
    let F := fun z : E × E => c (c.symm z.1 * c.symm z.2)
    extChartCoordinateField I (1 : G) (mulInvariantVectorField X) a =
      fderivWithin ℝ F (range I ×ˢ range I) (a, a)
        (0, groupLieAlgebraModelEquiv I X) := by
  exact (extChartCoordinateField_mulInvariantVectorField_identity I X).trans
    (centeredChartMul_second_normalization I (groupLieAlgebraModelEquiv I X)).symm

/-- Exact identity-point identification of the project right-invariant field's Mathlib chart
pullback with the first partial of centered chart multiplication. -/
theorem extChartCoordinateField_mulRightInvariantVectorField_eq_firstPartial_identity
    (Y : GroupLieAlgebra I G) :
    let c := extChartAt I (1 : G)
    let a := c (1 : G)
    let F := fun z : E × E => c (c.symm z.1 * c.symm z.2)
    extChartCoordinateField I (1 : G) (mulRightInvariantVectorField I Y) a =
      fderivWithin ℝ F (range I ×ˢ range I) (a, a)
        (groupLieAlgebraModelEquiv I Y, 0) := by
  exact (extChartCoordinateField_mulRightInvariantVectorField_identity I Y).trans
    (centeredChartMul_first_normalization I (groupLieAlgebraModelEquiv I Y)).symm

end
end YangMills.Mathematics
