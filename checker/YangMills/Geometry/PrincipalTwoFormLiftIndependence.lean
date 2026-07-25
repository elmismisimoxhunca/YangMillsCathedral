/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Geometry.PrincipalCurvatureStructure
import YangMills.Geometry.PrincipalBundleLocalTangentLift

/-!
# Lift independence of horizontal principal two-forms

Horizontality implies that a principal two-form depends only on the projected tangent vectors at a
fixed total-space point. Consequently, any tuple of tangent lifts agrees with the exact local lift
supplied by a designated principal chart.

This proves lift independence only. It does not identify different total-space representatives,
construct a descended form, or assert curvature descent.
-/

namespace YangMills.Geometry

open Set
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
    {IG : ModelWithCorners ℝ EG HG}
    {IB : ModelWithCorners ℝ EB HB}
    {IP : ModelWithCorners ℝ EP HP}
    [ChartedSpace HG G] [LieGroup IG ∞ G]
    [ChartedSpace HB B] [IsManifold IB ∞ B]
    [ChartedSpace HP P] [IsManifold IP ∞ P]
    {torsor : PrincipalBundleTorsorData G B P}
    {bundle : TopologicalPrincipalBundleData torsor}
    (smoothBundle : SmoothPrincipalBundleData IB IG IP torsor bundle)

namespace PrincipalTwoForm.IsHorizontal

/-- Replacing one argument by another with the same projection differential does not change a
horizontal two-form. The proof subtracts the arguments and applies horizontality to the resulting
vertical insertion. -/
theorem eq_update_of_verticalDifference
    (form : YangMills.Mathematics.ManifoldDifferentialForm IP P
      (GroupLieAlgebra IG G) 2)
    (horizontal : PrincipalTwoForm.IsHorizontal smoothBundle form)
    (p : P) (args : Fin 2 → TangentSpace IP p) (i : Fin 2)
    (replacement : TangentSpace IP p)
    (verticalDifference :
      mfderiv IP IB torsor.projection p (args i - replacement) = 0) :
    form p args = form p (Function.update args i replacement) := by
  have zeroInsertion :
      form p (Function.update args i (args i - replacement)) = 0 := by
    apply horizontal p _
    refine ⟨i, ?_⟩
    simpa using verticalDifference
  rw [(form p).map_update_sub] at zeroInsertion
  exact sub_eq_zero.mp (by simpa using zeroInsertion)

/-- At a fixed total-space point, a horizontal two-form takes the same value on any two tangent
lifts of the same ordered pair of base tangent vectors. -/
theorem eq_of_projection_eq
    (form : YangMills.Mathematics.ManifoldDifferentialForm IP P
      (GroupLieAlgebra IG G) 2)
    (horizontal : PrincipalTwoForm.IsHorizontal smoothBundle form)
    (p : P) (first second : Fin 2 → TangentSpace IP p)
    (sameProjection : ∀ i,
      mfderiv IP IB torsor.projection p (first i) =
        mfderiv IP IB torsor.projection p (second i)) :
    form p first = form p second := by
  let middle := Function.update first (0 : Fin 2) (second 0)
  have vertical0 :
      mfderiv IP IB torsor.projection p (first 0 - second 0) = 0 := by
    rw [map_sub, sameProjection 0, sub_self]
  have first_to_middle : form p first = form p middle :=
    eq_update_of_verticalDifference smoothBundle form horizontal p first 0 (second 0) vertical0
  have vertical1 :
      mfderiv IP IB torsor.projection p (middle 1 - second 1) = 0 := by
    rw [map_sub]
    change mfderiv IP IB torsor.projection p (first 1) -
      mfderiv IP IB torsor.projection p (second 1) = 0
    rw [sameProjection 1, sub_self]
  have middle_to_secondUpdate :
      form p middle = form p (Function.update middle (1 : Fin 2) (second 1)) :=
    eq_update_of_verticalDifference smoothBundle form horizontal p middle 1 (second 1) vertical1
  have updated_eq : Function.update middle (1 : Fin 2) (second 1) = second := by
    funext i
    fin_cases i <;> simp [middle]
  calc
    form p first = form p middle := first_to_middle
    _ = form p (Function.update middle (1 : Fin 2) (second 1)) := middle_to_secondUpdate
    _ = form p second := congrArg (form p) updated_eq

/-- Any lifts at the point of a designated local section give the same horizontal-form value as the
canonical derivative lifts from that section. -/
theorem eq_localTangentLift
    (form : YangMills.Mathematics.ManifoldDifferentialForm IP P
      (GroupLieAlgebra IG G) 2)
    (horizontal : PrincipalTwoForm.IsHorizontal smoothBundle form)
    (chart : PrincipalBundleLocalTrivialization torsor)
    (chart_mem : chart ∈ bundle.trivializationAtlas)
    {b : B} (hb : b ∈ chart.baseSet)
    (baseVectors : Fin 2 → TangentSpace IB b)
    (lifts : Fin 2 → TangentSpace IP (principalBundleLocalSection chart b))
    (lifts_project : ∀ i,
      mfderiv IP IB torsor.projection (principalBundleLocalSection chart b) (lifts i) =
        baseVectors i) :
    form (principalBundleLocalSection chart b) lifts =
      form (principalBundleLocalSection chart b)
        (fun i => principalBundleLocalTangentLift (IB := IB) (IP := IP) chart b
          (baseVectors i)) := by
  apply eq_of_projection_eq smoothBundle form horizontal
  intro i
  rw [lifts_project i]
  exact (principalBundleLocalTangentLift_rightInverse
    smoothBundle chart chart_mem hb) (baseVectors i) |>.symm

end PrincipalTwoForm.IsHorizontal

end

end YangMills.Geometry
