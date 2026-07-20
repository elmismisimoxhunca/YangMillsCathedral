/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Mathematics.OneFormCartanFieldExtension
import YangMills.Mathematics.SmoothManifoldOneFormExtChartRegularity

/-!
# Arbitrary-field extended-chart transport of the one-form Cartan expression

For arbitrary tangent fields smooth on a set `s`, the intrinsic Cartan expression at `p ∈ s`
equals the normed coordinate expression in the extended chart centered at `p`. The coordinate
fields use `mpullbackWithin` on `Set.range I`, and the coordinate calculus set is retained exactly as
`chart.symm ⁻¹' s ∩ Set.range I`; no unrestricted inverse-chart derivative is substituted.

This is transport of the Cartan expression, not construction of an exterior derivative.
-/

namespace YangMills.Mathematics

open Set Function Filter
open scoped Manifold ContDiff Topology

universe uE uH uM uV uW

variable
    {E : Type uE} {H : Type uH}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
    {M : Type uM} [TopologicalSpace M]
    {V : Type uV} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]
    [IsTopologicalAddGroup V] [ContinuousSMul ℝ V]
    {W : Type uW} [NormedAddCommGroup W] [NormedSpace ℝ W]
    {I : ModelWithCorners ℝ E H} [ChartedSpace H M] [IsManifold I ∞ M]

noncomputable section

/-- Arbitrary smooth tangent fields transport the intrinsic one-form Cartan expression at a
point to the exact centered extended-chart coordinate expression. The coordinate fields and the
calculus set retain Mathlib's corner-aware `mpullbackWithin`/`range I` convention. -/
theorem SmoothManifoldDifferentialForm.oneFormCartanExpressionCoordinates_inExtChartAt_arbitraryFields
    (coordinates : V ≃L[ℝ] W)
    (form : SmoothManifoldDifferentialForm I M V coordinates 1)
    (s : Set M) (p : M) (hp : p ∈ s)
    (first second : (y : M) → TangentSpace I y)
    (first_smooth : ManifoldTangentField.IsSmoothOn I s first)
    (second_smooth : ManifoldTangentField.IsSmoothOn I s second) :
    form.toForm.oneFormCartanExpressionCoordinates coordinates s p first second =
      (form.toForm.inExtChartAt coordinates 1 p).toManifoldForm.oneFormCartanExpressionCoordinates
        (I := modelWithCornersSelf ℝ E) (ContinuousLinearEquiv.refl ℝ W)
        ((extChartAt I p).symm ⁻¹' s ∩ Set.range ⇑I) ((extChartAt I p) p)
        (extChartCoordinateField I p first) (extChartCoordinateField I p second) := by
  let chart : PartialEquiv M E := extChartAt I p
  let source : Set E := chart.symm ⁻¹' s ∩ Set.range ⇑I
  let first' : E → E := extChartCoordinateField I p first
  let second' : E → E := extChartCoordinateField I p second
  have first_center : first' (chart p) = first p := by
    change (mfderivWithin (modelWithCornersSelf ℝ E) I (extChartAt I p).symm
      (Set.range ⇑I) ((extChartAt I p) p)).inverse
        (first ((extChartAt I p).symm ((extChartAt I p) p))) = first p
    rw [extChartAt_to_inv]
    exact mfderivWithin_extChartAt_symm_inverse_apply (I := I) (x := p) (first p)
  have second_center : second' (chart p) = second p := by
    change (mfderivWithin (modelWithCornersSelf ℝ E) I (extChartAt I p).symm
      (Set.range ⇑I) ((extChartAt I p) p)).inverse
        (second ((extChartAt I p).symm ((extChartAt I p) p))) = second p
    rw [extChartAt_to_inv]
    exact mfderivWithin_extChartAt_symm_inverse_apply (I := I) (x := p) (second p)
  have eval_coord (field : (y : M) → TangentSpace I y)
      (y : E) (hy : y ∈ chart.target) :
      (form.toForm.inExtChartAt coordinates 1 p y)
          (fun _ => extChartCoordinateField I p field y) =
        coordinates (form.toForm (chart.symm y) (fun _ => field (chart.symm y))) := by
    simp only [ManifoldDifferentialForm.inExtChartAt_apply, extChartCoordinateField,
      VectorField.mpullbackWithin_apply]
    congr 3
    funext i
    exact (isInvertible_mfderivWithin_extChartAt_symm (I := I) hy).self_apply_inverse _
  have eval_first_eventually :
      (fun y => (form.toForm.inExtChartAt coordinates 1 p y) (fun _ => first' y)) =ᶠ[𝓝[source] chart p]
        (fun y => coordinates (form.toForm (chart.symm y) (fun _ => first (chart.symm y)))) := by
    apply Filter.Eventually.filter_mono (nhdsWithin_mono _ inter_subset_right)
    filter_upwards [extChartAt_target_mem_nhdsWithin p] with y hy
    simpa [first', chart] using eval_coord first y (by simpa [chart] using hy)
  have eval_second_eventually :
      (fun y => (form.toForm.inExtChartAt coordinates 1 p y) (fun _ => second' y)) =ᶠ[𝓝[source] chart p]
        (fun y => coordinates (form.toForm (chart.symm y) (fun _ => second (chart.symm y)))) := by
    apply Filter.Eventually.filter_mono (nhdsWithin_mono _ inter_subset_right)
    filter_upwards [extChartAt_target_mem_nhdsWithin p] with y hy
    simpa [second', chart] using eval_coord second y (by simpa [chart] using hy)
  have first_eval_mdiff : MDifferentiableWithinAt I (modelWithCornersSelf ℝ W)
      (fun y => coordinates (form.toForm y (fun _ => first y))) s p := by
    exact ((form.eval_smooth s (fun _ => first) (fun _ => first_smooth)) p hp).mdifferentiableWithinAt (by simp)
  have second_eval_mdiff : MDifferentiableWithinAt I (modelWithCornersSelf ℝ W)
      (fun y => coordinates (form.toForm y (fun _ => second y))) s p := by
    exact ((form.eval_smooth s (fun _ => second) (fun _ => second_smooth)) p hp).mdifferentiableWithinAt (by simp)
  have first_derivative :
      (NormedSpace.fromTangentSpace (coordinates (form.toForm p (fun _ => first p))))
        (mfderivWithin I (modelWithCornersSelf ℝ W)
          (fun y => coordinates (form.toForm y (fun _ => first y))) s p (second p)) =
      fderivWithin ℝ
        (fun y => (form.toForm.inExtChartAt coordinates 1 p y) (fun _ => first' y))
        source (chart p) (second' (chart p)) := by
    have center_mem : chart p ∈ source := by
      exact ⟨by simpa [chart] using hp, by simp [chart]⟩
    rw [eval_first_eventually.fderivWithin_eq_of_mem center_mem]
    rw [second_center]
    simp only [mfderivWithin, first_eval_mdiff, if_pos]
    change (fderivWithin ℝ
      (fun y => coordinates (form.toForm ((extChartAt I p).symm y)
        (fun _ => first ((extChartAt I p).symm y))))
      ((extChartAt I p).symm ⁻¹' s ∩ Set.range ⇑I) ((extChartAt I p) p)) (second p) = _
    rfl
  have second_derivative :
      (NormedSpace.fromTangentSpace (coordinates (form.toForm p (fun _ => second p))))
        (mfderivWithin I (modelWithCornersSelf ℝ W)
          (fun y => coordinates (form.toForm y (fun _ => second y))) s p (first p)) =
      fderivWithin ℝ
        (fun y => (form.toForm.inExtChartAt coordinates 1 p y) (fun _ => second' y))
        source (chart p) (first' (chart p)) := by
    have center_mem : chart p ∈ source := by
      exact ⟨by simpa [chart] using hp, by simp [chart]⟩
    rw [eval_second_eventually.fderivWithin_eq_of_mem center_mem]
    rw [first_center]
    simp only [mfderivWithin, second_eval_mdiff, if_pos]
    change (fderivWithin ℝ
      (fun y => coordinates (form.toForm ((extChartAt I p).symm y)
        (fun _ => second ((extChartAt I p).symm y))))
      ((extChartAt I p).symm ⁻¹' s ∩ Set.range ⇑I) ((extChartAt I p) p)) (first p) = _
    rfl
  have bracket_eq :
      VectorField.mlieBracketWithin I first second s p =
        VectorField.lieBracketWithin ℝ first' second' source (chart p) := by
    rw [VectorField.mlieBracketWithin_apply]
    rw [(isInvertible_mfderiv_extChartAt (I := I) (mem_extChartAt_source p)).inverse_apply_eq]
    rw [mfderiv_extChartAt_self]
    rfl
  have form_center (v : E) :
      (form.toForm.inExtChartAt coordinates 1 p (chart p)) (fun _ => v) =
        coordinates (form.toForm p (fun _ => v)) := by
    rw [ManifoldDifferentialForm.inExtChartAt_center,
      mfderivWithin_range_extChartAt_symm]
    congr 3
  rw [ManifoldDifferentialForm.oneFormCartanExpressionCoordinates_normedSpace]
  unfold ManifoldDifferentialForm.oneFormCartanExpressionCoordinates
  change _ =
    fderivWithin ℝ (fun y => (form.toForm.inExtChartAt coordinates 1 p y)
      (fun _ => second' y)) source (chart p) (first' (chart p)) -
    fderivWithin ℝ (fun y => (form.toForm.inExtChartAt coordinates 1 p y)
      (fun _ => first' y)) source (chart p) (second' (chart p)) -
    (form.toForm.inExtChartAt coordinates 1 p (chart p))
      (fun _ => VectorField.lieBracketWithin ℝ first' second' source (chart p))
  rw [second_derivative, first_derivative, bracket_eq,
    form_center (VectorField.lieBracketWithin ℝ first' second' source (chart p))]

/-- If the centered coordinate one-form is differentiable as an alternating-map-valued function,
the intrinsic Cartan expression is independent of all admissible smooth field extensions with the
same two values at the point. -/
theorem SmoothManifoldDifferentialForm.oneFormCartanExpressionCoordinates_congr_at_of_inExtChartAt
    [CompleteSpace E]
    (coordinates : V ≃L[ℝ] W)
    (form : SmoothManifoldDifferentialForm I M V coordinates 1)
    (s : Set M) (p : M) (hp : p ∈ s) (unique_s : UniqueMDiffOn I s)
    (first second first' second' : (y : M) → TangentSpace I y)
    (first_smooth : ManifoldTangentField.IsSmoothOn I s first)
    (second_smooth : ManifoldTangentField.IsSmoothOn I s second)
    (first'_smooth : ManifoldTangentField.IsSmoothOn I s first')
    (second'_smooth : ManifoldTangentField.IsSmoothOn I s second')
    (hfirst : first p = first' p) (hsecond : second p = second' p)
    (form_differentiable : DifferentiableWithinAt ℝ
      (form.toForm.inExtChartAt coordinates 1 p)
      ((extChartAt I p).symm ⁻¹' s ∩ Set.range ⇑I) ((extChartAt I p) p)) :
    form.toForm.oneFormCartanExpressionCoordinates coordinates s p first second =
      form.toForm.oneFormCartanExpressionCoordinates coordinates s p first' second' := by
  rw [SmoothManifoldDifferentialForm.oneFormCartanExpressionCoordinates_inExtChartAt_arbitraryFields
      coordinates form s p hp first second first_smooth second_smooth,
    SmoothManifoldDifferentialForm.oneFormCartanExpressionCoordinates_inExtChartAt_arbitraryFields
      coordinates form s p hp first' second' first'_smooth second'_smooth]
  exact inExtChart_oneFormCartanExpressionCoordinates_eq_of_eq_at
    I coordinates form s p hp unique_s first second first' second'
    first_smooth second_smooth first'_smooth second'_smooth hfirst hsecond form_differentiable

/-- On a finite-dimensional manifold model, evaluation-based smoothness derives the required
centered coordinate regularity, so the intrinsic Cartan expression is unconditionally independent
of all admissible smooth field extensions with the same values at the point. -/
theorem SmoothManifoldDifferentialForm.oneFormCartanExpressionCoordinates_congr_at
    [FiniteDimensional ℝ E]
    (coordinates : V ≃L[ℝ] W)
    (form : SmoothManifoldDifferentialForm I M V coordinates 1)
    (s : Set M) (p : M) (hp : p ∈ s) (unique_s : UniqueMDiffOn I s)
    (first second first' second' : (y : M) → TangentSpace I y)
    (first_smooth : ManifoldTangentField.IsSmoothOn I s first)
    (second_smooth : ManifoldTangentField.IsSmoothOn I s second)
    (first'_smooth : ManifoldTangentField.IsSmoothOn I s first')
    (second'_smooth : ManifoldTangentField.IsSmoothOn I s second')
    (hfirst : first p = first' p) (hsecond : second p = second' p) :
    form.toForm.oneFormCartanExpressionCoordinates coordinates s p first second =
      form.toForm.oneFormCartanExpressionCoordinates coordinates s p first' second' := by
  letI : CompleteSpace E := FiniteDimensional.complete ℝ E
  apply SmoothManifoldDifferentialForm.oneFormCartanExpressionCoordinates_congr_at_of_inExtChartAt
    coordinates form s p hp unique_s first second first' second'
    first_smooth second_smooth first'_smooth second'_smooth hfirst hsecond
  exact (SmoothManifoldDifferentialForm.inExtChartAt_differentiableWithinAt_range
    coordinates form p).mono inter_subset_right

end
end YangMills.Mathematics
