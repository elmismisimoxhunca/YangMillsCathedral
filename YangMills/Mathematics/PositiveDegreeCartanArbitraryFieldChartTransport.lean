/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Mathematics.OneFormCartanArbitraryFieldChartTransport
import YangMills.Mathematics.SmoothManifoldDifferentialFormExtChartRegularity
import YangMills.Mathematics.ManifoldPositiveDegreeExteriorDerivative

/-!
# Positive-degree Cartan transport for arbitrary fields

This module transports the full triangular positive-degree Cartan expression through a centered
inverse extended chart for arbitrary local smooth fields. It derives field-extension independence
without an exterior certificate and retains the exact corner-aware coordinate calculus set. It also
proves locality under equality of set germs.
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

/-- Arbitrary smooth tangent fields transport the intrinsic positive-degree Cartan expression at
`p` to the exact centered extended-chart coordinate expression. -/
theorem SmoothManifoldDifferentialForm.positiveDegreeCartanExpressionCoordinates_inExtChartAt_arbitraryFields
    (coordinates : V ≃L[ℝ] W) (n : ℕ)
    (form : SmoothManifoldDifferentialForm I M V coordinates (n + 1))
    (s : Set M) (p : M) (hp : p ∈ s)
    (fields : Fin (n + 2) → (y : M) → TangentSpace I y)
    (fields_smooth : ∀ i, ManifoldTangentField.IsSmoothOn I s (fields i)) :
    form.toForm.positiveDegreeCartanExpressionCoordinates coordinates n s p fields =
      ManifoldDifferentialForm.positiveDegreeCartanExpressionCoordinates
        (I := modelWithCornersSelf ℝ E) (ContinuousLinearEquiv.refl ℝ W) n
        (form.toForm.inExtChartAt coordinates (n + 1) p).toManifoldForm
        ((extChartAt I p).symm ⁻¹' s ∩ Set.range ⇑I) ((extChartAt I p) p)
        (fun i => extChartCoordinateField I p (fields i)) := by
  let chart : PartialEquiv M E := extChartAt I p
  let source : Set E := chart.symm ⁻¹' s ∩ Set.range ⇑I
  let fields' : Fin (n + 2) → E → E := fun i => extChartCoordinateField I p (fields i)
  have fields_center (i : Fin (n + 2)) : fields' i (chart p) = fields i p := by
    change (mfderivWithin (modelWithCornersSelf ℝ E) I (extChartAt I p).symm
      (Set.range ⇑I) ((extChartAt I p) p)).inverse
        (fields i ((extChartAt I p).symm ((extChartAt I p) p))) = fields i p
    rw [extChartAt_to_inv]
    exact mfderivWithin_extChartAt_symm_inverse_apply (I := I) (x := p) (fields i p)
  have eval_coord (tuple : Fin (n + 1) → ((y : M) → TangentSpace I y))
      (y : E) (hy : y ∈ chart.target) :
      (form.toForm.inExtChartAt coordinates (n + 1) p y)
          (fun i => extChartCoordinateField I p (tuple i) y) =
        coordinates (form.toForm (chart.symm y) (fun i => tuple i (chart.symm y))) := by
    simp only [ManifoldDifferentialForm.inExtChartAt_apply, extChartCoordinateField,
      VectorField.mpullbackWithin_apply]
    congr 3
    funext i
    exact (isInvertible_mfderivWithin_extChartAt_symm (I := I) hy).self_apply_inverse _
  have derivative_eq (i : Fin (n + 2)) :
      (NormedSpace.fromTangentSpace
        (coordinates (form.toForm p (i.removeNth (fun k => fields k p)))))
        (mfderivWithin I (modelWithCornersSelf ℝ W)
          (fun y => coordinates (form.toForm y (i.removeNth (fun k => fields k y))))
          s p (fields i p)) =
      fderivWithin ℝ
        (fun y => (form.toForm.inExtChartAt coordinates (n + 1) p y)
          (i.removeNth (fun k => fields' k y)))
        source (chart p) (fields' i (chart p)) := by
    let tuple : Fin (n + 1) → ((y : M) → TangentSpace I y) := i.removeNth fields
    have eval_eventually :
        (fun y => (form.toForm.inExtChartAt coordinates (n + 1) p y)
          (i.removeNth (fun k => fields' k y))) =ᶠ[𝓝[source] chart p]
        (fun y => coordinates
          (form.toForm (chart.symm y) (i.removeNth (fun k => fields k (chart.symm y))))) := by
      apply Filter.Eventually.filter_mono (nhdsWithin_mono _ inter_subset_right)
      filter_upwards [extChartAt_target_mem_nhdsWithin p] with y hy
      have htuple : i.removeNth (fun k => fields' k y) =
          fun a => extChartCoordinateField I p (tuple a) y := by
        funext a
        simp only [tuple, fields', Fin.removeNth_apply]
      rw [htuple]
      convert eval_coord tuple y (by simpa [chart] using hy) using 1
      congr 3
    have eval_mdiff : MDifferentiableWithinAt I (modelWithCornersSelf ℝ W)
        (fun y => coordinates
          (form.toForm y (i.removeNth (fun k => fields k y)))) s p := by
      exact ((form.eval_smooth s (i.removeNth fields)
        (fun a => fields_smooth (i.succAbove a))) p hp).mdifferentiableWithinAt (by simp)
    have center_mem : chart p ∈ source := by
      exact ⟨by simpa [chart] using hp, by simp [chart]⟩
    rw [eval_eventually.fderivWithin_eq_of_mem center_mem]
    rw [fields_center]
    simp only [mfderivWithin, eval_mdiff, if_pos]
    change (fderivWithin ℝ
      (fun y => coordinates (form.toForm ((extChartAt I p).symm y)
        (i.removeNth (fun k => fields k ((extChartAt I p).symm y)))))
      ((extChartAt I p).symm ⁻¹' s ∩ Set.range ⇑I) ((extChartAt I p) p))
      (fields i p) = _
    rfl
  have bracket_eq (i : Fin (n + 1)) (j : Fin (n + 2)) :
      VectorField.mlieBracketWithin I (fields i.castSucc) (fields j) s p =
        VectorField.lieBracketWithin ℝ (fields' i.castSucc) (fields' j)
          source (chart p) := by
    rw [VectorField.mlieBracketWithin_apply]
    rw [(isInvertible_mfderiv_extChartAt (I := I)
      (mem_extChartAt_source p)).inverse_apply_eq]
    rw [mfderiv_extChartAt_self]
    rfl
  have form_center (tuple : Fin (n + 1) → E) :
      (form.toForm.inExtChartAt coordinates (n + 1) p (chart p)) tuple =
        coordinates (form.toForm p tuple) := by
    rw [ManifoldDifferentialForm.inExtChartAt_center,
      mfderivWithin_range_extChartAt_symm]
    congr 3
  rw [ManifoldDifferentialForm.positiveDegreeCartanExpressionCoordinates_normedSpace]
  unfold ManifoldDifferentialForm.positiveDegreeCartanExpressionCoordinates
  congr 1
  · apply Finset.sum_congr rfl
    intro i hi
    congr 1
    exact derivative_eq i
  · apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    congr 1
    rw [← form_center]
    congr 2
    · exact bracket_eq i j.succ
    · funext a
      simp only [Fin.removeNth_apply]
      exact (fields_center (i.castSucc.succAbove (j.succAbove a))).symm

/-- The normed-space positive-degree Cartan expression only depends on the field values at the
base point. -/
theorem NormedSpaceDifferentialForm.positiveDegreeCartanExpressionCoordinates_congr_at
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    (n : ℕ) (form : NormedSpaceDifferentialForm E W (n + 1)) (s : Set E) (x : E)
    (fields fields' : Fin (n + 2) → E → E)
    (form_differentiable : DifferentiableWithinAt ℝ form s x)
    (fields_differentiable : ∀ i, DifferentiableWithinAt ℝ (fields i) s x)
    (fields'_differentiable : ∀ i, DifferentiableWithinAt ℝ (fields' i) s x)
    (unique : UniqueDiffWithinAt ℝ s x)
    (hfields : ∀ i, fields i x = fields' i x) :
    form.toManifoldForm.positiveDegreeCartanExpressionCoordinates
        (I := modelWithCornersSelf ℝ E) (ContinuousLinearEquiv.refl ℝ W)
        n s x fields =
      form.toManifoldForm.positiveDegreeCartanExpressionCoordinates
        (I := modelWithCornersSelf ℝ E) (ContinuousLinearEquiv.refl ℝ W)
        n s x fields' := by
  rw [← form.extDerivWithin_eq_positiveDegreeCartanExpression n s x fields
      form_differentiable fields_differentiable unique,
    ← form.extDerivWithin_eq_positiveDegreeCartanExpression n s x fields'
      form_differentiable fields'_differentiable unique]
  congr 1
  funext i
  exact hfields i

/-- Centered coordinate differentiability implies intrinsic field-extension independence,
without using an exterior-derivative certificate. -/
theorem SmoothManifoldDifferentialForm.positiveDegreeCartanExpressionCoordinates_congr_at_of_inExtChartAt
    [CompleteSpace E]
    (coordinates : V ≃L[ℝ] W) (n : ℕ)
    (form : SmoothManifoldDifferentialForm I M V coordinates (n + 1))
    (s : Set M) (p : M) (hp : p ∈ s) (unique_s : UniqueMDiffOn I s)
    (fields fields' : Fin (n + 2) → (y : M) → TangentSpace I y)
    (fields_smooth : ∀ i, ManifoldTangentField.IsSmoothOn I s (fields i))
    (fields'_smooth : ∀ i, ManifoldTangentField.IsSmoothOn I s (fields' i))
    (hfields : ∀ i, fields i p = fields' i p)
    (form_differentiable : DifferentiableWithinAt ℝ
      (form.toForm.inExtChartAt coordinates (n + 1) p)
      ((extChartAt I p).symm ⁻¹' s ∩ Set.range ⇑I) ((extChartAt I p) p)) :
    form.toForm.positiveDegreeCartanExpressionCoordinates coordinates n s p fields =
      form.toForm.positiveDegreeCartanExpressionCoordinates coordinates n s p fields' := by
  rw [form.positiveDegreeCartanExpressionCoordinates_inExtChartAt_arbitraryFields
      coordinates n s p hp fields fields_smooth,
    form.positiveDegreeCartanExpressionCoordinates_inExtChartAt_arbitraryFields
      coordinates n s p hp fields' fields'_smooth]
  apply NormedSpaceDifferentialForm.positiveDegreeCartanExpressionCoordinates_congr_at
    (form_differentiable := form_differentiable)
    (fields_differentiable := fun i =>
      extChartCoordinateField_differentiableWithinAt I s p hp (fields i) (fields_smooth i))
    (fields'_differentiable := fun i =>
      extChartCoordinateField_differentiableWithinAt I s p hp (fields' i) (fields'_smooth i))
  · rw [inter_comm]
    apply unique_s.uniqueDiffWithinAt_range_inter p
    exact ⟨mem_extChartAt_target p, by simpa using hp⟩
  · intro i
    exact extChartCoordinateField_eq_at_center I p (fields i) (fields' i) (hfields i)

/-- In a finite-dimensional manifold model, arbitrary-degree centered-coordinate regularity
discharges the differentiability hypothesis, so the intrinsic Cartan expression only depends on
the admissible smooth field values at the base point. -/
theorem SmoothManifoldDifferentialForm.positiveDegreeCartanExpressionCoordinates_congr_at
    [FiniteDimensional ℝ E]
    (coordinates : V ≃L[ℝ] W) (n : ℕ)
    (form : SmoothManifoldDifferentialForm I M V coordinates (n + 1))
    (s : Set M) (p : M) (hp : p ∈ s) (unique_s : UniqueMDiffOn I s)
    (fields fields' : Fin (n + 2) → (y : M) → TangentSpace I y)
    (fields_smooth : ∀ i, ManifoldTangentField.IsSmoothOn I s (fields i))
    (fields'_smooth : ∀ i, ManifoldTangentField.IsSmoothOn I s (fields' i))
    (hfields : ∀ i, fields i p = fields' i p) :
    form.toForm.positiveDegreeCartanExpressionCoordinates coordinates n s p fields =
      form.toForm.positiveDegreeCartanExpressionCoordinates coordinates n s p fields' := by
  letI : CompleteSpace E := FiniteDimensional.complete ℝ E
  apply form.positiveDegreeCartanExpressionCoordinates_congr_at_of_inExtChartAt
    coordinates n s p hp unique_s fields fields' fields_smooth fields'_smooth hfields
  exact (form.inExtChartAt_differentiableWithinAt_modelRange coordinates (n + 1) p).mono
    inter_subset_right

omit [IsManifold I ∞ M] in
/-- The intrinsic positive-degree Cartan expression is local in its calculus set. -/
theorem ManifoldDifferentialForm.positiveDegreeCartanExpressionCoordinates_congr_set
    (coordinates : V ≃L[ℝ] W) (n : ℕ)
    (form : ManifoldDifferentialForm I M V (n + 1))
    (s t : Set M) (p : M)
    (fields : Fin (n + 2) → (y : M) → TangentSpace I y)
    (hst : s =ᶠ[𝓝 p] t) :
    form.positiveDegreeCartanExpressionCoordinates coordinates n s p fields =
      form.positiveDegreeCartanExpressionCoordinates coordinates n t p fields := by
  unfold ManifoldDifferentialForm.positiveDegreeCartanExpressionCoordinates
  congr 1
  · apply Finset.sum_congr rfl
    intro i hi
    congr 1
    rw [mfderivWithin_congr_set hst]
  · apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    congr 2
    rw [VectorField.mlieBracketWithin_congr_set hst]

end
end YangMills.Mathematics
