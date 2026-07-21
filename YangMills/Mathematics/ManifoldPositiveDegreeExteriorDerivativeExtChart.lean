/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Mathematics.SmoothManifoldDifferentialFormExtChartRegularity
import YangMills.Mathematics.ManifoldPositiveDegreeExteriorDerivative
import YangMills.Mathematics.ManifoldOneFormExtChartNaturality

/-!
# Positive-degree exterior derivative in a centered inverse extended chart

A smooth positive-degree Cartan certificate agrees at the chart center with Mathlib's
`extDerivWithin` on the exact chart target. Inverse-chart tangent transport remains
`mfderivWithin` on `Set.range I` through `ManifoldDifferentialForm.inExtChartAt`.
-/

namespace YangMills.Mathematics

open Set Function Filter
open scoped Manifold ContDiff Topology

universe uE uH uM uV uW

variable
    {E : Type uE} {H : Type uH}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace H]
    {M : Type uM} [TopologicalSpace M]
    {V : Type uV} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]
    [IsTopologicalAddGroup V] [ContinuousSMul ℝ V]
    {W : Type uW} [NormedAddCommGroup W] [NormedSpace ℝ W]
    {I : ModelWithCorners ℝ E H} [ChartedSpace H M] [IsManifold I ∞ M]

noncomputable section

omit [FiniteDimensional ℝ E] in
private lemma eval_mpullback_extChart_derivative_naturality_at_source
    (coordinates : V ≃L[ℝ] W) (k : ℕ)
    (form : ManifoldDifferentialForm I M V k)
    (p q : M) (hq : q ∈ (extChartAt I p).source)
    (tuple : Fin k → E) (v : E)
    (hcoord : DifferentiableWithinAt ℝ
      (form.inExtChartAt coordinates k p) (extChartAt I p).target ((extChartAt I p) q)) :
    (NormedSpace.fromTangentSpace
      (coordinates (form q (fun i =>
        VectorField.mpullback I (modelWithCornersSelf ℝ E)
          (extChartAt I p) (fun _ => tuple i) q))))
      (mfderivWithin I (modelWithCornersSelf ℝ W)
        (fun y => coordinates (form y (fun i =>
          VectorField.mpullback I (modelWithCornersSelf ℝ E)
            (extChartAt I p) (fun _ => tuple i) y)))
        (extChartAt I p).source q
        (VectorField.mpullback I (modelWithCornersSelf ℝ E)
          (extChartAt I p) (fun _ => v) q)) =
      fderivWithin ℝ
        (fun y => form.inExtChartAt coordinates k p y tuple)
        (extChartAt I p).target ((extChartAt I p) q) v := by
  let chart : PartialEquiv M E := extChartAt I p
  let fields : Fin k → (z : M) → TangentSpace I z := fun i =>
    VectorField.mpullback I (modelWithCornersSelf ℝ E) chart (fun _ => tuple i)
  let first : (z : M) → TangentSpace I z :=
    VectorField.mpullback I (modelWithCornersSelf ℝ E) chart (fun _ => v)
  let g : M → W := fun z => coordinates (form z (fun i => fields i z))
  let h : E → W := fun y => form.inExtChartAt coordinates k p y tuple
  have hq' : q ∈ chart.source := by simpa [chart] using hq
  have hinv (z : M) (hz : z ∈ chart.source) :
      (mfderiv I (modelWithCornersSelf ℝ E) chart z).inverse =
        mfderivWithin (modelWithCornersSelf ℝ E) I chart.symm (range ⇑I) (chart z) := by
    have ht : chart z ∈ chart.target := chart.map_source hz
    have hleft : chart.symm (chart z) = z := chart.left_inv hz
    have h1 := mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm
      (I := I) (x := p) ht
    have h2 := mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt
      (I := I) (x := p) ht
    rw [hleft] at h1 h2
    exact ContinuousLinearMap.inverse_eq h1 h2
  have eval_eq : ∀ z ∈ chart.source, g z = h (chart z) := by
    intro z hz
    simp only [g, h, ManifoldDifferentialForm.inExtChartAt_apply]
    rw [chart.left_inv hz]
    congr 3
    funext i
    change (mfderiv I (modelWithCornersSelf ℝ E) chart z).inverse (tuple i) =
      mfderivWithin (modelWithCornersSelf ℝ E) I chart.symm (range ⇑I) (chart z) (tuple i)
    rw [hinv z hz]
    rfl
  have hdiff : DifferentiableWithinAt ℝ h chart.target (chart q) := by
    apply hcoord.continuousAlternatingMap_apply
    intro i
    exact differentiableWithinAt_const (tuple i)
  have hmdiff : MDifferentiableWithinAt (modelWithCornersSelf ℝ E)
      (modelWithCornersSelf ℝ W) h chart.target (chart q) := by
    rwa [mdifferentiableWithinAt_iff_differentiableWithinAt]
  have chartmdiff : MDifferentiableWithinAt I (modelWithCornersSelf ℝ E)
      chart chart.source q :=
    (mdifferentiableAt_extChartAt (I := I) (x := p)
      (by simpa [chart] using hq)).mdifferentiableWithinAt
  have chain := mfderivWithin_comp (I' := modelWithCornersSelf ℝ E)
    (u := chart.target) q hmdiff chartmdiff
    (fun z hz => chart.map_source hz)
    ((isOpen_extChartAt_source p).uniqueMDiffWithinAt (by simpa [chart] using hq'))
  have deriv_eq : mfderivWithin I (modelWithCornersSelf ℝ W) g chart.source q =
      (mfderivWithin (modelWithCornersSelf ℝ E) (modelWithCornersSelf ℝ W)
          h chart.target (chart q)).comp
        (mfderivWithin I (modelWithCornersSelf ℝ E) chart chart.source q) := by
    rw [eval_eq q hq']
    rw [mfderivWithin_congr (fun z hz => eval_eq z hz) (eval_eq q hq')]
    exact chain
  have chart_within_eq :
      mfderivWithin I (modelWithCornersSelf ℝ E) chart chart.source q =
        mfderiv I (modelWithCornersSelf ℝ E) chart q := by
    apply mfderivWithin_eq_mfderiv
    · exact (isOpen_extChartAt_source p).uniqueMDiffWithinAt (by simpa [chart] using hq')
    · exact mdifferentiableAt_extChartAt (I := I) (x := p) (by simpa [chart] using hq)
  change (NormedSpace.fromTangentSpace (coordinates (form q (fun i => fields i q))))
      (mfderivWithin I (modelWithCornersSelf ℝ W) g chart.source q (first q)) =
    fderivWithin ℝ h chart.target (chart q) v
  rw [deriv_eq, chart_within_eq]
  change ((mfderivWithin (modelWithCornersSelf ℝ E) (modelWithCornersSelf ℝ W)
      h chart.target (chart q)).comp (mfderiv I (modelWithCornersSelf ℝ E) chart q))
      ((mfderiv I (modelWithCornersSelf ℝ E) chart q).inverse v) = _
  have cancel :
      mfderiv I (modelWithCornersSelf ℝ E) chart q
          ((mfderiv I (modelWithCornersSelf ℝ E) chart q).inverse v) = v := by
    rw [hinv q hq']
    have hcomp := mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm
      (I := I) (x := p) (chart.map_source hq')
    have hleft : chart.symm (chart q) = q := chart.left_inv hq'
    rw [hleft] at hcomp
    exact congrArg (fun L : E →L[ℝ] E => L v) hcomp
  rw [ContinuousLinearMap.comp_apply, cancel, mfderivWithin_eq_fderivWithin]
  rfl

private lemma positiveDegreeCartanExpressionCoordinates_inExtChartAt_center
    (coordinates : V ≃L[ℝ] W) (n : ℕ)
    (form : ManifoldDifferentialForm I M V (n + 1)) (p : M)
    (vectors : Fin (n + 2) → E)
    (hcoord : DifferentiableWithinAt ℝ
      (form.inExtChartAt coordinates (n + 1) p)
      (extChartAt I p).target ((extChartAt I p) p)) :
    form.positiveDegreeCartanExpressionCoordinates coordinates n
        (extChartAt I p).source p
        (fun i => VectorField.mpullback I (modelWithCornersSelf ℝ E)
          (extChartAt I p) (fun _ => vectors i)) =
      ManifoldDifferentialForm.positiveDegreeCartanExpressionCoordinates
        (I := modelWithCornersSelf ℝ E) (ContinuousLinearEquiv.refl ℝ W) n
        (form.inExtChartAt coordinates (n + 1) p).toManifoldForm
        (extChartAt I p).target ((extChartAt I p) p) (fun i _ => vectors i) := by
  rw [ManifoldDifferentialForm.positiveDegreeCartanExpressionCoordinates_normedSpace]
  unfold ManifoldDifferentialForm.positiveDegreeCartanExpressionCoordinates
  congr 1
  · apply Finset.sum_congr rfl
    intro i hi
    congr 1
    have removed_fields (y : M) :
        i.removeNth (fun k => VectorField.mpullback I (modelWithCornersSelf ℝ E)
          (extChartAt I p) (fun _ => vectors k) y) =
        (fun a => VectorField.mpullback I (modelWithCornersSelf ℝ E)
          (extChartAt I p) (fun _ => (i.removeNth vectors) a) y) := by
      funext a
      rw [Fin.removeNth_apply, Fin.removeNth_apply]
    have removed_function :
        (fun y => coordinates (form y (i.removeNth (fun k =>
          VectorField.mpullback I (modelWithCornersSelf ℝ E)
            (extChartAt I p) (fun _ => vectors k) y)))) =
        (fun y => coordinates (form y (fun a =>
          VectorField.mpullback I (modelWithCornersSelf ℝ E)
            (extChartAt I p) (fun _ => (i.removeNth vectors) a) y))) := by
      funext y
      rw [removed_fields y]
    rw [removed_fields p, removed_function]
    exact eval_mpullback_extChart_derivative_naturality_at_source
      coordinates (n + 1) form p p (mem_extChartAt_source p)
      (i.removeNth vectors) (vectors i) hcoord
  · apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    congr 1
    have bracket_zero :=
      ManifoldDifferentialForm.mlieBracketWithin_mpullback_extChart_const_const
        (I := I) p p (mem_extChartAt_source p) (vectors i.castSucc) (vectors j.succ)
    rw [bracket_zero]
    have coordinate_bracket_zero :
        VectorField.lieBracketWithin ℝ (fun _ => vectors i.castSucc)
          (fun _ => vectors j.succ) (extChartAt I p).target ((extChartAt I p) p) = 0 := by
      simp [VectorField.lieBracketWithin]
    rw [coordinate_bracket_zero]
    have left_zero : coordinates (form p (Matrix.vecCons 0
        (j.removeNth (i.castSucc.removeNth (fun k =>
          VectorField.mpullback I (modelWithCornersSelf ℝ E)
            (extChartAt I p) (fun _ => vectors k) p))))) = 0 := by
      rw [(form p).map_coord_zero 0 rfl, map_zero]
    have right_zero :
        form.inExtChartAt coordinates (n + 1) p ((extChartAt I p) p)
          (Matrix.vecCons 0
            (j.removeNth (i.castSucc.removeNth (fun k => vectors k)))) = 0 := by
      apply (form.inExtChartAt coordinates (n + 1) p ((extChartAt I p) p)).map_coord_zero 0
      rfl
    rw [left_zero, right_zero]



lemma SmoothManifoldPositiveDegreeExteriorDerivativeCertificate.inExtChartAt_derivative_eq_extDerivWithin_of_differentiable
    (coordinates : V ≃L[ℝ] W) (n : ℕ)
    (form : SmoothManifoldDifferentialForm I M V coordinates (n + 1))
    (certificate : SmoothManifoldPositiveDegreeExteriorDerivativeCertificate coordinates n form)
    (p : M)
    (hcoord : DifferentiableWithinAt ℝ
      (form.toForm.inExtChartAt coordinates (n + 1) p)
      (extChartAt I p).target ((extChartAt I p) p)) :
    certificate.derivative.toForm.inExtChartAt coordinates (n + 2) p ((extChartAt I p) p) =
      extDerivWithin (form.toForm.inExtChartAt coordinates (n + 1) p)
        (extChartAt I p).target ((extChartAt I p) p) := by
  ext vectors
  let fields : Fin (n + 2) → (q : M) → TangentSpace I q := fun i =>
    VectorField.mpullback I (modelWithCornersSelf ℝ E)
      (extChartAt I p) (fun _ => vectors i)
  have fields_smooth : ∀ i, ManifoldTangentField.IsSmoothOn I
      (extChartAt I p).source (fields i) := fun i => by
    simpa [fields, extChartPulledBackConstantField] using
      (extChartPulledBackConstantField_isSmoothOn (I := I) p (vectors i))
  have unique_target : UniqueDiffWithinAt ℝ
      (extChartAt I p).target ((extChartAt I p) p) := by
    have h : UniqueDiffOn ℝ ((extChartAt I p).target ∩
        (extChartAt I p).symm ⁻¹' (Set.univ : Set M)) :=
      (uniqueMDiffOn_univ (I := I)).uniqueDiffOn_target_inter p
    simpa only [preimage_univ, inter_univ] using
      h.uniqueDiffWithinAt ⟨mem_extChartAt_target p, trivial⟩
  have ext_formula :=
    (form.toForm.inExtChartAt coordinates (n + 1) p)
      |>.extDerivWithin_eq_positiveDegreeCartanExpression n
        (extChartAt I p).target ((extChartAt I p) p)
        (fun i _ => vectors i) hcoord
        (fun i => differentiableWithinAt_const (vectors i)) unique_target
  rw [ext_formula]
  rw [← positiveDegreeCartanExpressionCoordinates_inExtChartAt_center
    coordinates n form.toForm p vectors hcoord]
  rw [← certificate.cartan_formula (extChartAt I p).source p
    (isOpen_extChartAt_source p) (mem_extChartAt_source p)
    (isOpen_extChartAt_source p).uniqueMDiffOn fields fields_smooth]
  simp only [ManifoldDifferentialForm.inExtChartAt_apply]
  rw [extChartAt_to_inv, mfderivWithin_range_extChartAt_symm]
  congr 3
  funext i
  change vectors i =
    (mfderiv I (modelWithCornersSelf ℝ E) (extChartAt I p) p).inverse (vectors i)
  symm
  apply (isInvertible_mfderiv_extChartAt (mem_extChartAt_source p)).inverse_apply_eq.mpr
  rw [mfderiv_extChartAt_self]
  rfl

/-- Every smooth positive-degree Cartan certificate is exactly Mathlib's exterior derivative in
its inverse extended chart at the chart center, on the exact chart target. -/
lemma SmoothManifoldPositiveDegreeExteriorDerivativeCertificate.inExtChartAt_derivative_eq_extDerivWithin
    (coordinates : V ≃L[ℝ] W) (n : ℕ)
    (form : SmoothManifoldDifferentialForm I M V coordinates (n + 1))
    (certificate : SmoothManifoldPositiveDegreeExteriorDerivativeCertificate coordinates n form)
    (p : M) :
    certificate.derivative.toForm.inExtChartAt coordinates (n + 2) p ((extChartAt I p) p) =
      extDerivWithin (form.toForm.inExtChartAt coordinates (n + 1) p)
        (extChartAt I p).target ((extChartAt I p) p) :=
  certificate.inExtChartAt_derivative_eq_extDerivWithin_of_differentiable
    coordinates n form p
      (SmoothManifoldDifferentialForm.inExtChartAt_differentiableWithinAt_target
        coordinates (n + 1) form p)

end
end YangMills.Mathematics
