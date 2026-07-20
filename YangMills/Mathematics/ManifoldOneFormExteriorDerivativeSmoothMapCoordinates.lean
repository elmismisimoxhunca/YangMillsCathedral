/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Mathematics.OneFormCartanArbitraryFieldChartTransport

/-!
# Centered-chart exterior calculus under arbitrary smooth maps

A supplied manifold Cartan certificate is identified exactly with Mathlib's `extDerivWithin` in the
centered extended chart. Separately, Mathlib's normed-space pullback naturality theorem is applied to
the written-in-chart representative of an arbitrary smooth manifold map on the exact chart-safe
source set. These are the two coordinate-calculus ingredients for a future arbitrary-smooth-map
certificate pullback constructor.

This file does not yet bridge the raw manifold pullback carrier to the written-chart pullback carrier
on that local set and therefore does not construct the final certificate.
-/

namespace YangMills.Mathematics

open Set Function
open scoped Manifold ContDiff

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

lemma pullbackExtChartConstantField_isSmoothOn
    (p : M) (v : E) :
    ManifoldTangentField.IsSmoothOn I (extChartAt I p).source
      (VectorField.mpullback I (modelWithCornersSelf ℝ E)
        (extChartAt I p) (fun _ => v)) := by
  let chart := extChartAt I p
  let constantField : (x : E) → TangentSpace (modelWithCornersSelf ℝ E) x := fun _ => v
  have constantField_smooth : ContMDiff (modelWithCornersSelf ℝ E)
      ((modelWithCornersSelf ℝ E).prod (modelWithCornersSelf ℝ E)) ∞
      (fun x => (⟨x, constantField x⟩ : TangentBundle (modelWithCornersSelf ℝ E) E)) := by
    rw [contMDiff_vectorSpace_iff_contDiff]
    exact contDiff_const
  intro q hq
  have hq' : q ∈ (chartAt H p).source := by simpa [chart] using hq
  exact constantField_smooth.contMDiffAt.mpullback_vectorField_preimage
    (m := ∞) (n := ∞)
    (contMDiffAt_extChartAt' hq')
    (isInvertible_mfderiv_extChartAt hq) (by simp) |>.contMDiffWithinAt

lemma SmoothManifoldOneFormExteriorDerivativeCertificate.inExtChartAt_derivative_eq_extDerivWithin
    (coordinates : V ≃L[ℝ] W)
    (form : SmoothManifoldDifferentialForm I M V coordinates 1)
    (certificate : SmoothManifoldOneFormExteriorDerivativeCertificate coordinates form)
    (p : M) :
    certificate.derivative.toForm.inExtChartAt coordinates 2 p ((extChartAt I p) p) =
      extDerivWithin (form.toForm.inExtChartAt coordinates 1 p)
        (extChartAt I p).target ((extChartAt I p) p) := by
  ext vectors
  let first : (q : M) → TangentSpace I q :=
    VectorField.mpullback I (modelWithCornersSelf ℝ E) (extChartAt I p)
      (fun _ => vectors 0)
  let second : (q : M) → TangentSpace I q :=
    VectorField.mpullback I (modelWithCornersSelf ℝ E) (extChartAt I p)
      (fun _ => vectors 1)
  have first_smooth : ManifoldTangentField.IsSmoothOn I (extChartAt I p).source first :=
    pullbackExtChartConstantField_isSmoothOn p (vectors 0)
  have second_smooth : ManifoldTangentField.IsSmoothOn I (extChartAt I p).source second :=
    pullbackExtChartConstantField_isSmoothOn p (vectors 1)
  have form_diff : DifferentiableWithinAt ℝ
      (form.toForm.inExtChartAt coordinates 1 p) (extChartAt I p).target ((extChartAt I p) p) :=
    (SmoothManifoldDifferentialForm.inExtChartAt_contDiffWithinAt coordinates form p).differentiableWithinAt (by simp)
  have unique_target : UniqueDiffWithinAt ℝ (extChartAt I p).target ((extChartAt I p) p) := by
    have h : UniqueDiffOn ℝ ((extChartAt I p).target ∩
        (extChartAt I p).symm ⁻¹' (Set.univ : Set M)) :=
      (uniqueMDiffOn_univ (I := I)).uniqueDiffOn_target_inter p
    simpa only [preimage_univ, inter_univ] using
      h.uniqueDiffWithinAt ⟨mem_extChartAt_target p, trivial⟩
  have cartan_coord := form.toForm.oneFormCartanExpressionCoordinates_inExtChartAt
    coordinates p ((extChartAt I p) p) (mem_extChartAt_target p)
    (vectors 0) (vectors 1) form_diff
  have ext_formula :=
    (form.toForm.inExtChartAt coordinates 1 p).extDerivWithin_eq_oneFormCartanExpression
      (extChartAt I p).target ((extChartAt I p) p)
      (fun _ => vectors 0) (fun _ => vectors 1) form_diff
      (differentiableWithinAt_const (vectors 0))
      (differentiableWithinAt_const (vectors 1)) unique_target
  have vectors_eq : vectors =
      ManifoldDifferentialForm.twoVectorArguments
        (I := modelWithCornersSelf ℝ E) (fun _ => vectors 0) (fun _ => vectors 1)
          ((extChartAt I p) p) := by
    funext i
    fin_cases i <;> rfl
  rw [vectors_eq, ext_formula, ← cartan_coord, extChartAt_to_inv]
  rw [← certificate.cartan_formula (extChartAt I p).source p
    (isOpen_extChartAt_source p) (mem_extChartAt_source p)
    (isOpen_extChartAt_source p).uniqueMDiffOn first second first_smooth second_smooth]
  simp only [ManifoldDifferentialForm.inExtChartAt_apply]
  rw [extChartAt_to_inv, mfderivWithin_range_extChartAt_symm]
  congr 3
  funext i
  fin_cases i
  · change vectors 0 =
      (mfderiv I (modelWithCornersSelf ℝ E) (extChartAt I p) p).inverse (vectors 0)
    symm
    apply (isInvertible_mfderiv_extChartAt (mem_extChartAt_source p)).inverse_apply_eq.mpr
    rw [mfderiv_extChartAt_self]
    rfl
  · change vectors 1 =
      (mfderiv I (modelWithCornersSelf ℝ E) (extChartAt I p) p).inverse (vectors 1)
    symm
    apply (isInvertible_mfderiv_extChartAt (mem_extChartAt_source p)).inverse_apply_eq.mpr
    rw [mfderiv_extChartAt_self]
    rfl

universe uE' uH' uM'

variable
    {E' : Type uE'} {H' : Type uH'}
    [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E'] [TopologicalSpace H']
    {M' : Type uM'} [TopologicalSpace M']
    {I' : ModelWithCorners ℝ E' H'} [ChartedSpace H' M'] [IsManifold I' ∞ M']

omit [FiniteDimensional ℝ E] in
lemma centeredChart_extDerivWithin_pullback
    (f : M → M') (hf : ContMDiff I I' ∞ f)
    (coordinates : V ≃L[ℝ] W)
    (form : SmoothManifoldDifferentialForm I' M' V coordinates 1)
    (p : M) :
    let g : E → E' := writtenInExtChartAt I I' p f
    let s : Set E := (extChartAt I p).target ∩
      (f ∘ (extChartAt I p).symm) ⁻¹' (extChartAt I' (f p)).source
    let t : Set E' := (extChartAt I' (f p)).target
    extDerivWithin
        (fun x => ((form.toForm.inExtChartAt coordinates 1 (f p)) (g x)).compContinuousLinearMap
          (fderivWithin ℝ g s x)) s ((extChartAt I p) p) =
      (extDerivWithin (form.toForm.inExtChartAt coordinates 1 (f p)) t (g ((extChartAt I p) p))).compContinuousLinearMap
        (fderivWithin ℝ g s ((extChartAt I p) p)) := by
  dsimp only
  let g : E → E' := writtenInExtChartAt I I' p f
  let s : Set E := (extChartAt I p).target ∩
    (f ∘ (extChartAt I p).symm) ⁻¹' (extChartAt I' (f p)).source
  let t : Set E' := (extChartAt I' (f p)).target
  apply extDerivWithin_pullback (r := ∞)
  · have h := SmoothManifoldDifferentialForm.inExtChartAt_contDiffWithinAt
      coordinates form (f p)
    have hg_center : g ((extChartAt I p) p) = (extChartAt I' (f p)) (f p) := by
      simp [g]
    simpa [g] using h.differentiableWithinAt (by simp)
  · have hwritten : ContDiffWithinAt ℝ ∞ g (Set.range ⇑I) ((extChartAt I p) p) := by
      exact (contMDiffAt_iff.mp (hf.contMDiffAt)).2
    apply hwritten.mono
    intro x hx
    exact extChartAt_target_subset_range p hx.1
  · rw [minSmoothness_of_isRCLikeNormedField]
    exact (show (↑(2 : ℕ∞) : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞) from
      WithTop.coe_le_coe.mpr le_top)
  · have hopen : IsOpen (f ⁻¹' (extChartAt I' (f p)).source) :=
      (isOpen_extChartAt_source (f p)).preimage hf.continuous
    have h := hopen.uniqueMDiffOn (I := I) |>.uniqueDiffOn_target_inter p
    change UniqueDiffOn ℝ ((extChartAt I p).target ∩
      (extChartAt I p).symm ⁻¹' (f ⁻¹' (extChartAt I' (f p)).source))
    exact h
  · have hopen : IsOpen (f ⁻¹' (extChartAt I' (f p)).source) :=
      (isOpen_extChartAt_source (f p)).preimage hf.continuous
    have hpU : p ∈ f ⁻¹' (extChartAt I' (f p)).source := mem_extChartAt_source (f p)
    have hpInterior : p ∈ interior (f ⁻¹' (extChartAt I' (f p)).source) :=
      mem_interior_iff_mem_nhds.mpr (hopen.mem_nhds hpU)
    have hpClosure : p ∈ closure (interior (f ⁻¹' (extChartAt I' (f p)).source)) :=
      subset_closure hpInterior
    have hchart := extChartAt_mem_closure_interior (I := I) (x₀ := p)
      hpClosure (mem_extChartAt_source p)
    change (extChartAt I p) p ∈ closure (interior
      ((extChartAt I p).target ∩
        (extChartAt I p).symm ⁻¹' (f ⁻¹' (extChartAt I' (f p)).source)))
    simpa only [inter_comm] using hchart
  · exact ⟨mem_extChartAt_target p, by simp⟩
  · exact writtenInExtChartAt_mapsTo

end
end YangMills.Mathematics
