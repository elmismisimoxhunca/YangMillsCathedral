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
source set. The raw manifold pullback is then identified with the written-chart carrier on the exact chart-safe
set. A local equality of the chart-safe and arbitrary Cartan-calculus sets completes a constructor
that derives arbitrary-smooth-map certificates from exact smooth pullback packages in
finite-dimensional source and target models.
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


omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ E'] in
lemma pullback_inExtChartAt_eqOn
    (f : M → M') (hf : ContMDiff I I' ∞ f)
    (coordinates : V ≃L[ℝ] W) (k : ℕ)
    (form : ManifoldDifferentialForm I' M' V k) (p : M) :
    let g : E → E' := writtenInExtChartAt I I' p f
    let s : Set E := (extChartAt I p).target ∩
      (f ∘ (extChartAt I p).symm) ⁻¹' (extChartAt I' (f p)).source
    Set.EqOn
      ((ManifoldDifferentialForm.pullback f hf form).inExtChartAt coordinates k p)
      (fun x => ((form.inExtChartAt coordinates k (f p)) (g x)).compContinuousLinearMap
        (fderivWithin ℝ g s x)) s := by
  dsimp only
  intro x hx
  apply ContinuousAlternatingMap.ext
  intro vectors
  let q : M := (extChartAt I p).symm x
  have hq_source : q ∈ (extChartAt I p).source := by
    exact (extChartAt I p).map_target hx.1
  have hq : (extChartAt I p) q = x := (extChartAt I p).right_inv hx.1
  have hfq_source : f q ∈ (extChartAt I' (f p)).source := hx.2
  have hg : writtenInExtChartAt I I' p f x = (extChartAt I' (f p)) (f q) := by
    rfl
  simp only [ManifoldDifferentialForm.inExtChartAt_apply,
    ManifoldDifferentialForm.pullback,
    ContinuousAlternatingMap.compContinuousLinearMap_apply]
  rw [show (extChartAt I p).symm x = q from rfl]
  rw [hg, (extChartAt I' (f p)).left_inv hfq_source]
  congr 3
  funext i
  let sourceInv := mfderivWithin (modelWithCornersSelf ℝ E) I
    (extChartAt I p).symm (Set.range ⇑I) x
  let targetInv := mfderivWithin (modelWithCornersSelf ℝ E') I'
    (extChartAt I' (f p)).symm (Set.range ⇑I') ((extChartAt I' (f p)) (f q))
  let sourceSet : Set E := (extChartAt I p).target ∩
    (extChartAt I p).symm ⁻¹' (f ⁻¹' (extChartAt I' (f p)).source)
  let targetChartDeriv := mfderiv I' (modelWithCornersSelf ℝ E')
    (extChartAt I' (f p)) (f q)
  have unique_source_on : UniqueDiffOn ℝ sourceSet := by
    have h := ((isOpen_extChartAt_source (I := I') (f p)).preimage hf.continuous).uniqueMDiffOn
      |>.uniqueDiffOn_target_inter (I := I) p
    simpa [sourceSet] using h
  have unique_source : UniqueMDiffWithinAt (modelWithCornersSelf ℝ E) sourceSet x :=
    UniqueDiffWithinAt.uniqueMDiffWithinAt (unique_source_on x hx)
  have sourceInv_eq : mfderivWithin (modelWithCornersSelf ℝ E) I
      (extChartAt I p).symm sourceSet x = sourceInv := by
    apply MDifferentiableWithinAt.mfderivWithin_mono
      (mdifferentiableWithinAt_extChartAt_symm hx.1) unique_source
    exact inter_subset_left.trans (extChartAt_target_subset_range p)
  have inner_deriv : mfderivWithin (modelWithCornersSelf ℝ E) I'
      (f ∘ (extChartAt I p).symm) sourceSet x =
      (mfderiv I I' f q).comp sourceInv := by
    have h := mfderiv_comp_mfderivWithin_of_eq
      (I := modelWithCornersSelf ℝ E) (I' := I) (I'' := I')
      (g := f) (f := (extChartAt I p).symm) (s := sourceSet)
      (x := x) (y := q)
      (hf.mdifferentiableAt (by simp))
      ((mdifferentiableWithinAt_extChartAt_symm hx.1).mono
        (inter_subset_left.trans (extChartAt_target_subset_range p)))
      unique_source rfl
    rw [sourceInv_eq] at h
    exact h
  have inner_mdiff : MDifferentiableWithinAt (modelWithCornersSelf ℝ E) I'
      (f ∘ (extChartAt I p).symm) sourceSet x :=
    MDifferentiableWithinAt.comp_of_eq
      (I := modelWithCornersSelf ℝ E) (I' := I) (I'' := I')
      (g := f) (f := (extChartAt I p).symm) (u := Set.univ) (s := sourceSet)
      (x := x) (y := q)
      (hf.mdifferentiableAt (by simp)).mdifferentiableWithinAt
      ((mdifferentiableWithinAt_extChartAt_symm hx.1).mono
        (inter_subset_left.trans (extChartAt_target_subset_range p)))
      (by simp) rfl
  have written_deriv : fderivWithin ℝ (writtenInExtChartAt I I' p f)
      sourceSet x = targetChartDeriv.comp ((mfderiv I I' f q).comp sourceInv) := by
    rw [← mfderivWithin_eq_fderivWithin]
    have h := mfderiv_comp_mfderivWithin_of_eq
      (I := modelWithCornersSelf ℝ E) (I' := I')
      (I'' := modelWithCornersSelf ℝ E')
      (g := extChartAt I' (f p)) (f := f ∘ (extChartAt I p).symm)
      (s := sourceSet) (x := x) (y := f q)
      (mdifferentiableAt_extChartAt (I := I') (by simpa using hfq_source))
      inner_mdiff unique_source rfl
    rw [inner_deriv] at h
    exact h
  have cancel_target : targetInv.comp targetChartDeriv = ContinuousLinearMap.id ℝ E' := by
    have hcomp := mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt
      (I := I') (x := f p) (y := (extChartAt I' (f p)) (f q))
      ((extChartAt I' (f p)).map_source hfq_source)
    rw [(extChartAt I' (f p)).left_inv hfq_source] at hcomp
    exact hcomp
  change ((mfderiv I I' f q).comp sourceInv) (vectors i) =
    targetInv ((fderivWithin ℝ (writtenInExtChartAt I I' p f) sourceSet x) (vectors i))
  rw [written_deriv]
  change ((mfderiv I I' f q).comp sourceInv) (vectors i) =
    (targetInv.comp targetChartDeriv) (((mfderiv I I' f q).comp sourceInv) (vectors i))
  rw [cancel_target]
  rfl

omit [FiniteDimensional ℝ E] in
lemma pullback_inExtChartAt_extDerivWithin
    (f : M → M') (hf : ContMDiff I I' ∞ f)
    (coordinates : V ≃L[ℝ] W)
    (form : SmoothManifoldDifferentialForm I' M' V coordinates 1)
    (p : M) :
    let g : E → E' := writtenInExtChartAt I I' p f
    let s : Set E := (extChartAt I p).target ∩
      (f ∘ (extChartAt I p).symm) ⁻¹' (extChartAt I' (f p)).source
    let t : Set E' := (extChartAt I' (f p)).target
    extDerivWithin
        ((ManifoldDifferentialForm.pullback f hf form.toForm).inExtChartAt coordinates 1 p)
        s ((extChartAt I p) p) =
      (extDerivWithin (form.toForm.inExtChartAt coordinates 1 (f p)) t
        ((extChartAt I' (f p)) (f p))).compContinuousLinearMap
          (fderivWithin ℝ g s ((extChartAt I p) p)) := by
  dsimp only
  let g : E → E' := writtenInExtChartAt I I' p f
  let s : Set E := (extChartAt I p).target ∩
    (f ∘ (extChartAt I p).symm) ⁻¹' (extChartAt I' (f p)).source
  let writtenPullback : NormedSpaceDifferentialForm E W 1 := fun x =>
    ((form.toForm.inExtChartAt coordinates 1 (f p)) (g x)).compContinuousLinearMap
      (fderivWithin ℝ g s x)
  have carrier_eq : Set.EqOn
      ((ManifoldDifferentialForm.pullback f hf form.toForm).inExtChartAt coordinates 1 p)
      writtenPullback s := by
    exact pullback_inExtChartAt_eqOn f hf coordinates 1 form.toForm p
  rw [extDerivWithin_congr' carrier_eq ⟨mem_extChartAt_target p, by simp⟩]
  simpa [g, s, writtenPullback] using
    (centeredChart_extDerivWithin_pullback f hf coordinates form p)

omit [FiniteDimensional ℝ E] in
lemma extDerivWithin_congr_set_local
    {n : ℕ} (omega : NormedSpaceDifferentialForm E W n)
    {s t : Set E} {x : E} (h : s =ᶠ[𝓝 x] t) :
    extDerivWithin omega s x = extDerivWithin omega t x := by
  unfold extDerivWithin
  rw [fderivWithin_congr_set h]

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M]
    [FiniteDimensional ℝ E'] [IsManifold I' ∞ M'] in
lemma centered_calculusSet_eventuallyEq_chartSafe
    (f : M → M') (hf : ContMDiff I I' ∞ f)
    (s : Set M) (p : M) (open_s : IsOpen s) (mem_s : p ∈ s) :
    ((extChartAt I p).symm ⁻¹' s ∩ Set.range ⇑I : Set E) =ᶠ[𝓝 ((extChartAt I p) p)]
      ((extChartAt I p).target ∩
        (f ∘ (extChartAt I p).symm) ⁻¹' (extChartAt I' (f p)).source : Set E) := by
  let rangeI : Set E := Set.range ⇑I
  let calculusSet : Set E := (extChartAt I p).symm ⁻¹' s ∩ rangeI
  let chartSafe : Set E := (extChartAt I p).target ∩
    (f ∘ (extChartAt I p).symm) ⁻¹' (extChartAt I' (f p)).source
  have calculus_mem : calculusSet ∈ 𝓝[rangeI] ((extChartAt I p) p) := by
    apply Filter.inter_mem
    · simpa [rangeI] using
        (extChartAt_preimage_mem_nhdsWithin (I := I) (s := Set.univ)
          (mem_nhdsWithin_of_mem_nhds (open_s.mem_nhds mem_s)))
    · exact self_mem_nhdsWithin
  have target_preimage_mem :
      (f ⁻¹' (extChartAt I' (f p)).source) ∈ 𝓝 p :=
    hf.continuous.continuousAt.preimage_mem_nhds
      (extChartAt_source_mem_nhds (I := I') (f p))
  have safe_preimage_mem :
      (extChartAt I p).symm ⁻¹' (f ⁻¹' (extChartAt I' (f p)).source) ∈
        𝓝[rangeI] ((extChartAt I p) p) :=
    by
      simpa [rangeI] using
        (extChartAt_preimage_mem_nhdsWithin (I := I) (s := Set.univ)
          (mem_nhdsWithin_of_mem_nhds target_preimage_mem))
  have chartSafe_mem : chartSafe ∈ 𝓝[rangeI] ((extChartAt I p) p) := by
    exact Filter.inter_mem (extChartAt_target_mem_nhdsWithin p) safe_preimage_mem
  have calculus_union : calculusSet ∪ rangeIᶜ ∈ 𝓝 ((extChartAt I p) p) := by
    rw [← nhdsWithin_univ, ← union_compl_self rangeI, nhdsWithin_union]
    exact Filter.union_mem_sup calculus_mem self_mem_nhdsWithin
  have chartSafe_union : chartSafe ∪ rangeIᶜ ∈ 𝓝 ((extChartAt I p) p) := by
    rw [← nhdsWithin_univ, ← union_compl_self rangeI, nhdsWithin_union]
    exact Filter.union_mem_sup chartSafe_mem self_mem_nhdsWithin
  filter_upwards [calculus_union, chartSafe_union] with x hxCalc hxSafe
  have calculus_subset : calculusSet ⊆ rangeI := inter_subset_right
  have chartSafe_subset : chartSafe ⊆ rangeI :=
    inter_subset_left.trans (extChartAt_target_subset_range p)
  apply propext
  constructor
  · intro hx
    exact hxSafe.resolve_right (fun hnot => hnot (calculus_subset hx))
  · intro hx
    exact hxCalc.resolve_right (fun hnot => hnot (chartSafe_subset hx))

omit [FiniteDimensional ℝ E] in
lemma pullback_certificate_centered_extDeriv
    (f : M → M') (hf : ContMDiff I I' ∞ f)
    (coordinates : V ≃L[ℝ] W)
    (form : SmoothManifoldDifferentialForm I' M' V coordinates 1)
    (certificate : SmoothManifoldOneFormExteriorDerivativeCertificate coordinates form)
    (pulledForm : SmoothManifoldDifferentialForm I M V coordinates 1)
    (pulledForm_eq : pulledForm.toForm =
      ManifoldDifferentialForm.pullback f hf form.toForm)
    (pulledDerivative : SmoothManifoldDifferentialForm I M V coordinates 2)
    (pulledDerivative_eq : pulledDerivative.toForm =
      ManifoldDifferentialForm.pullback f hf certificate.derivative.toForm)
    (s : Set M) (p : M) (open_s : IsOpen s) (mem_s : p ∈ s) :
    pulledDerivative.toForm.inExtChartAt coordinates 2 p ((extChartAt I p) p) =
      extDerivWithin (pulledForm.toForm.inExtChartAt coordinates 1 p)
        ((extChartAt I p).symm ⁻¹' s ∩ Set.range ⇑I) ((extChartAt I p) p) := by
  let calculusSet : Set E := (extChartAt I p).symm ⁻¹' s ∩ Set.range ⇑I
  let chartSafe : Set E := (extChartAt I p).target ∩
    (f ∘ (extChartAt I p).symm) ⁻¹' (extChartAt I' (f p)).source
  let targetSet : Set E' := (extChartAt I' (f p)).target
  let g : E → E' := writtenInExtChartAt I I' p f
  have set_eq : calculusSet =ᶠ[𝓝 ((extChartAt I p) p)] chartSafe := by
    exact centered_calculusSet_eventuallyEq_chartSafe f hf s p open_s mem_s
  have pulled_form_chart : pulledForm.toForm.inExtChartAt coordinates 1 p =
      (ManifoldDifferentialForm.pullback f hf form.toForm).inExtChartAt coordinates 1 p := by
    rw [pulledForm_eq]
  have pulled_derivative_chart : pulledDerivative.toForm.inExtChartAt coordinates 2 p =
      (ManifoldDifferentialForm.pullback f hf certificate.derivative.toForm).inExtChartAt
        coordinates 2 p := by
    rw [pulledDerivative_eq]
  rw [pulled_derivative_chart, pulled_form_chart]
  rw [extDerivWithin_congr_set_local _ set_eq]
  rw [pullback_inExtChartAt_extDerivWithin f hf coordinates form p]
  rw [← certificate.inExtChartAt_derivative_eq_extDerivWithin coordinates form (f p)]
  have center_carrier := pullback_inExtChartAt_eqOn
    f hf coordinates 2 certificate.derivative.toForm p
    ⟨mem_extChartAt_target p, by simp⟩
  simpa [g, chartSafe, targetSet] using center_carrier

noncomputable def SmoothManifoldOneFormExteriorDerivativeCertificate.pullbackSmoothMapOfForms
    (f : M → M') (hf : ContMDiff I I' ∞ f)
    (coordinates : V ≃L[ℝ] W)
    (form : SmoothManifoldDifferentialForm I' M' V coordinates 1)
    (certificate : SmoothManifoldOneFormExteriorDerivativeCertificate coordinates form)
    (pulledForm : SmoothManifoldDifferentialForm I M V coordinates 1)
    (pulledForm_eq : pulledForm.toForm =
      ManifoldDifferentialForm.pullback f hf form.toForm)
    (pulledDerivative : SmoothManifoldDifferentialForm I M V coordinates 2)
    (pulledDerivative_eq : pulledDerivative.toForm =
      ManifoldDifferentialForm.pullback f hf certificate.derivative.toForm) :
    SmoothManifoldOneFormExteriorDerivativeCertificate coordinates pulledForm where
  derivative := pulledDerivative
  cartan_formula := by
    intro s p open_s mem_s unique_s first second first_smooth second_smooth
    let calculusSet : Set E := (extChartAt I p).symm ⁻¹' s ∩ Set.range ⇑I
    let first' : E → E := extChartCoordinateField I p first
    let second' : E → E := extChartCoordinateField I p second
    have centered := pullback_certificate_centered_extDeriv f hf coordinates form certificate
      pulledForm pulledForm_eq pulledDerivative pulledDerivative_eq s p open_s mem_s
    have form_diff : DifferentiableWithinAt ℝ
        (pulledForm.toForm.inExtChartAt coordinates 1 p) calculusSet ((extChartAt I p) p) := by
      letI : CompleteSpace E := FiniteDimensional.complete ℝ E
      exact (SmoothManifoldDifferentialForm.inExtChartAt_differentiableWithinAt_range
        coordinates pulledForm p).mono inter_subset_right
    have first_diff : DifferentiableWithinAt ℝ first' calculusSet ((extChartAt I p) p) := by
      letI : CompleteSpace E := FiniteDimensional.complete ℝ E
      exact extChartCoordinateField_differentiableWithinAt
        I s p mem_s first first_smooth
    have second_diff : DifferentiableWithinAt ℝ second' calculusSet ((extChartAt I p) p) := by
      letI : CompleteSpace E := FiniteDimensional.complete ℝ E
      exact extChartCoordinateField_differentiableWithinAt
        I s p mem_s second second_smooth
    have unique_calculus : UniqueDiffWithinAt ℝ calculusSet ((extChartAt I p) p) := by
      rw [show calculusSet = (extChartAt I p).symm ⁻¹' s ∩ Set.range ⇑I from rfl,
        inter_comm]
      apply unique_s.uniqueDiffWithinAt_range_inter p
      exact ⟨mem_extChartAt_target p, by simpa using mem_s⟩
    have ext_formula :=
      (pulledForm.toForm.inExtChartAt coordinates 1 p).extDerivWithin_eq_oneFormCartanExpression
        calculusSet ((extChartAt I p) p) first' second'
        form_diff first_diff second_diff unique_calculus
    have transport :=
      pulledForm.oneFormCartanExpressionCoordinates_inExtChartAt_arbitraryFields
        coordinates s p mem_s first second first_smooth second_smooth
    have first_center : first' ((extChartAt I p) p) =
        (mfderivWithin (modelWithCornersSelf ℝ E) I (extChartAt I p).symm
          (Set.range ⇑I) ((extChartAt I p) p)).inverse (first p) := by
      dsimp [first', extChartCoordinateField]
      rw [VectorField.mpullbackWithin_apply]
      congr 1
      exact congrArg first (extChartAt_to_inv p)
    have second_center : second' ((extChartAt I p) p) =
        (mfderivWithin (modelWithCornersSelf ℝ E) I (extChartAt I p).symm
          (Set.range ⇑I) ((extChartAt I p) p)).inverse (second p) := by
      dsimp [second', extChartCoordinateField]
      rw [VectorField.mpullbackWithin_apply]
      congr 1
      exact congrArg second (extChartAt_to_inv p)
    have derivative_eval :
        pulledDerivative.toForm.inExtChartAt coordinates 2 p ((extChartAt I p) p)
            (ManifoldDifferentialForm.twoVectorArguments
              (I := modelWithCornersSelf ℝ E) first' second' ((extChartAt I p) p)) =
          coordinates (pulledDerivative.toForm p
            (ManifoldDifferentialForm.twoVectorArguments (I := I) first second p)) := by
      rw [ManifoldDifferentialForm.inExtChartAt_center]
      congr 3
      funext i
      fin_cases i
      · change (mfderivWithin (modelWithCornersSelf ℝ E) I (extChartAt I p).symm
          (Set.range ⇑I) ((extChartAt I p) p)) (first' ((extChartAt I p) p)) = first p
        rw [first_center]
        exact (isInvertible_mfderivWithin_extChartAt_symm
          (I := I) (mem_extChartAt_target p)).self_apply_inverse _
      · change (mfderivWithin (modelWithCornersSelf ℝ E) I (extChartAt I p).symm
          (Set.range ⇑I) ((extChartAt I p) p)) (second' ((extChartAt I p) p)) = second p
        rw [second_center]
        exact (isInvertible_mfderivWithin_extChartAt_symm
          (I := I) (mem_extChartAt_target p)).self_apply_inverse _
    rw [← derivative_eval, centered, ext_formula, ← transport]


end
end YangMills.Mathematics
