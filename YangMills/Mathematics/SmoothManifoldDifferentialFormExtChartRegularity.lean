/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Mathematics.ManifoldDifferentialFormNormedCoordinates
import YangMills.Mathematics.ManifoldOneFormExteriorDerivative
import YangMills.Mathematics.SmoothManifoldDifferentialForms
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.VectorField.Pullback
import Mathlib.Analysis.Normed.Operator.Bilinear

/-!
# Arbitrary-degree inverse-extended-chart regularity

This module upgrades evaluation-smooth fixed-value manifold differential forms of every finite
degree to `C∞` alternating-map-valued coordinates at a centered inverse extended chart. Tangent
transport remains the corner-aware `mfderivWithin` on `Set.range I`; target and model-range
regularity are exposed separately.
-/

namespace YangMills.Mathematics

open Set Function Filter ChartedSpace IsManifold Bundle
open scoped Manifold ContDiff Topology Bundle

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

/-- The intrinsic field obtained by pulling a constant model vector back through the extended chart
centered at `p`. -/
noncomputable def extChartPulledBackConstantField
    (p : M) (v : E) : (q : M) → TangentSpace I q :=
  VectorField.mpullback I (modelWithCornersSelf ℝ E) (extChartAt I p) (fun _ => v)

/-- A pulled-back constant chart field is smooth on the exact extended-chart source. -/
theorem extChartPulledBackConstantField_isSmoothOn
    (p : M) (v : E) :
    ManifoldTangentField.IsSmoothOn I (extChartAt I p).source
      (extChartPulledBackConstantField (I := I) p v) := by
  let chart := extChartAt I p
  let constantField : (x : E) → TangentSpace (modelWithCornersSelf ℝ E) x := fun _ => v
  have constantField_smooth : ContMDiff (modelWithCornersSelf ℝ E)
      ((modelWithCornersSelf ℝ E).prod (modelWithCornersSelf ℝ E)) ∞
      (fun x => (⟨x, constantField x⟩ : TangentBundle (modelWithCornersSelf ℝ E) E)) := by
    rw [contMDiff_vectorSpace_iff_contDiff]
    exact contDiff_const
  intro q hq
  have hq' : q ∈ (chartAt H p).source := by simpa [chart] using hq
  simpa [extChartPulledBackConstantField, chart, constantField] using
    (constantField_smooth.contMDiffAt.mpullback_vectorField_preimage
      (m := ∞) (n := ∞) (contMDiffAt_extChartAt' hq')
      (isInvertible_mfderiv_extChartAt hq) (by simp)).contMDiffWithinAt

private lemma inExtChartAt_eval_contDiffWithinAt
    (coordinates : V ≃L[ℝ] W) (k : ℕ)
    (form : SmoothManifoldDifferentialForm I M V coordinates k)
    (p : M) (tuple : Fin k → E) :
    ContDiffWithinAt ℝ ∞
      (fun x => form.toForm.inExtChartAt coordinates k p x tuple)
      (extChartAt I p).target ((extChartAt I p) p) := by
  letI : CompleteSpace E := FiniteDimensional.complete ℝ E
  let chart := extChartAt I p
  let fields : Fin k → (q : M) → TangentSpace I q := fun i =>
    extChartPulledBackConstantField (I := I) p (tuple i)
  have fields_smooth : ∀ i, ManifoldTangentField.IsSmoothOn I chart.source (fields i) := by
    intro i
    exact extChartPulledBackConstantField_isSmoothOn p (tuple i)
  have eval_smooth := form.eval_smooth chart.source fields fields_smooth
  have eval_at : ContMDiffWithinAt I (modelWithCornersSelf ℝ W) ∞
      (fun q => coordinates (form.toForm q (fun i => fields i q))) chart.source p :=
    eval_smooth p (mem_extChartAt_source p)
  have composed : ContMDiffWithinAt (modelWithCornersSelf ℝ E)
      (modelWithCornersSelf ℝ W) ∞
      (fun x => coordinates (form.toForm (chart.symm x) (fun i => fields i (chart.symm x))))
      chart.target (chart p) := by
    exact ContMDiffWithinAt.comp_of_eq
      (g := fun q => coordinates (form.toForm q (fun i => fields i q)))
      (f := chart.symm) (t := chart.source) (s := chart.target)
      eval_at (contMDiffWithinAt_extChartAt_symm_target_self p)
      (by intro x hx; exact chart.map_target hx)
      (chart.left_inv (mem_extChartAt_source p))
  have eq_on : ∀ x ∈ chart.target,
      coordinates (form.toForm (chart.symm x) (fun i => fields i (chart.symm x))) =
        form.toForm.inExtChartAt coordinates k p x tuple := by
    intro x hx
    rw [ManifoldDifferentialForm.inExtChartAt_apply]
    congr 3
    funext i
    simp only [fields, extChartPulledBackConstantField, VectorField.mpullback_apply]
    have hright : (extChartAt I p) ((extChartAt I p).symm x) = x :=
      (extChartAt I p).right_inv (by simpa [chart] using hx)
    rw [show chart (chart.symm x) = x by simpa [chart] using hright]
    have hcomp := mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm
      (I := I) (x := p) hx
    have hcomp' := mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt
      (I := I) (x := p) hx
    rw [hright] at hcomp
    have hinv := ContinuousLinearMap.inverse_eq hcomp hcomp'
    simpa [chart] using congrArg (fun L => L (tuple i)) hinv
  exact composed.contDiffWithinAt.congr (fun x hx => (eq_on x hx).symm)
    (eq_on _ (mem_extChartAt_target p)).symm

private noncomputable def alternatizationCLM (k : ℕ) :
    ContinuousMultilinearMap ℝ (fun _ : Fin k => E) W →L[ℝ]
      (E [⋀^Fin k]→L[ℝ] W) := by
  let L : ContinuousMultilinearMap ℝ (fun _ : Fin k => E) W →ₗ[ℝ]
      (E [⋀^Fin k]→L[ℝ] W) :=
    { toFun := fun f => ContinuousMultilinearMap.alternatization f
      map_add' := fun f g => (ContinuousMultilinearMap.alternatization :
        ContinuousMultilinearMap ℝ (fun _ : Fin k => E) W →+
          (E [⋀^Fin k]→L[ℝ] W)).map_add f g
      map_smul' := by
        intro c f
        ext v
        simp [ContinuousMultilinearMap.alternatization_apply_apply,
          Finset.smul_sum, smul_comm c] }
  exact LinearMap.mkContinuous L (Fintype.card (Equiv.Perm (Fin k))) (by
    intro f
    change ‖∑ σ : Equiv.Perm (Fin k), Equiv.Perm.sign σ • f.domDomCongr σ‖ ≤
      (Fintype.card (Equiv.Perm (Fin k)) : ℝ) * ‖f‖
    calc
      _ ≤ ∑ σ : Equiv.Perm (Fin k), ‖Equiv.Perm.sign σ • f.domDomCongr σ‖ := by
        simpa using (norm_sum_le Finset.univ
          (fun σ : Equiv.Perm (Fin k) => Equiv.Perm.sign σ • f.domDomCongr σ))
      _ = ∑ _σ : Equiv.Perm (Fin k), ‖f‖ := by
        apply Finset.sum_congr rfl
        intro σ hσ
        change ‖((Equiv.Perm.sign σ : ℤ) • f.domDomCongr σ)‖ = ‖f‖
        rw [norm_isUnit_zsmul _ (Equiv.Perm.sign σ).isUnit,
          ContinuousMultilinearMap.norm_domDomCongr]
      _ = (Fintype.card (Equiv.Perm (Fin k)) : ℝ) * ‖f‖ := by simp)

private noncomputable def reconstructMultilinearCLM
    (k : ℕ) (b : Module.Basis (Module.Basis.ofVectorSpaceIndex ℝ E) ℝ E) :
    ((Fin k → Module.Basis.ofVectorSpaceIndex ℝ E) → W) →L[ℝ]
      ContinuousMultilinearMap ℝ (fun _ : Fin k => E) W := by
  let coord (i : Module.Basis.ofVectorSpaceIndex ℝ E) : E →L[ℝ] ℝ :=
    (ContinuousLinearMap.proj i).comp
      b.equivFun.toContinuousLinearEquiv.toContinuousLinearMap
  exact ∑ a,
    (ContinuousMultilinearMap.smulRightL ℝ (fun _ : Fin k => E) W
      ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin k) ℝ).compContinuousLinearMap
        (fun j => coord (a j)))).comp (ContinuousLinearMap.proj a)

private lemma reconstructMultilinearCLM_basisValues
    (k : ℕ) (b : Module.Basis (Module.Basis.ofVectorSpaceIndex ℝ E) ℝ E)
    (A : E [⋀^Fin k]→L[ℝ] W) :
    reconstructMultilinearCLM (E := E) (W := W) k b
        (fun a => A (fun j => b (a j))) = A.toContinuousMultilinearMap := by
  apply ContinuousMultilinearMap.toMultilinearMap_injective
  apply Module.Basis.ext_multilinear (fun _ : Fin k => b)
  intro a
  classical
  simp [reconstructMultilinearCLM, ContinuousMultilinearMap.mkPiAlgebra_apply]
  rw [Fintype.sum_eq_single a]
  · simp
  · intro x hx
    obtain ⟨i, hi⟩ : ∃ i, x i ≠ a i := by
      simpa only [Function.ne_iff] using hx
    have hzero : ∏ j, (if a j = x j then (1 : ℝ) else 0) = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      simp [Ne.symm hi]
    simp_rw [Finsupp.single_apply]
    rw [hzero, zero_smul]

omit [FiniteDimensional ℝ E] in
private lemma alternatizationCLM_toContinuousMultilinearMap
    (k : ℕ) (A : E [⋀^Fin k]→L[ℝ] W) :
    alternatizationCLM (E := E) (W := W) k A.toContinuousMultilinearMap =
      (Nat.factorial k : ℝ) • A := by
  rw [show alternatizationCLM (E := E) (W := W) k A.toContinuousMultilinearMap =
      ContinuousMultilinearMap.alternatization A.toContinuousMultilinearMap by rfl]
  apply ContinuousAlternatingMap.toAlternatingMap_injective
  rw [ContinuousMultilinearMap.alternatization_apply_toAlternatingMap]
  have h := AlternatingMap.coe_alternatization A.toAlternatingMap
  rw [Fintype.card_fin] at h
  change MultilinearMap.alternatization A.toMultilinearMap =
    Nat.factorial k • A.toAlternatingMap at h
  rw [h]
  exact (Nat.cast_smul_eq_nsmul ℝ (Nat.factorial k) A.toAlternatingMap).symm

set_option backward.isDefEq.respectTransparency false in
/-- `C∞` regularity of an arbitrary-degree smooth form in its centered inverse extended chart,
on the exact chart target used by exterior calculus. -/
theorem SmoothManifoldDifferentialForm.inExtChartAt_contDiffWithinAt_target
    (coordinates : V ≃L[ℝ] W) (k : ℕ)
    (form : SmoothManifoldDifferentialForm I M V coordinates k) (p : M) :
    ContDiffWithinAt ℝ ∞ (form.toForm.inExtChartAt coordinates k p)
      (extChartAt I p).target ((extChartAt I p) p) := by
  let b := Module.Basis.ofVectorSpace ℝ E
  letI : Fintype (Module.Basis.ofVectorSpaceIndex ℝ E) :=
    FiniteDimensional.fintypeBasisIndex b
  let values : E → (Fin k → Module.Basis.ofVectorSpaceIndex ℝ E) → W := fun x a =>
    form.toForm.inExtChartAt coordinates k p x (fun j => b (a j))
  have values_smooth : ContDiffWithinAt ℝ ∞ values
      (extChartAt I p).target ((extChartAt I p) p) := by
    rw [contDiffWithinAt_pi]
    intro a
    exact inExtChartAt_eval_contDiffWithinAt coordinates k form p (fun j => b (a j))
  let assembled : E → E [⋀^Fin k]→L[ℝ] W := fun x =>
    (Nat.factorial k : ℝ)⁻¹ • alternatizationCLM (E := E) (W := W) k
      (reconstructMultilinearCLM (E := E) (W := W) k b (values x))
  have assembled_smooth : ContDiffWithinAt ℝ ∞ assembled
      (extChartAt I p).target ((extChartAt I p) p) := by
    exact ((values_smooth.continuousLinearMap_comp
      (reconstructMultilinearCLM (E := E) (W := W) k b)).continuousLinearMap_comp
        (alternatizationCLM (E := E) (W := W) k)).const_smul _
  have assembled_eq : assembled = form.toForm.inExtChartAt coordinates k p := by
    funext x
    simp only [assembled]
    rw [reconstructMultilinearCLM_basisValues]
    rw [alternatizationCLM_toContinuousMultilinearMap]
    apply inv_smul_smul₀
    exact_mod_cast Nat.factorial_ne_zero k
  rw [← assembled_eq]
  exact assembled_smooth

/-- The same arbitrary-degree `C∞` regularity on the full corner-model range. -/
theorem SmoothManifoldDifferentialForm.inExtChartAt_contDiffWithinAt_modelRange
    (coordinates : V ≃L[ℝ] W) (k : ℕ)
    (form : SmoothManifoldDifferentialForm I M V coordinates k) (p : M) :
    ContDiffWithinAt ℝ ∞ (form.toForm.inExtChartAt coordinates k p)
      (Set.range ⇑I) ((extChartAt I p) p) :=
  (form.inExtChartAt_contDiffWithinAt_target coordinates k p).mono_of_mem_nhdsWithin
    (extChartAt_target_mem_nhdsWithin p)

/-- Differentiability on the exact chart target, derived from arbitrary-degree `C∞` regularity. -/
theorem SmoothManifoldDifferentialForm.inExtChartAt_differentiableWithinAt_target
    (coordinates : V ≃L[ℝ] W) (k : ℕ)
    (form : SmoothManifoldDifferentialForm I M V coordinates k) (p : M) :
    DifferentiableWithinAt ℝ (form.toForm.inExtChartAt coordinates k p)
      (extChartAt I p).target ((extChartAt I p) p) :=
  (form.inExtChartAt_contDiffWithinAt_target coordinates k p).differentiableWithinAt (by simp)

/-- Differentiability on the exact corner-model range used inside `inExtChartAt`. -/
theorem SmoothManifoldDifferentialForm.inExtChartAt_differentiableWithinAt_modelRange
    (coordinates : V ≃L[ℝ] W) (k : ℕ)
    (form : SmoothManifoldDifferentialForm I M V coordinates k) (p : M) :
    DifferentiableWithinAt ℝ (form.toForm.inExtChartAt coordinates k p)
      (Set.range ⇑I) ((extChartAt I p) p) :=
  (form.inExtChartAt_contDiffWithinAt_modelRange coordinates k p).differentiableWithinAt (by simp)

end
end YangMills.Mathematics
