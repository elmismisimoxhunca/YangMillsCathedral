/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Mathematics.ManifoldDifferentialFormNormedCoordinates
import YangMills.Mathematics.SmoothManifoldDifferentialForms
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.VectorField.Pullback
import Mathlib.Analysis.Normed.Operator.Bilinear

open Set Function Filter ChartedSpace IsManifold Bundle
open scoped Manifold ContDiff Topology Bundle
open YangMills.Mathematics

namespace YangMills.Mathematics

/-!
# Generic extended-chart regularity for smooth manifold one-forms

On a finite-dimensional manifold model, the evaluation-based smoothness interface reconstructs
`C∞` regularity of the complete degree-one alternating-map-valued extended-chart carrier. Fixed
coordinate-vector evaluations are smooth by chart pullback; a finite basis and the exact
`Fin 1` continuous-linear equivalence reconstruct the whole one-form. The result is transferred to
`Set.range I` at the chart center, retaining the corner-aware within-set semantics.
-/

universe uE uH uM uV uW

noncomputable section
set_option backward.isDefEq.respectTransparency false

variable
    {E : Type uE} {H : Type uH}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace H]
    {M : Type uM} [TopologicalSpace M]
    {V : Type uV} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]
    [IsTopologicalAddGroup V] [ContinuousSMul ℝ V]
    {W : Type uW} [NormedAddCommGroup W] [NormedSpace ℝ W]
    {I : ModelWithCorners ℝ E H} [ChartedSpace H M] [IsManifold I ∞ M]

private theorem inExtChartAt_eval_contDiffWithinAt
    (coordinates : V ≃L[ℝ] W)
    (form : SmoothManifoldDifferentialForm I M V coordinates 1)
    (p : M) (v : E) :
    ContDiffWithinAt ℝ ∞
      (fun x => form.toForm.inExtChartAt coordinates 1 p x (fun _ => v))
      (extChartAt I p).target ((extChartAt I p) p) := by
  letI : CompleteSpace E := FiniteDimensional.complete ℝ E
  let chart := extChartAt I p
  let constantField : (x : E) → TangentSpace (modelWithCornersSelf ℝ E) x := fun _ => v
  let field : (q : M) → TangentSpace I q :=
    VectorField.mpullback I (modelWithCornersSelf ℝ E) chart constantField
  have constantField_smooth : ContMDiff (modelWithCornersSelf ℝ E)
      ((modelWithCornersSelf ℝ E).prod (modelWithCornersSelf ℝ E)) ∞
      (fun x => (⟨x, constantField x⟩ : TangentBundle (modelWithCornersSelf ℝ E) E)) := by
    rw [contMDiff_vectorSpace_iff_contDiff]
    exact contDiff_const
  have field_smooth : ContMDiffOn I (I.prod (modelWithCornersSelf ℝ E)) ∞
      (fun q => (⟨q, field q⟩ : TangentBundle I M)) chart.source := by
    intro q hq
    have hq' : q ∈ (chartAt H p).source := by simpa [chart] using hq
    have h := constantField_smooth.contMDiffAt.mpullback_vectorField_preimage
      (m := ∞) (n := ∞)
      (contMDiffAt_extChartAt' hq')
      (isInvertible_mfderiv_extChartAt hq) (by simp)
    exact h.contMDiffWithinAt
  have eval_smooth := form.eval_smooth chart.source (fun _ => field) (fun _ => field_smooth)
  have eval_at : ContMDiffWithinAt I (modelWithCornersSelf ℝ W) ∞
      (fun q => coordinates (form.toForm q (fun _ => field q))) chart.source p :=
    eval_smooth p (mem_extChartAt_source p)
  have composed : ContMDiffWithinAt (modelWithCornersSelf ℝ E)
      (modelWithCornersSelf ℝ W) ∞
      (fun x => coordinates (form.toForm (chart.symm x) (fun _ => field (chart.symm x))))
      chart.target (chart p) := by
    exact ContMDiffWithinAt.comp_of_eq
      (g := fun q => coordinates (form.toForm q (fun _ => field q)))
      (f := chart.symm) (t := chart.source) (s := chart.target)
      eval_at (contMDiffWithinAt_extChartAt_symm_target_self p)
      (by intro x hx; exact chart.map_target hx)
      (chart.left_inv (mem_extChartAt_source p))
  have eq_on : ∀ x ∈ chart.target,
      coordinates (form.toForm (chart.symm x) (fun _ => field (chart.symm x))) =
        form.toForm.inExtChartAt coordinates 1 p x (fun _ => v) := by
    intro x hx
    rw [ManifoldDifferentialForm.inExtChartAt_apply]
    congr 3
    funext i
    simp only [field, VectorField.mpullback_apply, constantField]
    have hright : (extChartAt I p) ((extChartAt I p).symm x) = x :=
      (extChartAt I p).right_inv (by simpa [chart] using hx)
    rw [show chart (chart.symm x) = x by simpa [chart] using hright]
    have hcomp :=
      mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm (I := I) (x := p) hx
    have hcomp' :=
      mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt (I := I) (x := p) hx
    rw [hright] at hcomp
    have hinv := ContinuousLinearMap.inverse_eq hcomp hcomp'
    simpa [chart] using congrArg (fun L => L v) hinv
  exact composed.contDiffWithinAt.congr (fun x hx => (eq_on x hx).symm) (eq_on _ (mem_extChartAt_target p)).symm

/-- Generic centered chart regularity for evaluation-smooth one-forms on finite-dimensional
model spaces. -/
theorem SmoothManifoldDifferentialForm.inExtChartAt_contDiffWithinAt
    (coordinates : V ≃L[ℝ] W)
    (form : SmoothManifoldDifferentialForm I M V coordinates 1)
    (p : M) :
    ContDiffWithinAt ℝ ∞ (form.toForm.inExtChartAt coordinates 1 p)
      (extChartAt I p).target ((extChartAt I p) p) := by
  let b := Module.Basis.ofVectorSpace ℝ E
  letI : Fintype (Module.Basis.ofVectorSpaceIndex ℝ E) :=
    FiniteDimensional.fintypeBasisIndex b
  let coord (i : Module.Basis.ofVectorSpaceIndex ℝ E) : E →L[ℝ] ℝ :=
    (ContinuousLinearMap.proj i).comp
      b.equivFun.toContinuousLinearEquiv.toContinuousLinearMap
  let reconstruct :
      (Module.Basis.ofVectorSpaceIndex ℝ E → W) →L[ℝ] (E →L[ℝ] W) :=
    ∑ i, (ContinuousLinearMap.smulRightL ℝ E W (coord i)).comp
      (ContinuousLinearMap.proj i)
  let oneFormEquiv :=
    ContinuousAlternatingMap.ofSubsingletonLIE (𝕜 := ℝ) (E := E) (F := W) (0 : Fin 1)
  let assemble :
      (Module.Basis.ofVectorSpaceIndex ℝ E → W) →L[ℝ]
        (E [⋀^Fin 1]→L[ℝ] W) :=
    oneFormEquiv.toContinuousLinearEquiv.toContinuousLinearMap.comp reconstruct
  have basisValues_smooth : ContDiffWithinAt ℝ ∞
      (fun x i => form.toForm.inExtChartAt coordinates 1 p x (fun _ => b i))
      (extChartAt I p).target ((extChartAt I p) p) := by
    rw [contDiffWithinAt_pi]
    intro i
    exact inExtChartAt_eval_contDiffWithinAt coordinates form p (b i)
  have assembled_smooth : ContDiffWithinAt ℝ ∞
      (fun x => assemble (fun i =>
        form.toForm.inExtChartAt coordinates 1 p x (fun _ => b i)))
      (extChartAt I p).target ((extChartAt I p) p) :=
    basisValues_smooth.continuousLinearMap_comp assemble
  have assemble_eq : ∀ x,
      assemble (fun i => form.toForm.inExtChartAt coordinates 1 p x (fun _ => b i)) =
        form.toForm.inExtChartAt coordinates 1 p x := by
    intro x
    let A := form.toForm.inExtChartAt coordinates 1 p x
    apply oneFormEquiv.symm.injective
    change reconstruct (fun i => A (fun _ => b i)) = oneFormEquiv.symm A
    ext z
    simp only [reconstruct, sum_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRightL_apply_apply,
      coord]
    change (∑ i, b.equivFun z i • A (fun _ => b i)) =
      (oneFormEquiv.symm A) z
    let L := oneFormEquiv.symm A
    change (∑ i, b.equivFun z i • L (b i)) = L z
    calc
      (∑ i, b.equivFun z i • L (b i)) =
          ∑ i, L (b.equivFun z i • b i) := by simp
      _ = L (∑ i, b.equivFun z i • b i) := by
        simpa using (map_sum L (fun i => b.equivFun z i • b i) Finset.univ).symm
      _ = L z := by rw [b.sum_equivFun]
  exact assembled_smooth.congr (fun x hx => (assemble_eq x).symm) (assemble_eq _).symm

/-- The same centered regularity on the full corner-model range, since the chart target is a
neighborhood of the center within that range. -/
theorem SmoothManifoldDifferentialForm.inExtChartAt_contDiffWithinAt_range
    (coordinates : V ≃L[ℝ] W)
    (form : SmoothManifoldDifferentialForm I M V coordinates 1)
    (p : M) :
    ContDiffWithinAt ℝ ∞ (form.toForm.inExtChartAt coordinates 1 p)
      (Set.range ⇑I) ((extChartAt I p) p) :=
  (SmoothManifoldDifferentialForm.inExtChartAt_contDiffWithinAt
    coordinates form p).mono_of_mem_nhdsWithin
    (extChartAt_target_mem_nhdsWithin p)

/-- In particular, the centered coordinate one-form is differentiable on the exact corner-model
range used in `inExtChartAt`. -/
theorem SmoothManifoldDifferentialForm.inExtChartAt_differentiableWithinAt_range
    (coordinates : V ≃L[ℝ] W)
    (form : SmoothManifoldDifferentialForm I M V coordinates 1)
    (p : M) :
    DifferentiableWithinAt ℝ (form.toForm.inExtChartAt coordinates 1 p)
      (Set.range ⇑I) ((extChartAt I p) p) :=
  (SmoothManifoldDifferentialForm.inExtChartAt_contDiffWithinAt_range
    coordinates form p).differentiableWithinAt (by simp)

end
end YangMills.Mathematics
