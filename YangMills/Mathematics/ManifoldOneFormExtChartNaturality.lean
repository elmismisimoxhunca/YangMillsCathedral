/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Mathematics.ManifoldDifferentialFormNormedCoordinates
import YangMills.Mathematics.ManifoldOneFormExteriorDerivative
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Geometry.Manifold.VectorField.LieBracket

/-!
# Inverse-extended-chart naturality of the one-form Cartan expression

This module proves reusable corner-aware Cartan transport for arbitrary fixed-value manifold
one-forms. It keeps the inverse-chart tangent transport on `Set.range I` and exterior calculus on the
actual extended-chart target. The two directional derivative terms follow from the within-manifold
chain rule and inverse tangent identities. Mathlib's pullback theorem transports the Lie bracket;
Constant-coordinate vector fields make that bracket vanish.

No principal connection, curvature, or Bianchi datum occurs in this mathematics layer.
-/

namespace YangMills.Mathematics

open Set Function
open scoped Manifold ContDiff

universe uE uH uM uV uW

variable
    {E : Type uE} {H : Type uH}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
    {M : Type uM} [TopologicalSpace M]
    {V : Type uV} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]
    [IsTopologicalAddGroup V] [ContinuousSMul ℝ V]
    {W : Type uW} [NormedAddCommGroup W] [NormedSpace ℝ W]
    {I : ModelWithCorners ℝ E H} [ChartedSpace H M] [IsManifold I ∞ M]
    [FiniteDimensional ℝ E]

noncomputable section

omit [FiniteDimensional ℝ E] in
private theorem oneForm_eval_mpullback_extChart_derivative_naturality_at_source
    (coordinates : V ≃L[ℝ] W) (form : ManifoldDifferentialForm I M V 1)
    (p q : M) (hq : q ∈ (extChartAt I p).source) (v w : E)
    (hcoord : DifferentiableWithinAt ℝ
      (form.inExtChartAt coordinates 1 p) (extChartAt I p).target ((extChartAt I p) q)) :
    (NormedSpace.fromTangentSpace
      (coordinates (form q (fun _ =>
        VectorField.mpullback I (modelWithCornersSelf ℝ E)
          (extChartAt I p) (fun _ => w) q))))
      (mfderivWithin I (modelWithCornersSelf ℝ W)
        (fun y => coordinates (form y (fun _ =>
          VectorField.mpullback I (modelWithCornersSelf ℝ E)
            (extChartAt I p) (fun _ => w) y)))
        (extChartAt I p).source q
        (VectorField.mpullback I (modelWithCornersSelf ℝ E)
          (extChartAt I p) (fun _ => v) q)) =
      fderivWithin ℝ
        (fun y => form.inExtChartAt coordinates 1 p y (fun _ => w))
        (extChartAt I p).target ((extChartAt I p) q) v := by
  let chart : PartialEquiv M E := extChartAt I p
  let first : (z : M) → TangentSpace I z :=
    VectorField.mpullback I (modelWithCornersSelf ℝ E) chart (fun _ => v)
  let second : (z : M) → TangentSpace I z :=
    VectorField.mpullback I (modelWithCornersSelf ℝ E) chart (fun _ => w)
  let g : M → W := fun z => coordinates (form z (fun _ => second z))
  let h : E → W := fun y => form.inExtChartAt coordinates 1 p y (fun _ => w)
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
    change (mfderiv I (modelWithCornersSelf ℝ E) chart z).inverse w =
      mfderivWithin (modelWithCornersSelf ℝ E) I chart.symm (range ⇑I) (chart z) w
    rw [hinv z hz]
    rfl
  have hdiff : DifferentiableWithinAt ℝ h chart.target (chart q) := by
    apply hcoord.continuousAlternatingMap_apply
    intro i
    exact differentiableWithinAt_const w
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
  change (NormedSpace.fromTangentSpace (coordinates (form q (fun _ => second q))))
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

/-- Pullbacks of constant coordinate fields have zero intrinsic within-chart Lie bracket. -/
theorem ManifoldDifferentialForm.mlieBracketWithin_mpullback_extChart_const_const
    (p q : M) (hq : q ∈ (extChartAt I p).source) (v w : E) :
    VectorField.mlieBracketWithin I
        (VectorField.mpullback I (modelWithCornersSelf ℝ E)
          (extChartAt I p) (fun _ => v))
        (VectorField.mpullback I (modelWithCornersSelf ℝ E)
          (extChartAt I p) (fun _ => w))
        (extChartAt I p).source q = 0 := by
  letI : CompleteSpace E := FiniteDimensional.complete ℝ E
  letI : IsManifold I (minSmoothness ℝ 2) M :=
    IsManifold.of_le (m := minSmoothness ℝ 2) (n := ∞) (by
      rw [minSmoothness_of_isRCLikeNormedField]
      exact (show (↑(2 : ℕ∞) : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞) from
        WithTop.coe_le_coe.mpr le_top))
  let chart : PartialEquiv M E := extChartAt I p
  let Vc : (y : E) → TangentSpace (modelWithCornersSelf ℝ E) y := fun _ => v
  let Wc : (y : E) → TangentSpace (modelWithCornersSelf ℝ E) y := fun _ => w
  have Vc_smooth : ContMDiff (modelWithCornersSelf ℝ E)
      ((modelWithCornersSelf ℝ E).prod (modelWithCornersSelf ℝ E)) ∞
      (fun y => (⟨y, Vc y⟩ : TangentBundle (modelWithCornersSelf ℝ E) E)) := by
    apply contMDiff_vectorSpace_iff_contDiff.mpr
    simpa [Vc] using (contDiff_const : ContDiff ℝ ∞ (fun _ : E => v))
  have Wc_smooth : ContMDiff (modelWithCornersSelf ℝ E)
      ((modelWithCornersSelf ℝ E).prod (modelWithCornersSelf ℝ E)) ∞
      (fun y => (⟨y, Wc y⟩ : TangentBundle (modelWithCornersSelf ℝ E) E)) := by
    apply contMDiff_vectorSpace_iff_contDiff.mpr
    simpa [Wc] using (contDiff_const : ContDiff ℝ ∞ (fun _ : E => w))
  have hV : MDifferentiableWithinAt (modelWithCornersSelf ℝ E)
      (modelWithCornersSelf ℝ E).tangent
      (fun y => (⟨y, Vc y⟩ : TangentBundle (modelWithCornersSelf ℝ E) E))
      chart.target (chart q) :=
    (Vc_smooth.mdifferentiable (by simp) (chart q)).mdifferentiableWithinAt
  have hW : MDifferentiableWithinAt (modelWithCornersSelf ℝ E)
      (modelWithCornersSelf ℝ E).tangent
      (fun y => (⟨y, Wc y⟩ : TangentBundle (modelWithCornersSelf ℝ E) E))
      chart.target (chart q) :=
    (Wc_smooth.mdifferentiable (by simp) (chart q)).mdifferentiableWithinAt
  have hnat := VectorField.mpullback_mlieBracketWithin
    (f := (chart : M → E)) (V := Vc) (W := Wc)
    (x₀ := q) (s := chart.source) (t := chart.target)
    hV hW (isOpen_extChartAt_source p).uniqueMDiffOn
    (contMDiffAt_extChartAt' (I := I) (x := p) (n := ∞) (by simpa [chart] using hq))
    (by simpa [chart] using hq) (by
      rw [minSmoothness_of_isRCLikeNormedField]
      exact (show (↑(2 : ℕ∞) : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞) from
        WithTop.coe_le_coe.mpr le_top))
    (Filter.mem_of_superset self_mem_nhdsWithin (fun z hz => chart.map_source hz))
  have coord_zero :
      VectorField.mlieBracketWithin (modelWithCornersSelf ℝ E) Vc Wc chart.target = 0 := by
    rw [VectorField.mlieBracketWithin_eq_lieBracketWithin]
    funext y
    simp [Vc, Wc, VectorField.lieBracketWithin]
    rfl
  rw [coord_zero, VectorField.mpullback_zero] at hnat
  simpa [chart, Vc, Wc] using hnat.symm

/-- The Cartan expression of a one-form is natural under an inverse extended chart at every
chart-target point where the coordinate one-form is differentiable within the chart target. -/
theorem ManifoldDifferentialForm.oneFormCartanExpressionCoordinates_inExtChartAt
    (coordinates : V ≃L[ℝ] W) (form : ManifoldDifferentialForm I M V 1)
    (p : M) (x : E) (hx : x ∈ (extChartAt I p).target) (v w : E)
    (hcoord : DifferentiableWithinAt ℝ
      (form.inExtChartAt coordinates 1 p) (extChartAt I p).target x) :
    form.oneFormCartanExpressionCoordinates coordinates (extChartAt I p).source
        ((extChartAt I p).symm x)
        (VectorField.mpullback I (modelWithCornersSelf ℝ E)
          (extChartAt I p) (fun _ => v))
        (VectorField.mpullback I (modelWithCornersSelf ℝ E)
          (extChartAt I p) (fun _ => w)) =
      ManifoldDifferentialForm.oneFormCartanExpressionCoordinates
        (I := modelWithCornersSelf ℝ E) (ContinuousLinearEquiv.refl ℝ W)
        (form.inExtChartAt coordinates 1 p).toManifoldForm
        (extChartAt I p).target x (fun _ => v) (fun _ => w) := by
  let q : M := (extChartAt I p).symm x
  have hq : q ∈ (extChartAt I p).source := (extChartAt I p).map_target hx
  have hchartq : (extChartAt I p) q = x := (extChartAt I p).right_inv hx
  rw [ManifoldDifferentialForm.oneFormCartanExpressionCoordinates_normedSpace]
  unfold ManifoldDifferentialForm.oneFormCartanExpressionCoordinates
  have first_derivative := oneForm_eval_mpullback_extChart_derivative_naturality_at_source
    coordinates form p q hq v w (by simpa only [hchartq] using hcoord)
  have second_derivative := oneForm_eval_mpullback_extChart_derivative_naturality_at_source
    coordinates form p q hq w v (by simpa only [hchartq] using hcoord)
  have bracket_zero :=
    ManifoldDifferentialForm.mlieBracketWithin_mpullback_extChart_const_const p q hq v w
  dsimp only [q] at first_derivative second_derivative bracket_zero
  rw [first_derivative, second_derivative, bracket_zero, hchartq]
  have intrinsic_zero : coordinates
      (form ((extChartAt I p).symm x) (fun _ => 0)) = 0 := by
    have tuple_zero : (fun _ : Fin 1 =>
        (0 : TangentSpace I ((extChartAt I p).symm x))) = 0 := rfl
    rw [tuple_zero]
    change coordinates
      ((form ((extChartAt I p).symm x)).toContinuousMultilinearMap 0) = 0
    rw [ContinuousMultilinearMap.map_zero, map_zero]
  have coordinate_bracket_zero :
      VectorField.lieBracketWithin ℝ (fun _ : E => v) (fun _ : E => w)
        (extChartAt I p).target x = 0 := by
    simp [VectorField.lieBracketWithin]
  rw [coordinate_bracket_zero]
  have coordinate_zero :
      (form.inExtChartAt coordinates 1 p x) (fun _ => 0) = 0 := by
    have tuple_zero : (fun _ : Fin 1 => (0 : E)) = 0 := rfl
    rw [tuple_zero]
    change (form.inExtChartAt coordinates 1 p x).toContinuousMultilinearMap 0 = 0
    rw [ContinuousMultilinearMap.map_zero]
  rw [intrinsic_zero, coordinate_zero]

end

end YangMills.Mathematics
