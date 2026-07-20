/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Geometry.PrincipalCurvatureNormedCoordinates
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension

/-!
# Inverse-chart regularity of principal connection coordinates

A principal connection already carries intrinsic smoothness tested against smooth manifold vector
fields. This module derives smoothness of its exact corner-aware inverse-extended-chart coordinate
one-form. Coordinate tangent vectors are pulled back to manifold vector fields with Mathlib's
`VectorField.mpullback`; the proof then reconstructs smoothness of the one-form-valued map from
fixed-vector evaluations in the finite-dimensional total-space model.

The result uses the same `mfderivWithin ... (Set.range IP)` transport as the committed coordinate
carrier. It introduces no coordinate-regularity witness and makes no exterior-derivative naturality
or Bianchi claim.
-/

namespace YangMills.Geometry

open Set Function
open scoped Manifold ContDiff
open YangMills.Mathematics

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
    {IB : ModelWithCorners ℝ EB HB}
    {IG : ModelWithCorners ℝ EG HG}
    {IP : ModelWithCorners ℝ EP HP}
    [ChartedSpace HB B] [IsManifold IB ∞ B]
    [ChartedSpace HG G] [LieGroup IG ∞ G]
    [ChartedSpace HP P] [IsManifold IP ∞ P]
    {torsor : PrincipalBundleTorsorData G B P}
    {bundle : TopologicalPrincipalBundleData torsor}
    {smoothBundle : SmoothPrincipalBundleData IB IG IP torsor bundle}
    [FiniteDimensional ℝ EP]

namespace PrincipalConnectionData

private theorem coordinate_eval_contDiffOn
    (connection : PrincipalConnectionData smoothBundle) (p : P) (v : EP) :
    ContDiffOn ℝ ∞ (fun x => connection.connectionCoordinatesInExtChartAt p x (fun _ => v))
      (extChartAt IP p).target := by
  let chart : PartialEquiv P EP := extChartAt IP p
  let coordinateField : EP → EP := fun _ => v
  let ambientField : (q : P) → TangentSpace IP q :=
    VectorField.mpullback IP (modelWithCornersSelf ℝ EP) chart coordinateField
  have coordinateField_smooth : ContMDiff (modelWithCornersSelf ℝ EP)
      ((modelWithCornersSelf ℝ EP).prod (modelWithCornersSelf ℝ EP)) ∞
      (fun x => (⟨x, coordinateField x⟩ : TangentBundle (modelWithCornersSelf ℝ EP) EP)) := by
    apply contMDiff_vectorSpace_iff_contDiff.mpr
    simpa [coordinateField] using
      (contDiff_const : ContDiff ℝ ∞ (fun _ : EP => v))
  have ambientField_smooth : ContMDiffOn IP IP.tangent ∞
      (fun q => (⟨q, ambientField q⟩ : TangentBundle IP P)) chart.source := by
    intro q hq
    simpa [ambientField, chart] using
      (ContMDiffAt.mpullback_vectorField_preimage
        coordinateField_smooth.contMDiffAt
        (contMDiffAt_extChartAt' (I := IP) (x := p) (n := ∞) (by simpa [chart] using hq))
        (isInvertible_mfderiv_extChartAt (I := IP) (x := p) (by simpa [chart] using hq))
        (by simp)).contMDiffWithinAt
  have evaluation_smooth : ContMDiffOn IP (modelWithCornersSelf ℝ EG) ∞
      (fun q => groupLieAlgebraModelEquiv IG
        (connection.pointwise.form q (fun _ => ambientField q))) chart.source :=
    connection.form_smooth chart.source (fun _ _ => ambientField _) (fun _ => ambientField_smooth)
  have composed_smooth : ContMDiffOn (modelWithCornersSelf ℝ EP)
      (modelWithCornersSelf ℝ EG) ∞
      ((fun q => groupLieAlgebraModelEquiv IG
        (connection.pointwise.form q (fun _ => ambientField q))) ∘ chart.symm) chart.target :=
    evaluation_smooth.comp (by simpa [chart] using
      (contMDiffOn_extChartAt_symm (I := IP) (n := ∞) p))
      (fun x hx => chart.map_target hx)
  apply (contMDiffOn_iff_contDiffOn.mp composed_smooth).congr
  intro x hx
  rw [PrincipalConnectionData.connectionCoordinatesInExtChartAt,
    ManifoldDifferentialForm.inExtChartAt_apply]
  change groupLieAlgebraModelEquiv IG
      (connection.pointwise.form (chart.symm x) (fun _ =>
        mfderivWithin (modelWithCornersSelf ℝ EP) IP chart.symm (range ⇑IP) x v)) =
    groupLieAlgebraModelEquiv IG
      (connection.pointwise.form (chart.symm x) (fun _ => ambientField (chart.symm x)))
  congr 3
  funext i
  change mfderivWithin (modelWithCornersSelf ℝ EP) IP chart.symm (range ⇑IP) x v =
    (mfderiv IP (modelWithCornersSelf ℝ EP) chart (chart.symm x)).inverse v
  have hinv :
      (mfderiv IP (modelWithCornersSelf ℝ EP) chart (chart.symm x)).inverse =
        mfderivWithin (modelWithCornersSelf ℝ EP) IP chart.symm (range ⇑IP) x :=
    ContinuousLinearMap.inverse_eq
      (mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm hx)
      (mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt hx)
  rw [hinv]
  rfl

/-- The exact inverse-chart connection one-form is smooth throughout the actual chart target. -/
theorem connectionCoordinatesInExtChartAt_contDiffOn
    (connection : PrincipalConnectionData smoothBundle) (p : P) :
    ContDiffOn ℝ ∞ (connection.connectionCoordinatesInExtChartAt p)
      (extChartAt IP p).target := by
  let e : (EP →L[ℝ] EG) ≃L[ℝ] ContinuousAlternatingMap ℝ EP EG (Fin 1) :=
    (ContinuousAlternatingMap.ofSubsingletonLIE (𝕜 := ℝ) (E := EP) (F := EG)
      (0 : Fin 1)).toContinuousLinearEquiv
  have hclm : ContDiffOn ℝ ∞
      (fun x => e.symm (connection.connectionCoordinatesInExtChartAt p x))
      (extChartAt IP p).target := by
    apply contDiffOn_clm_apply.mpr
    intro v
    have h := connection.coordinate_eval_contDiffOn p v
    simpa [e] using h
  have h := e.contDiff.comp_contDiffOn hclm
  simpa [Function.comp_def] using h

/-- Pointwise `C∞` regularity of the exact inverse-chart connection one-form follows from the
connection's stored intrinsic smoothness. -/
theorem connectionCoordinatesInExtChartAt_contDiffWithinAt
    (connection : PrincipalConnectionData smoothBundle) (p : P) (x : EP)
    (hx : x ∈ (extChartAt IP p).target) :
    ContDiffWithinAt ℝ ∞ (connection.connectionCoordinatesInExtChartAt p)
      (extChartAt IP p).target x :=
  connection.connectionCoordinatesInExtChartAt_contDiffOn p x hx

end PrincipalConnectionData

end

end YangMills.Geometry
