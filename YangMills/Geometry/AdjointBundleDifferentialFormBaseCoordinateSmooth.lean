/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Geometry.AdjointBundleDifferentialFormBaseCoordinates
import YangMills.Mathematics.ContinuousAlternatingMapSmoothEvaluation
import Mathlib.Geometry.Manifold.VectorField.Pullback

/-!
# Smooth base coordinates of adjoint-bundle-valued forms

For a smooth adjoint-bundle-valued form, its fixed-model base extended-chart coordinates are smooth
within the exact overlap with every designated principal atlas chart. No smoothness is claimed
across the boundary where the total carrier is zero-extended.
-/

namespace YangMills.Geometry

open Set Function
open scoped Manifold ContDiff Bundle Topology
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
    {IG : ModelWithCorners ℝ EG HG}
    {IB : ModelWithCorners ℝ EB HB}
    {IP : ModelWithCorners ℝ EP HP}
    [ChartedSpace HG G] [LieGroup IG ∞ G]
    [ChartedSpace HB B] [IsManifold IB ∞ B]
    [ChartedSpace HP P] [IsManifold IP ∞ P]
    {torsor : PrincipalBundleTorsorData G B P}
    {bundle : TopologicalPrincipalBundleData torsor}

namespace AdjointBundle.DifferentialForm.Smooth

/-- Fixed-tuple evaluation of base extended-chart coordinates of a smooth adjoint-valued form is
smooth on the exact overlap. -/
theorem inBaseExtChartAt_apply_contDiffOn
    [FiniteDimensional ℝ EB]
    {smoothBundle : SmoothPrincipalBundleData IB IG IP torsor bundle}
    {k : ℕ} (form : AdjointBundle.DifferentialForm.Smooth smoothBundle k)
    (chart : PrincipalBundleLocalTrivialization torsor)
    (chart_mem : chart ∈ bundle.trivializationAtlas) (b : B)
    (vectors : Fin k → EB) :
    ContDiffOn ℝ ∞
      (fun x => form.toForm.inBaseExtChartAt chart b x vectors)
      (AdjointBundle.DifferentialForm.baseExtChartDomain (IB := IB) chart b) := by
  let baseChart : PartialEquiv B EB := extChartAt IB b
  let fields : Fin k → (q : B) → TangentSpace IB q := fun i =>
    VectorField.mpullback IB (modelWithCornersSelf ℝ EB) baseChart (fun _ => vectors i)
  have coordinateFieldSmooth : ∀ i, ContMDiffOn IB (IB.prod 𝓘(ℝ, EB)) ∞
      (fun q => (⟨q, fields i q⟩ : TangentBundle IB B)) baseChart.source := by
    intro i q hq
    have constantSmooth : ContMDiff (modelWithCornersSelf ℝ EB)
        ((modelWithCornersSelf ℝ EB).prod (modelWithCornersSelf ℝ EB)) ∞
        (fun y => (⟨y, vectors i⟩ : TangentBundle (modelWithCornersSelf ℝ EB) EB)) := by
      apply contMDiff_vectorSpace_iff_contDiff.mpr
      simpa using (contDiff_const : ContDiff ℝ ∞ (fun _ : EB => vectors i))
    simpa [fields, baseChart] using
      (ContMDiffAt.mpullback_vectorField_preimage
        constantSmooth.contMDiffAt
        (contMDiffAt_extChartAt' (I := IB) (x := b) (n := ∞) (by simpa [baseChart] using hq))
        (isInvertible_mfderiv_extChartAt (I := IB) (x := b) (by simpa [baseChart] using hq))
        (by simp)).contMDiffWithinAt
  let s : Set B := baseChart.source ∩ chart.baseSet
  have evaluatedSmooth : ContMDiffOn IB 𝓘(ℝ, EG) ∞
      (AdjointBundle.DifferentialForm.coordinateEvaluation form.toForm chart fields) s :=
    form.smooth chart chart_mem s fields inter_subset_right
      (fun i => (coordinateFieldSmooth i).mono inter_subset_left)
  have inverseMaps : Set.MapsTo baseChart.symm
      (AdjointBundle.DifferentialForm.baseExtChartDomain (IB := IB) chart b) s := by
    intro x hx
    exact ⟨baseChart.map_target hx.1, hx.2⟩
  have composedSmooth : ContMDiffOn (modelWithCornersSelf ℝ EB) 𝓘(ℝ, EG) ∞
      (fun x => AdjointBundle.DifferentialForm.coordinateEvaluation
        form.toForm chart fields (baseChart.symm x))
      (AdjointBundle.DifferentialForm.baseExtChartDomain (IB := IB) chart b) := by
    apply evaluatedSmooth.comp
      ((contMDiffOn_extChartAt_symm b).mono inter_subset_left)
      inverseMaps
  apply composedSmooth.contDiffOn.congr
  intro x hx
  rw [AdjointBundle.DifferentialForm.inBaseExtChartAt_apply form.toForm chart b x hx vectors]
  rw [AdjointBundle.DifferentialForm.coordinateEvaluation_eq_inCoordinates
    form.toForm chart fields hx.2]
  rw [AdjointBundle.DifferentialForm.inCoordinates_apply]
  congr 2
  funext i
  have tangent_inverse :
      (mfderiv IB (modelWithCornersSelf ℝ EB) baseChart (baseChart.symm x)).inverse =
        mfderivWithin (modelWithCornersSelf ℝ EB) IB baseChart.symm (Set.range ⇑IB) x :=
    ContinuousLinearMap.inverse_eq
      (mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm hx.1)
      (mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt hx.1)
  change
    (mfderivWithin (modelWithCornersSelf ℝ EB) IB baseChart.symm (Set.range ⇑IB) x)
        (vectors i) =
      (mfderiv IB (modelWithCornersSelf ℝ EB) baseChart (baseChart.symm x)).inverse
        (vectors i)
  exact congrArg (fun L => L (vectors i)) tangent_inverse.symm


/-- The whole fixed-model base coordinate form of a smooth adjoint-valued form is smooth on the
exact overlap. -/
theorem inBaseExtChartAt_contDiffOn
    [FiniteDimensional ℝ EB]
    {smoothBundle : SmoothPrincipalBundleData IB IG IP torsor bundle}
    {k : ℕ} (form : AdjointBundle.DifferentialForm.Smooth smoothBundle k)
    (chart : PrincipalBundleLocalTrivialization torsor)
    (chart_mem : chart ∈ bundle.trivializationAtlas) (b : B) :
    ContDiffOn ℝ ∞
      (form.toForm.inBaseExtChartAt chart b)
      (AdjointBundle.DifferentialForm.baseExtChartDomain (IB := IB) chart b) := by
  apply contDiffOn_continuousAlternatingMap_of_apply
  exact fun vectors => form.inBaseExtChartAt_apply_contDiffOn chart chart_mem b vectors


/-- Pointwise form of `inBaseExtChartAt_contDiffOn`. -/
theorem inBaseExtChartAt_contDiffWithinAt
    [FiniteDimensional ℝ EB]
    {smoothBundle : SmoothPrincipalBundleData IB IG IP torsor bundle}
    {k : ℕ} (form : AdjointBundle.DifferentialForm.Smooth smoothBundle k)
    (chart : PrincipalBundleLocalTrivialization torsor)
    (chart_mem : chart ∈ bundle.trivializationAtlas) (b : B)
    (x : EB)
    (hx : x ∈ AdjointBundle.DifferentialForm.baseExtChartDomain (IB := IB) chart b) :
    ContDiffWithinAt ℝ ∞ (form.toForm.inBaseExtChartAt chart b)
      (AdjointBundle.DifferentialForm.baseExtChartDomain (IB := IB) chart b) x :=
  form.inBaseExtChartAt_contDiffOn chart chart_mem b x hx

end AdjointBundle.DifferentialForm.Smooth
end
end YangMills.Geometry
