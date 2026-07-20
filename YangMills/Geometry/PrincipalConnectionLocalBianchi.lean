/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Geometry.PrincipalConnectionLocalCurvatureCoherence

/-!
# Exact-overlap local Bianchi identity

The exact local potential is proved smooth on the base/principal-chart overlap, whose unique differentiability and closure-of-interior conditions are derived. Together with the proved
same-potential curvature coherence, the normed-coordinate Bianchi theorem makes the exact local
`dF + [A ∧ F]` expression vanish. This remains a chart-local coordinate theorem, not an intrinsic
positive-degree adjoint-bundle covariant derivative.
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
    [LieGroup IG (minSmoothness ℝ 3) G]
    [ChartedSpace HB B] [IsManifold IB ∞ B]
    [ChartedSpace HP P] [IsManifold IP ∞ P]
    {torsor : PrincipalBundleTorsorData G B P}
    {bundle : TopologicalPrincipalBundleData torsor}
    {smoothBundle : SmoothPrincipalBundleData IB IG IP torsor bundle}
    [FiniteDimensional ℝ EG] [FiniteDimensional ℝ EB] [FiniteDimensional ℝ EP]

namespace AdjointBundle.DifferentialForm

omit [IsTopologicalGroup G] [FiniteDimensional ℝ EB] in
/-- The exact overlap has unique derivatives. -/
theorem baseExtChartDomain_uniqueDiffOn
    (chart : PrincipalBundleLocalTrivialization torsor) (b : B) :
    UniqueDiffOn ℝ (baseExtChartDomain (IB := IB) chart b) := by
  change UniqueDiffOn ℝ
    ((extChartAt IB b).target ∩ (extChartAt IB b).symm ⁻¹' chart.baseSet)
  exact chart.isOpen_baseSet.uniqueMDiffOn.uniqueDiffOn_target_inter (I := IB) b

omit [IsTopologicalGroup G] [IsManifold IB ∞ B] [FiniteDimensional ℝ EB] in
/-- Every point of the exact overlap is in the closure of its interior. -/
theorem baseExtChartDomain_subset_closure_interior
    (chart : PrincipalBundleLocalTrivialization torsor) (b : B) {x : EB}
    (hx : x ∈ baseExtChartDomain (IB := IB) chart b) :
    x ∈ closure (interior (baseExtChartDomain (IB := IB) chart b)) := by
  have hqInterior : (extChartAt IB b).symm x ∈ interior chart.baseSet :=
    mem_interior_iff_mem_nhds.mpr (chart.isOpen_baseSet.mem_nhds hx.2)
  have hqClosure : (extChartAt IB b).symm x ∈ closure (interior chart.baseSet) :=
    subset_closure hqInterior
  have h := extChartAt_mem_closure_interior (I := IB) (x₀ := b)
    hqClosure ((extChartAt IB b).map_target hx.1)
  rw [(extChartAt IB b).right_inv hx.1] at h
  change x ∈ closure (interior
    ((extChartAt IB b).target ∩ (extChartAt IB b).symm ⁻¹' chart.baseSet))
  simpa only [inter_comm] using h

end AdjointBundle.DifferentialForm

namespace PrincipalConnectionData

omit [LieGroup IG (minSmoothness ℝ 3) G] [FiniteDimensional ℝ EG]
    [FiniteDimensional ℝ EP] in
private theorem localPotential_eval_contDiffOn
    (connection : PrincipalConnectionData smoothBundle)
    (chart : PrincipalBundleLocalTrivialization torsor)
    (chart_mem : chart ∈ bundle.trivializationAtlas) (b : B) (v : EB) :
    ContDiffOn ℝ ∞
      (fun x => connection.localPotentialInBaseExtChartAt chart b x (fun _ => v))
      (AdjointBundle.DifferentialForm.baseExtChartDomain (IB := IB) chart b) := by
  let baseChart : PartialEquiv B EB := extChartAt IB b
  let field : (q : B) → TangentSpace IB q :=
    VectorField.mpullback IB (modelWithCornersSelf ℝ EB) baseChart (fun _ => v)
  have fieldSmooth : ContMDiffOn IB (IB.prod 𝓘(ℝ, EB)) ∞
      (fun q => (⟨q, field q⟩ : TangentBundle IB B)) baseChart.source := by
    intro q hq
    have constantSmooth : ContMDiff (modelWithCornersSelf ℝ EB)
        ((modelWithCornersSelf ℝ EB).prod (modelWithCornersSelf ℝ EB)) ∞
        (fun y => (⟨y, v⟩ : TangentBundle (modelWithCornersSelf ℝ EB) EB)) := by
      apply contMDiff_vectorSpace_iff_contDiff.mpr
      simpa using (contDiff_const : ContDiff ℝ ∞ (fun _ : EB => v))
    simpa [field, baseChart] using
      (ContMDiffAt.mpullback_vectorField_preimage
        constantSmooth.contMDiffAt
        (contMDiffAt_extChartAt' (I := IB) (x := b) (n := ∞)
          (by simpa [baseChart] using hq))
        (isInvertible_mfderiv_extChartAt (I := IB) (x := b)
          (by simpa [baseChart] using hq))
        (by simp)).contMDiffWithinAt
  let s : Set B := baseChart.source ∩ chart.baseSet
  have evaluatedSmooth : ContMDiffOn IB 𝓘(ℝ, EG) ∞
      (fun q => groupLieAlgebraModelEquiv IG
        (connection.pointwise.form (principalBundleLocalSection chart q)
          (fun _ => principalBundleLocalTangentLift (IB := IB) (IP := IP)
            chart q (field q)))) s :=
    principalBundleLocalTangentLift_formEvaluation_contMDiffOn
      (groupLieAlgebraModelEquiv IG) connection.pointwise.form connection.form_smooth
      smoothBundle chart chart_mem inter_subset_right (fun _ q => field q)
      (fun _ => fieldSmooth.mono inter_subset_left)
  have inverseMaps : Set.MapsTo baseChart.symm
      (AdjointBundle.DifferentialForm.baseExtChartDomain (IB := IB) chart b) s := by
    intro x hx
    exact ⟨baseChart.map_target hx.1, hx.2⟩
  have composedSmooth : ContMDiffOn (modelWithCornersSelf ℝ EB) 𝓘(ℝ, EG) ∞
      (fun x => groupLieAlgebraModelEquiv IG
        (connection.pointwise.form (principalBundleLocalSection chart (baseChart.symm x))
          (fun _ => principalBundleLocalTangentLift (IB := IB) (IP := IP)
            chart (baseChart.symm x) (field (baseChart.symm x)))))
      (AdjointBundle.DifferentialForm.baseExtChartDomain (IB := IB) chart b) := by
    apply evaluatedSmooth.comp
      ((contMDiffOn_extChartAt_symm b).mono inter_subset_left)
      inverseMaps
  apply composedSmooth.contDiffOn.congr
  intro x hx
  rw [connection.localPotentialInBaseExtChartAt_apply chart b x hx (fun _ => v)]
  congr 3
  funext i
  have tangent_inverse :
      (mfderiv IB (modelWithCornersSelf ℝ EB) baseChart (baseChart.symm x)).inverse =
        mfderivWithin (modelWithCornersSelf ℝ EB) IB baseChart.symm (Set.range ⇑IB) x :=
    ContinuousLinearMap.inverse_eq
      (mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm hx.1)
      (mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt hx.1)
  congr 1
  exact congrArg (fun L => L v) tangent_inverse.symm

omit [LieGroup IG (minSmoothness ℝ 3) G] [FiniteDimensional ℝ EG]
    [FiniteDimensional ℝ EP] in
/-- The exact local potential is smooth on the exact overlap. -/
theorem localPotentialInBaseExtChartAt_contDiffOn
    (connection : PrincipalConnectionData smoothBundle)
    (chart : PrincipalBundleLocalTrivialization torsor)
    (chart_mem : chart ∈ bundle.trivializationAtlas) (b : B) :
    ContDiffOn ℝ ∞ (connection.localPotentialInBaseExtChartAt chart b)
      (AdjointBundle.DifferentialForm.baseExtChartDomain (IB := IB) chart b) := by
  let e : (EB →L[ℝ] EG) ≃L[ℝ] ContinuousAlternatingMap ℝ EB EG (Fin 1) :=
    (ContinuousAlternatingMap.ofSubsingletonLIE (𝕜 := ℝ) (E := EB) (F := EG)
      (0 : Fin 1)).toContinuousLinearEquiv
  have hclm : ContDiffOn ℝ ∞
      (fun x => e.symm (connection.localPotentialInBaseExtChartAt chart b x))
      (AdjointBundle.DifferentialForm.baseExtChartDomain (IB := IB) chart b) := by
    apply contDiffOn_clm_apply.mpr
    intro v
    simpa [e] using connection.localPotential_eval_contDiffOn chart chart_mem b v
  have h := e.contDiff.comp_contDiffOn hclm
  simpa [Function.comp_def] using h

omit [LieGroup IG (minSmoothness ℝ 3) G] [FiniteDimensional ℝ EG]
    [FiniteDimensional ℝ EP] in
/-- Pointwise regularity needed by within-coordinate Bianchi. -/
theorem localPotentialInBaseExtChartAt_contDiffWithinAt
    (connection : PrincipalConnectionData smoothBundle)
    (chart : PrincipalBundleLocalTrivialization torsor)
    (chart_mem : chart ∈ bundle.trivializationAtlas) (b : B) (x : EB)
    (hx : x ∈ AdjointBundle.DifferentialForm.baseExtChartDomain (IB := IB) chart b) :
    ContDiffWithinAt ℝ ∞ (connection.localPotentialInBaseExtChartAt chart b)
      (AdjointBundle.DifferentialForm.baseExtChartDomain (IB := IB) chart b) x :=
  connection.localPotentialInBaseExtChartAt_contDiffOn chart chart_mem b x hx

/-- The exact local same-chain expression satisfies Bianchi at every point of the exact
overlap. -/
theorem localCurvatureCovariantExteriorExpression_eq_zero
    (connection : PrincipalConnectionData smoothBundle)
    (exterior : PrincipalConnectionExteriorDerivativeData connection)
    (certificate : PrincipalCurvatureStructureCertificate smoothBundle connection exterior)
    (chart : PrincipalBundleLocalTrivialization torsor)
    (chart_mem : chart ∈ bundle.trivializationAtlas)
    (b : B) (x : EB)
    (hx : x ∈ AdjointBundle.DifferentialForm.baseExtChartDomain (IB := IB) chart b) :
    connection.localCurvatureCovariantExteriorExpression exterior certificate chart b x = 0 := by
  letI : CompleteSpace EG := FiniteDimensional.complete ℝ EG
  letI : ENat.LEInfty (minSmoothness ℝ 3) := by
    rw [minSmoothness_of_isRCLikeNormedField]
    infer_instance
  let s := AdjointBundle.DifferentialForm.baseExtChartDomain (IB := IB) chart b
  let A := connection.localPotentialInBaseExtChartAt chart b
  let F := connection.localCurvatureInBaseExtChartAt exterior certificate chart b
  let curvature := groupLieAlgebraCoordinateCurvatureWithin (I := IG) (G := G) A s
  have curvature_eq : Set.EqOn F curvature s :=
    connection.localCurvatureInBaseExtChartAt_eqOn_coordinateCurvature
      exterior certificate chart chart_mem b
  have derivative_eq : extDerivWithin F s x = extDerivWithin curvature s x :=
    extDerivWithin_congr' curvature_eq hx
  have bianchi := groupLieAlgebraCoordinate_bianchiWithin
    (I := IG) (G := G) A s x
    ((connection.localPotentialInBaseExtChartAt_contDiffWithinAt chart chart_mem b x hx).of_le
      (show (↑(2 : ℕ∞) : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞) from WithTop.coe_le_coe.mpr le_top))
    (by rw [minSmoothness_of_isRCLikeNormedField]; norm_num)
    (AdjointBundle.DifferentialForm.baseExtChartDomain_uniqueDiffOn chart b)
    (AdjointBundle.DifferentialForm.baseExtChartDomain_subset_closure_interior chart b hx) hx
  change groupLieAlgebraCoordinateCovariantExteriorDerivativeTwoWithin
    (I := IG) (G := G) A s F x = 0
  change extDerivWithin F s x +
    (A x).continuousBilinearWedgeOneMany
      (groupLieAlgebraCoordinateBracketCLM (I := IG) (G := G)) 2 (F x) = 0
  rw [derivative_eq, show F x = curvature x from curvature_eq hx]
  exact bianchi

end PrincipalConnectionData

end
end YangMills.Geometry
