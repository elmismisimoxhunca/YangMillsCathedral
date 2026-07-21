/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Geometry.PrincipalConnectionIntrinsicBianchiFiniteDimensional
import YangMills.Mathematics.PositiveDegreeCartanArbitraryFieldChartTransport
import YangMills.Mathematics.ManifoldOneFormExteriorDerivativeSmoothMapCoordinates

namespace YangMills.Geometry

open Set Function Filter
open scoped Manifold ContDiff Topology
open YangMills.Mathematics

universe uEG uHG uEB uHB uEP uHP uG uB uP

noncomputable section

variable
    {EG : Type uEG} {HG : Type uHG}
    [NormedAddCommGroup EG] [NormedSpace ℝ EG] [FiniteDimensional ℝ EG] [TopologicalSpace HG]
    {EB : Type uEB} {HB : Type uHB}
    [NormedAddCommGroup EB] [NormedSpace ℝ EB] [FiniteDimensional ℝ EB] [TopologicalSpace HB]
    {EP : Type uEP} {HP : Type uHP}
    [NormedAddCommGroup EP] [NormedSpace ℝ EP] [FiniteDimensional ℝ EP] [TopologicalSpace HP]
    {G : Type uG} {B : Type uB} {P : Type uP}
    [Group G] [TopologicalSpace G] [TopologicalSpace B] [TopologicalSpace P]
    [IsTopologicalGroup G]
    {IG : ModelWithCorners ℝ EG HG}
    {IB : ModelWithCorners ℝ EB HB}
    {IP : ModelWithCorners ℝ EP HP}
    [ChartedSpace HG G] [LieGroup IG ∞ G] [LieGroup IG (minSmoothness ℝ 3) G]
    [ChartedSpace HB B] [IsManifold IB ∞ B]
    [ChartedSpace HP P] [IsManifold IP ∞ P]
    [ENat.LEInfty (minSmoothness ℝ 3)]
    {torsor : PrincipalBundleTorsorData G B P}
    {bundle : TopologicalPrincipalBundleData torsor}
    {smoothBundle : SmoothPrincipalBundleData IB IG IP torsor bundle}

namespace PrincipalConnectionData

omit [FiniteDimensional ℝ EB] in
/-- The ordinary curvature exterior derivative, constructed from coordinate Bianchi rather than
assumed: `dF = -[A ∧ F]`. -/
noncomputable def curvatureExteriorCertificate_finiteDimensional
    (connection : PrincipalConnectionData smoothBundle)
    (exterior : PrincipalConnectionExteriorDerivativeData connection) :
    SmoothManifoldTwoFormExteriorDerivativeCertificate
      (groupLieAlgebraModelEquiv IG) (connection.curvatureForm exterior) where
  derivative := SmoothManifoldDifferentialForm.smul (-1 : ℝ)
    (PrincipalForm.covariantExteriorBracket connection 1 (connection.curvatureForm exterior))
  cartan_formula := by
    intro s p open_s mem_s unique_s fields fields_smooth
    let calculusSet : Set EP := (extChartAt IP p).symm ⁻¹' s ∩ Set.range ⇑IP
    let center : EP := (extChartAt IP p) p
    let coordinateFields : Fin 3 → EP → EP := fun i =>
      extChartCoordinateField IP p (fields i)
    let curvatureCoordinates : NormedSpaceDifferentialForm EP EG 2 :=
      connection.curvatureCoordinatesInExtChartAt exterior p
    let bracketCoordinates : EP → EP [⋀^Fin 3]→L[ℝ] EG := fun x =>
      ContinuousAlternatingMap.continuousBilinearWedgeOneMany
        (groupLieAlgebraCoordinateBracketCLM (I := IG) (G := G)) 2
        (connection.connectionCoordinatesInExtChartAt p x)
        (curvatureCoordinates x)
    have transport :=
      (connection.curvatureForm exterior).positiveDegreeCartanExpressionCoordinates_inExtChartAt_arbitraryFields
        (groupLieAlgebraModelEquiv IG) 1 s p mem_s fields fields_smooth
    have curvature_diff : DifferentiableWithinAt ℝ curvatureCoordinates calculusSet center := by
      exact ((connection.curvatureForm exterior).inExtChartAt_differentiableWithinAt_modelRange
        (groupLieAlgebraModelEquiv IG) 2 p).mono inter_subset_right
    have coordinateFields_diff : ∀ i,
        DifferentiableWithinAt ℝ (coordinateFields i) calculusSet center := by
      intro i
      exact extChartCoordinateField_differentiableWithinAt IP s p mem_s
        (fields i) (fields_smooth i)
    have unique_calculus : UniqueDiffWithinAt ℝ calculusSet center := by
      dsimp only [calculusSet, center]
      rw [inter_comm]
      apply unique_s.uniqueDiffWithinAt_range_inter p
      exact ⟨mem_extChartAt_target p, by simpa using mem_s⟩
    have ext_formula :=
      curvatureCoordinates.extDerivWithin_eq_positiveDegreeCartanExpression 1 calculusSet center
        coordinateFields curvature_diff coordinateFields_diff unique_calculus
    have calculus_germ : calculusSet =ᶠ[𝓝 center] (extChartAt IP p).target := by
      have h := centered_calculusSet_eventuallyEq_chartSafe
        (I := IP) (I' := IP) (fun x : P => x) contMDiff_id s p open_s mem_s
      have safe_eq : (extChartAt IP p).target ∩
          ((fun x : P => x) ∘ (extChartAt IP p).symm) ⁻¹'
            (extChartAt IP p).source = (extChartAt IP p).target := by
        ext x
        constructor
        · exact fun hx => hx.1
        · intro hx
          exact ⟨hx, (extChartAt IP p).map_target hx⟩
      rw [safe_eq] at h
      exact h
    have ext_germ : extDerivWithin curvatureCoordinates calculusSet center =
        extDerivWithin curvatureCoordinates (extChartAt IP p).target center :=
      extDerivWithin_congr_set_local curvatureCoordinates calculus_germ
    have bianchi := connection.curvatureCoordinatesInExtChartAt_coordinateBianchi_finiteDimensional
      exterior p center (mem_extChartAt_target p)
    have coordinate_bianchi :
        extDerivWithin curvatureCoordinates (extChartAt IP p).target center +
          bracketCoordinates center = 0 := by
      simpa only [groupLieAlgebraCoordinateCovariantExteriorDerivativeTwoWithin,
        curvatureCoordinates, bracketCoordinates] using bianchi
    have derivative_coordinate :
        extDerivWithin curvatureCoordinates calculusSet center = - bracketCoordinates center := by
      rw [ext_germ]
      exact eq_neg_of_add_eq_zero_left coordinate_bianchi
    have bracket_chart :=
      connection.pointwise.form.inExtChartAt_lieBracketWedgeOneMany
        (IG := IG) (G := G) 2 (connection.curvatureForm exterior).toForm p
    have fields_center : ∀ i, coordinateFields i center = fields i p := by
      intro i
      change (mfderivWithin (modelWithCornersSelf ℝ EP) IP (extChartAt IP p).symm
        (Set.range ⇑IP) ((extChartAt IP p) p)).inverse
          (fields i ((extChartAt IP p).symm ((extChartAt IP p) p))) = fields i p
      rw [extChartAt_to_inv]
      exact mfderivWithin_extChartAt_symm_inverse_apply (I := IP) (x := p) (fields i p)
    rw [transport]
    change _ = curvatureCoordinates.toManifoldForm.positiveDegreeCartanExpressionCoordinates
      (ContinuousLinearEquiv.refl ℝ EG) 1 calculusSet center coordinateFields
    rw [← ext_formula]
    rw [derivative_coordinate]
    change (groupLieAlgebraModelEquiv IG)
        ((((-1 : ℝ) •
          (PrincipalForm.covariantExteriorBracket connection 1
            (connection.curvatureForm exterior)).toForm) p)
          (fun i => fields i p)) = -bracketCoordinates center (fun i => coordinateFields i center)
    rw [Pi.smul_apply, ContinuousAlternatingMap.smul_apply, map_smul]
    change (-1 : ℝ) • (groupLieAlgebraModelEquiv IG)
        ((connection.pointwise.form.lieBracketWedgeOneMany 2
          (connection.curvatureForm exterior).toForm) p (fun i => fields i p)) = _
    have tuple_center : (fun i => fields i p) = (fun i => coordinateFields i center) := by
      funext i
      exact (fields_center i).symm
    rw [tuple_center]
    let bracketForm := connection.pointwise.form.lieBracketWedgeOneMany 2
      (connection.curvatureForm exterior).toForm
    have bracket_center :
        bracketForm.inExtChartAt (groupLieAlgebraModelEquiv IG) 3 p center
            (fun i => coordinateFields i center) =
          (groupLieAlgebraModelEquiv IG)
            (bracketForm p (fun i => coordinateFields i center)) := by
      dsimp only [center]
      rw [ManifoldDifferentialForm.inExtChartAt_center,
        mfderivWithin_range_extChartAt_symm]
      congr 3
    have bracket_chart_at := congrFun bracket_chart center
    have bracket_chart_eval := congrArg
      (fun form : EP [⋀^Fin 3]→L[ℝ] EG => form (fun i => coordinateFields i center))
      bracket_chart_at
    rw [neg_one_smul]
    change -(groupLieAlgebraModelEquiv IG)
      (bracketForm p (fun i => coordinateFields i center)) = _
    rw [← bracket_center, bracket_chart_eval]
    rfl

/-- Derived intrinsic `D_A F`, with both the curvature structure and ordinary curvature exterior
certificate constructed internally. Its public inputs are only the connection and its first
ordinary exterior data. -/
noncomputable def curvatureCovariantExteriorDerivative_derived
    (connection : PrincipalConnectionData smoothBundle)
    (exterior : PrincipalConnectionExteriorDerivativeData connection) :
    AdjointBundle.DifferentialForm.Smooth smoothBundle 3 :=
  connection.curvatureCovariantExteriorDerivative_finiteDimensional exterior
    (connection.curvatureExteriorCertificate_finiteDimensional exterior)

/-- Finite-dimensional intrinsic Bianchi identity with structure and curvature exterior certificates
derived internally, requiring only a connection and its first ordinary exterior data. -/
theorem curvatureCovariantExteriorDerivative_derived_eq_zero
    (connection : PrincipalConnectionData smoothBundle)
    (exterior : PrincipalConnectionExteriorDerivativeData connection) :
    connection.curvatureCovariantExteriorDerivative_derived exterior =
      AdjointBundle.DifferentialForm.Smooth.zero smoothBundle 3 :=
  connection.curvatureCovariantExteriorDerivative_finiteDimensional_eq_zero exterior
    (connection.curvatureExteriorCertificate_finiteDimensional exterior)

end PrincipalConnectionData

end
end YangMills.Geometry
