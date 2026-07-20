/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Geometry.PrincipalConnectionLocalAdjointCalculus

/-!
# Hostile probes for exact local adjoint curvature calculus
-/

namespace YangMills.Geometry.PrincipalConnectionLocalAdjointCalculus.Probes

open Set
open scoped Manifold ContDiff Bundle Topology
open YangMills.Mathematics

universe uEG uHG uEB uHB uEP uHP uG uB uP

noncomputable section

variable
    {EG : Type uEG} {HG : Type uHG}
    [NormedAddCommGroup EG] [NormedSpace ℝ EG] [FiniteDimensional ℝ EG] [TopologicalSpace HG]
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
    {smoothBundle : SmoothPrincipalBundleData IB IG IP torsor bundle}

omit [FiniteDimensional ℝ EG] in
/-- The local potential evaluates on the exact connection, section, lift, and tangent transport. -/
theorem exact_local_potential
    (connection : PrincipalConnectionData smoothBundle)
    (chart : PrincipalBundleLocalTrivialization torsor) (b : B)
    (x : EB)
    (hx : x ∈ AdjointBundle.DifferentialForm.baseExtChartDomain (IB := IB) chart b)
    (vectors : Fin 1 → EB) :
    connection.localPotentialInBaseExtChartAt chart b x vectors =
      groupLieAlgebraModelEquiv IG
        (connection.pointwise.form
          (principalBundleLocalSection chart ((extChartAt IB b).symm x))
          (fun i => principalBundleLocalTangentLift (IB := IB) (IP := IP) chart
            ((extChartAt IB b).symm x)
            (mfderivWithin (modelWithCornersSelf ℝ EB) IB (extChartAt IB b).symm
              (Set.range ⇑IB) x (vectors i)))) :=
  connection.localPotentialInBaseExtChartAt_apply chart b x hx vectors

omit [FiniteDimensional ℝ EG] in
/-- Outside the exact overlap, the local potential is exactly zero. -/
theorem exact_local_potential_outside_zero
    (connection : PrincipalConnectionData smoothBundle)
    (chart : PrincipalBundleLocalTrivialization torsor) (b : B) (x : EB)
    (hx : x ∉ AdjointBundle.DifferentialForm.baseExtChartDomain (IB := IB) chart b) :
    connection.localPotentialInBaseExtChartAt chart b x = 0 :=
  connection.localPotentialInBaseExtChartAt_of_not_mem chart b x hx

/-- The local curvature is the exact certified principal curvature on matching lifted arguments. -/
theorem exact_local_curvature
    (connection : PrincipalConnectionData smoothBundle)
    (exterior : PrincipalConnectionExteriorDerivativeData connection)
    (certificate : PrincipalCurvatureStructureCertificate smoothBundle connection exterior)
    (chart : PrincipalBundleLocalTrivialization torsor)
    (chart_mem : chart ∈ bundle.trivializationAtlas)
    (b : B) (x : EB)
    (hx : x ∈ AdjointBundle.DifferentialForm.baseExtChartDomain (IB := IB) chart b)
    (vectors : Fin 2 → EB) :
    connection.localCurvatureInBaseExtChartAt exterior certificate chart b x vectors =
      groupLieAlgebraModelEquiv IG
        ((connection.curvatureForm exterior).toForm
          (principalBundleLocalSection chart ((extChartAt IB b).symm x))
          (fun i => principalBundleLocalTangentLift (IB := IB) (IP := IP) chart
            ((extChartAt IB b).symm x)
            (mfderivWithin (modelWithCornersSelf ℝ EB) IB (extChartAt IB b).symm
              (Set.range ⇑IB) x (vectors i)))) :=
  connection.localCurvatureInBaseExtChartAt_apply exterior certificate chart chart_mem b x hx vectors

/-- A changed principal-curvature coordinate is rejected. -/
theorem mismatched_local_curvature_blocked
    (connection : PrincipalConnectionData smoothBundle)
    (exterior : PrincipalConnectionExteriorDerivativeData connection)
    (certificate : PrincipalCurvatureStructureCertificate smoothBundle connection exterior)
    (chart : PrincipalBundleLocalTrivialization torsor)
    (chart_mem : chart ∈ bundle.trivializationAtlas)
    (b : B) (x : EB)
    (hx : x ∈ AdjointBundle.DifferentialForm.baseExtChartDomain (IB := IB) chart b)
    (vectors : Fin 2 → EB)
    (wrong : connection.localCurvatureInBaseExtChartAt exterior certificate chart b x vectors ≠
      groupLieAlgebraModelEquiv IG
        ((connection.curvatureForm exterior).toForm
          (principalBundleLocalSection chart ((extChartAt IB b).symm x))
          (fun i => principalBundleLocalTangentLift (IB := IB) (IP := IP) chart
            ((extChartAt IB b).symm x)
            (mfderivWithin (modelWithCornersSelf ℝ EB) IB (extChartAt IB b).symm
              (Set.range ⇑IB) x (vectors i))))) : False :=
  wrong (connection.localCurvatureInBaseExtChartAt_apply
    exterior certificate chart chart_mem b x hx vectors)

/-- The degree-three carrier unfolds only to the exact `dF + [A∧F]` expression. -/
theorem exact_local_covariant_exterior_expression
    (connection : PrincipalConnectionData smoothBundle)
    (exterior : PrincipalConnectionExteriorDerivativeData connection)
    (certificate : PrincipalCurvatureStructureCertificate smoothBundle connection exterior)
    (chart : PrincipalBundleLocalTrivialization torsor) (b : B) (x : EB) :
    letI : CompleteSpace EG := FiniteDimensional.complete ℝ EG
    letI : ENat.LEInfty (minSmoothness ℝ 3) := by
      rw [minSmoothness_of_isRCLikeNormedField]
      infer_instance
    connection.localCurvatureCovariantExteriorExpression exterior certificate chart b x =
      extDerivWithin (connection.localCurvatureInBaseExtChartAt exterior certificate chart b)
          (AdjointBundle.DifferentialForm.baseExtChartDomain (IB := IB) chart b) x +
        (connection.localPotentialInBaseExtChartAt chart b x).continuousBilinearWedgeOneMany
          (groupLieAlgebraCoordinateBracketCLM (I := IG) (G := G)) 2
          (connection.localCurvatureInBaseExtChartAt exterior certificate chart b x) :=
  connection.localCurvatureCovariantExteriorExpression_apply exterior certificate chart b x

/-- An unrelated replacement for the exact local expression is rejected. -/
theorem mismatched_local_expression_blocked
    (connection : PrincipalConnectionData smoothBundle)
    (exterior : PrincipalConnectionExteriorDerivativeData connection)
    (certificate : PrincipalCurvatureStructureCertificate smoothBundle connection exterior)
    (chart : PrincipalBundleLocalTrivialization torsor) (b : B) (x : EB)
    (wrong :
      letI : CompleteSpace EG := FiniteDimensional.complete ℝ EG
      letI : ENat.LEInfty (minSmoothness ℝ 3) := by
        rw [minSmoothness_of_isRCLikeNormedField]
        infer_instance
      connection.localCurvatureCovariantExteriorExpression exterior certificate chart b x ≠
        extDerivWithin (connection.localCurvatureInBaseExtChartAt exterior certificate chart b)
            (AdjointBundle.DifferentialForm.baseExtChartDomain (IB := IB) chart b) x +
          (connection.localPotentialInBaseExtChartAt chart b x).continuousBilinearWedgeOneMany
            (groupLieAlgebraCoordinateBracketCLM (I := IG) (G := G)) 2
            (connection.localCurvatureInBaseExtChartAt exterior certificate chart b x)) : False :=
  wrong (connection.localCurvatureCovariantExteriorExpression_apply
    exterior certificate chart b x)

end

end YangMills.Geometry.PrincipalConnectionLocalAdjointCalculus.Probes
