/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Geometry.AdjointBundleDifferentialFormBaseCoordinateSmooth
import YangMills.Geometry.PrincipalCurvatureSmoothDescent
import YangMills.Mathematics.NormedCoordinateBianchiWithin

/-!
# Exact local adjoint curvature calculus

For one designated principal chart and one base extended chart, this module packages the local
potential `A`, the exact smoothly descended curvature coordinate `F`, and the typed degree-three
expression `dF + [A ∧ F]` on their exact overlap. The potential `A` is the direct Lie-algebra
coordinate of the same connection at the designated local section and tangent lifts. The curvature
`F` retains the exact curvature certificate and dependent quotient fiber before applying its
coordinate. Both use the same corner-aware inverse-chart transport.

No vanishing, chart independence, or intrinsic positive-degree covariant derivative is claimed here.
-/

namespace YangMills.Geometry

open Set
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
    {smoothBundle : SmoothPrincipalBundleData IB IG IP torsor bundle}
    [FiniteDimensional ℝ EG]

namespace PrincipalConnectionData

/-- Base-model coordinate of the local gauge potential `A = s*Θ`, totalized by zero outside the
same exact base/principal-chart overlap used by adjoint-valued base coordinates. -/
noncomputable def localPotentialInBaseExtChartAt
    (connection : PrincipalConnectionData smoothBundle)
    (chart : PrincipalBundleLocalTrivialization torsor) (b : B) :
    NormedSpaceDifferentialForm EB EG 1 := fun x => by
  classical
  let q := (extChartAt IB b).symm x
  if hx : x ∈ AdjointBundle.DifferentialForm.baseExtChartDomain (IB := IB) chart b then
    exact (groupLieAlgebraModelEquiv IG).toContinuousLinearMap.compContinuousAlternatingMap
      ((connection.pointwise.form (principalBundleLocalSection chart q)).compContinuousLinearMap
        ((principalBundleLocalTangentLift (IB := IB) (IP := IP) chart q).comp
          (mfderivWithin (modelWithCornersSelf ℝ EB) IB (extChartAt IB b).symm
            (Set.range ⇑IB) x)))
  else exact 0

/-- The exact descended curvature `F`, in the already-defined base coordinate on that overlap. -/
noncomputable def localCurvatureInBaseExtChartAt
    (connection : PrincipalConnectionData smoothBundle)
    (exterior : PrincipalConnectionExteriorDerivativeData connection)
    (certificate : PrincipalCurvatureStructureCertificate smoothBundle connection exterior)
    (chart : PrincipalBundleLocalTrivialization torsor) (b : B) :
    NormedSpaceDifferentialForm EB EG 2 :=
  (connection.smoothBaseCurvature exterior certificate).toForm.inBaseExtChartAt chart b

/-- Honest local positive-degree expression `dF + [A ∧ F]`, with `extDerivWithin` taken on the
exact overlap and the same connection, curvature, and canonical transported Lie bracket. -/
noncomputable def localCurvatureCovariantExteriorExpression
    (connection : PrincipalConnectionData smoothBundle)
    (exterior : PrincipalConnectionExteriorDerivativeData connection)
    (certificate : PrincipalCurvatureStructureCertificate smoothBundle connection exterior)
    (chart : PrincipalBundleLocalTrivialization torsor) (b : B) :
    NormedSpaceDifferentialForm EB EG 3 := by
  letI : CompleteSpace EG := FiniteDimensional.complete ℝ EG
  letI : ENat.LEInfty (minSmoothness ℝ 3) := by
    rw [minSmoothness_of_isRCLikeNormedField]
    infer_instance
  exact groupLieAlgebraCoordinateCovariantExteriorDerivativeTwoWithin (I := IG) (G := G)
    (localPotentialInBaseExtChartAt connection chart b)
    (AdjointBundle.DifferentialForm.baseExtChartDomain (IB := IB) chart b)
    (localCurvatureInBaseExtChartAt connection exterior certificate chart b)

omit [FiniteDimensional ℝ EG] in
@[simp] theorem localPotentialInBaseExtChartAt_apply
    (connection : PrincipalConnectionData smoothBundle)
    (chart : PrincipalBundleLocalTrivialization torsor) (b : B)
    (x : EB)
    (hx : x ∈ AdjointBundle.DifferentialForm.baseExtChartDomain (IB := IB) chart b)
    (vectors : Fin 1 → EB) :
    localPotentialInBaseExtChartAt connection chart b x vectors =
      groupLieAlgebraModelEquiv IG
        (connection.pointwise.form
          (principalBundleLocalSection chart ((extChartAt IB b).symm x))
          (fun i => principalBundleLocalTangentLift (IB := IB) (IP := IP) chart
            ((extChartAt IB b).symm x)
            (mfderivWithin (modelWithCornersSelf ℝ EB) IB (extChartAt IB b).symm
              (Set.range ⇑IB) x (vectors i)))) := by
  simp only [localPotentialInBaseExtChartAt, dif_pos hx]
  rfl

/-- On the exact overlap, the base-coordinate curvature is the exact derived principal curvature
at the same chart's local section and the same transported/lifted base vectors. -/
@[simp] theorem localCurvatureInBaseExtChartAt_apply
    (connection : PrincipalConnectionData smoothBundle)
    (exterior : PrincipalConnectionExteriorDerivativeData connection)
    (certificate : PrincipalCurvatureStructureCertificate smoothBundle connection exterior)
    (chart : PrincipalBundleLocalTrivialization torsor)
    (chart_mem : chart ∈ bundle.trivializationAtlas)
    (b : B) (x : EB)
    (hx : x ∈ AdjointBundle.DifferentialForm.baseExtChartDomain (IB := IB) chart b)
    (vectors : Fin 2 → EB) :
    localCurvatureInBaseExtChartAt connection exterior certificate chart b x vectors =
      groupLieAlgebraModelEquiv IG
        ((connection.curvatureForm exterior).toForm
          (principalBundleLocalSection chart ((extChartAt IB b).symm x))
          (fun i => principalBundleLocalTangentLift (IB := IB) (IP := IP) chart
            ((extChartAt IB b).symm x)
            (mfderivWithin (modelWithCornersSelf ℝ EB) IB (extChartAt IB b).symm
              (Set.range ⇑IB) x (vectors i)))) := by
  unfold localCurvatureInBaseExtChartAt
  rw [AdjointBundle.DifferentialForm.inBaseExtChartAt_apply _ chart b x hx vectors]
  change AdjointBundle.DifferentialForm.inCoordinates
      (PrincipalTwoForm.selectedBaseForm (IB := IB) (bundle := bundle)
        (connection.curvatureForm exterior).toForm)
      chart hx.2
      (fun i => mfderivWithin (modelWithCornersSelf ℝ EB) IB
        (extChartAt IB b).symm (Set.range ⇑IB) x (vectors i)) = _
  exact PrincipalTwoForm.selectedBaseForm_inCoordinates smoothBundle
    (connection.curvatureForm exterior).toForm certificate.horizontal
    certificate.right_ad_equivariant chart chart_mem hx.2 _

/-- The local expression unfolds to precisely `extDerivWithin F + [A ∧ F]` on the declared
coordinate overlap; this theorem does not yet assert that the result vanishes. -/
theorem localCurvatureCovariantExteriorExpression_apply
    (connection : PrincipalConnectionData smoothBundle)
    (exterior : PrincipalConnectionExteriorDerivativeData connection)
    (certificate : PrincipalCurvatureStructureCertificate smoothBundle connection exterior)
    (chart : PrincipalBundleLocalTrivialization torsor) (b : B) (x : EB) :
    letI : CompleteSpace EG := FiniteDimensional.complete ℝ EG
    letI : ENat.LEInfty (minSmoothness ℝ 3) := by
      rw [minSmoothness_of_isRCLikeNormedField]
      infer_instance
    localCurvatureCovariantExteriorExpression connection exterior certificate chart b x =
      extDerivWithin (localCurvatureInBaseExtChartAt connection exterior certificate chart b)
          (AdjointBundle.DifferentialForm.baseExtChartDomain (IB := IB) chart b) x +
        (localPotentialInBaseExtChartAt connection chart b x).continuousBilinearWedgeOneMany
          (groupLieAlgebraCoordinateBracketCLM (I := IG) (G := G)) 2
          (localCurvatureInBaseExtChartAt connection exterior certificate chart b x) := by
  rfl

omit [FiniteDimensional ℝ EG] in
@[simp] theorem localPotentialInBaseExtChartAt_of_not_mem
    (connection : PrincipalConnectionData smoothBundle)
    (chart : PrincipalBundleLocalTrivialization torsor) (b : B)
    (x : EB)
    (hx : x ∉ AdjointBundle.DifferentialForm.baseExtChartDomain (IB := IB) chart b) :
    localPotentialInBaseExtChartAt connection chart b x = 0 := by
  simp [localPotentialInBaseExtChartAt, hx]

end PrincipalConnectionData

end
end YangMills.Geometry
