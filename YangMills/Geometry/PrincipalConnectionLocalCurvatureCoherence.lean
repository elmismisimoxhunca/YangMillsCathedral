/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Geometry.PrincipalConnectionLocalExteriorNaturality

/-!
# Local curvature coherence

On the exact base/principal-chart overlap, the coordinate of the smoothly descended certified
curvature is proved equal to the coordinate curvature constructed from the same local potential.
The derivative term is supplied by the derived local-section exterior-naturality theorem; bracket
coherence is transported through the canonical Lie-algebra model equivalence.
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
    [FiniteDimensional ℝ EG] [FiniteDimensional ℝ EB] [FiniteDimensional ℝ EP]

namespace PrincipalConnectionData

omit [FiniteDimensional ℝ EB] in
set_option backward.isDefEq.respectTransparency false in
/-- The exact descended curvature coordinate equals the coordinate curvature of the exact local
potential on the exact overlap. -/
theorem localCurvatureInBaseExtChartAt_eqOn_coordinateCurvature
    (connection : PrincipalConnectionData smoothBundle)
    (exterior : PrincipalConnectionExteriorDerivativeData connection)
    (certificate : PrincipalCurvatureStructureCertificate smoothBundle connection exterior)
    (chart : PrincipalBundleLocalTrivialization torsor)
    (chart_mem : chart ∈ bundle.trivializationAtlas)
    (b : B) :
    letI : CompleteSpace EG := FiniteDimensional.complete ℝ EG
    letI : ENat.LEInfty (minSmoothness ℝ 3) := by
      rw [minSmoothness_of_isRCLikeNormedField]
      infer_instance
    Set.EqOn (connection.localCurvatureInBaseExtChartAt exterior certificate chart b)
      (groupLieAlgebraCoordinateCurvatureWithin (I := IG) (G := G)
        (connection.localPotentialInBaseExtChartAt chart b)
        (AdjointBundle.DifferentialForm.baseExtChartDomain (IB := IB) chart b))
      (AdjointBundle.DifferentialForm.baseExtChartDomain (IB := IB) chart b) := by
  letI : CompleteSpace EG := FiniteDimensional.complete ℝ EG
  letI : ENat.LEInfty (minSmoothness ℝ 3) := by
    rw [minSmoothness_of_isRCLikeNormedField]
    infer_instance
  intro x hx
  apply ContinuousAlternatingMap.ext
  intro vectors
  rw [connection.localCurvatureInBaseExtChartAt_apply
    exterior certificate chart chart_mem b x hx vectors]
  rw [connection.curvatureForm_toForm exterior]
  unfold groupLieAlgebraCoordinateCurvatureWithin
  rw [← connection.localExteriorDerivativeInBaseExtChartAt_eqOn_extDerivWithin
    exterior chart chart_mem b hx]
  let q := (extChartAt IB b).symm x
  let L := (principalBundleLocalTangentLift (IB := IB) (IP := IP) chart q).comp
    (mfderivWithin (modelWithCornersSelf ℝ EB) IB (extChartAt IB b).symm
      (Set.range ⇑IB) x)
  let alphaAt :=
    (connection.pointwise.form (principalBundleLocalSection chart q)).compContinuousLinearMap L
  have hA : connection.localPotentialInBaseExtChartAt chart b x =
      (groupLieAlgebraModelEquiv IG).toContinuousLinearMap.compContinuousAlternatingMap alphaAt := by
    apply ContinuousAlternatingMap.ext
    intro oneVectors
    rw [connection.localPotentialInBaseExtChartAt_apply chart b x hx oneVectors]
    rfl
  have hwedge := groupLieAlgebraCoordinateBracket_wedge_coherence
    (I := IG) (G := G) 1 alphaAt alphaAt
  rw [ContinuousAlternatingMap.lieBracketWedgeOneMany_one] at hwedge
  simp only [Pi.add_apply, Pi.smul_apply, ContinuousAlternatingMap.add_apply,
    ContinuousAlternatingMap.smul_apply]
  rw [map_add, map_smul]
  rw [connection.localExteriorDerivativeInBaseExtChartAt_apply
    exterior chart b x hx vectors]
  congr 1
  rw [hA]
  apply congrArg (fun z : EG => (1 / 2 : ℝ) • z)
  change groupLieAlgebraModelEquiv IG ((alphaAt.lieBracketWedgeOne alphaAt) vectors) = _
  exact congrArg (fun form : EB [⋀^Fin 2]→L[ℝ] EG => form vectors) hwedge

end PrincipalConnectionData

end
end YangMills.Geometry
