/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Geometry.PrincipalConnectionDescendedBianchiZero

/-!
# Hostile probes for the intrinsic zero Bianchi representative
-/

namespace YangMills.Geometry.PrincipalConnectionDescendedBianchiZero.Probes

open Set
open scoped Manifold ContDiff Bundle Topology
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
    {torsor : PrincipalBundleTorsorData G B P}
    {bundle : TopologicalPrincipalBundleData torsor}
    {smoothBundle : SmoothPrincipalBundleData IB IG IP torsor bundle}

/-- The exact local expression is represented by one intrinsic smooth dependent-fiber zero form. -/
theorem exact_zero_descended_coordinate
    (connection : PrincipalConnectionData smoothBundle)
    (exterior : PrincipalConnectionExteriorDerivativeData connection)
    (certificate : PrincipalCurvatureStructureCertificate smoothBundle connection exterior)
    (chart : PrincipalBundleLocalTrivialization torsor)
    (chart_mem : chart ∈ bundle.trivializationAtlas) (b : B) :
    Set.EqOn
      (connection.localCurvatureCovariantExteriorExpression exterior certificate chart b)
      ((AdjointBundle.DifferentialForm.Smooth.zero smoothBundle 3).toForm.inBaseExtChartAt chart b)
      (AdjointBundle.DifferentialForm.baseExtChartDomain (IB := IB) chart b) :=
  connection.localCurvatureCovariantExteriorExpression_eq_zeroDescendedCoordinate
    exterior certificate chart chart_mem b

/-- A changed intrinsic coordinate at an admitted point contradicts the derived bridge. -/
theorem mismatched_zero_descended_coordinate_blocked
    (connection : PrincipalConnectionData smoothBundle)
    (exterior : PrincipalConnectionExteriorDerivativeData connection)
    (certificate : PrincipalCurvatureStructureCertificate smoothBundle connection exterior)
    (chart : PrincipalBundleLocalTrivialization torsor)
    (chart_mem : chart ∈ bundle.trivializationAtlas) (b : B)
    (x : EB)
    (hx : x ∈ AdjointBundle.DifferentialForm.baseExtChartDomain (IB := IB) chart b)
    (wrong : connection.localCurvatureCovariantExteriorExpression exterior certificate chart b x ≠
      (AdjointBundle.DifferentialForm.Smooth.zero smoothBundle 3).toForm.inBaseExtChartAt chart b x) :
    False :=
  wrong (connection.localCurvatureCovariantExteriorExpression_eq_zeroDescendedCoordinate
    exterior certificate chart chart_mem b hx)

omit [FiniteDimensional ℝ EG] [FiniteDimensional ℝ EB] [FiniteDimensional ℝ EP]
    [LieGroup IG (minSmoothness ℝ 3) G] in
/-- The intrinsic coordinate used by the bridge cannot be nonzero on its exact domain. -/
theorem nonzero_descended_coordinate_blocked
    (chart : PrincipalBundleLocalTrivialization torsor) (b : B) (x : EB)
    (hx : x ∈ AdjointBundle.DifferentialForm.baseExtChartDomain (IB := IB) chart b)
    (wrong :
      (AdjointBundle.DifferentialForm.Smooth.zero smoothBundle 3).toForm.inBaseExtChartAt chart b x ≠
        0) : False := by
  apply wrong
  exact AdjointBundle.DifferentialForm.inBaseExtChartAt_zero
    (bundle := bundle) 3 chart b hx

end

end YangMills.Geometry.PrincipalConnectionDescendedBianchiZero.Probes
