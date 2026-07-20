/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Geometry.PrincipalConnectionLocalBianchi

/-!
# Intrinsic zero representative of the local Bianchi result

Every designated-atlas-chart local `dF + [A ∧ F]` expression is identified, throughout its meaningful overlap, with
the corresponding base-chart coordinate of the existing intrinsic smooth zero adjoint-bundle-valued
three-form. This connects the local calculus to an actual dependent-fiber global carrier.

This result-specific zero bridge does not construct a positive-degree covariant exterior derivative
or prove transformation laws for a possibly nonzero output.
-/

namespace YangMills.Geometry

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

namespace PrincipalConnectionData

/-- Every designated-atlas-chart local Bianchi expression is the coordinate of the canonical intrinsic smooth zero
adjoint-valued three-form on the exact overlap. -/
theorem localCurvatureCovariantExteriorExpression_eq_zeroDescendedCoordinate
    (connection : PrincipalConnectionData smoothBundle)
    (exterior : PrincipalConnectionExteriorDerivativeData connection)
    (certificate : PrincipalCurvatureStructureCertificate smoothBundle connection exterior)
    (chart : PrincipalBundleLocalTrivialization torsor)
    (chart_mem : chart ∈ bundle.trivializationAtlas)
    (b : B) :
    Set.EqOn
      (connection.localCurvatureCovariantExteriorExpression exterior certificate chart b)
      ((AdjointBundle.DifferentialForm.Smooth.zero smoothBundle 3).toForm.inBaseExtChartAt chart b)
      (AdjointBundle.DifferentialForm.baseExtChartDomain (IB := IB) chart b) := by
  intro x hx
  rw [connection.localCurvatureCovariantExteriorExpression_eq_zero
    exterior certificate chart chart_mem b x hx]
  symm
  exact AdjointBundle.DifferentialForm.inBaseExtChartAt_zero
    (bundle := bundle) 3 chart b hx

end PrincipalConnectionData

end
end YangMills.Geometry
