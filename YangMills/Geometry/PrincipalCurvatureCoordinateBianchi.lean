/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Geometry.PrincipalConnectionCoordinateExteriorNaturality

/-!
# Derived principal-curvature Bianchi identity in inverse charts

For finite-dimensional principal total-space models, intrinsic connection smoothness derives
coordinate regularity and generic Cartan transport derives exterior naturality. Combining those
results with the existing within-coordinate Bianchi theorem leaves only actual chart-target
membership. No Bianchi, regularity, or naturality witness is accepted.
-/

namespace YangMills.Geometry

open Set
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
    [FiniteDimensional ℝ EG] [FiniteDimensional ℝ EP]

namespace PrincipalConnectionData

/-- The exact derived principal curvature satisfies the coordinate Bianchi identity at every point
of every inverse extended-chart target. Exterior naturality and regularity are both derived. -/
theorem curvatureCoordinatesInExtChartAt_coordinateBianchi_finiteDimensional
    (connection : PrincipalConnectionData smoothBundle)
    (exterior : PrincipalConnectionExteriorDerivativeData connection)
    (p : P) (x : EP) (mem_target : x ∈ (extChartAt IP p).target) :
    letI : CompleteSpace EG := FiniteDimensional.complete ℝ EG
    letI : ENat.LEInfty (minSmoothness ℝ 3) := by
      rw [minSmoothness_of_isRCLikeNormedField]
      infer_instance
    groupLieAlgebraCoordinateCovariantExteriorDerivativeTwoWithin (I := IG) (G := G)
      (connection.connectionCoordinatesInExtChartAt p) (extChartAt IP p).target
      (connection.curvatureCoordinatesInExtChartAt exterior p) x = 0 :=
  connection.curvatureCoordinatesInExtChartAt_coordinateBianchi_of_finiteDimensional exterior
    p x (exterior.isNaturalInExtChartAt p) mem_target

end PrincipalConnectionData

end

end YangMills.Geometry
