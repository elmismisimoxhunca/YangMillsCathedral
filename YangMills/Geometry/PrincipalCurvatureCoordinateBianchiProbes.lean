/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Geometry.PrincipalCurvatureCoordinateBianchi

/-!
# Hostile probes for derived principal coordinate Bianchi

These probes expose the theorem without naturality or regularity premises and reject a nonzero
covariant exterior expression. No Bianchi datum is constructed.
-/

namespace YangMills.Geometry.PrincipalCurvatureCoordinateBianchi.Probes

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

/-- The same-connection coordinate Bianchi theorem requires only actual target membership. -/
theorem exact_unconditional_chart_bianchi
    (connection : PrincipalConnectionData smoothBundle)
    (exterior : PrincipalConnectionExteriorDerivativeData connection)
    (p : P) (x : EP) (mem : x ∈ (extChartAt IP p).target) :
    letI : CompleteSpace EG := FiniteDimensional.complete ℝ EG
    letI : ENat.LEInfty (minSmoothness ℝ 3) := by
      rw [minSmoothness_of_isRCLikeNormedField]
      infer_instance
    groupLieAlgebraCoordinateCovariantExteriorDerivativeTwoWithin (I := IG) (G := G)
      (connection.connectionCoordinatesInExtChartAt p) (extChartAt IP p).target
      (connection.curvatureCoordinatesInExtChartAt exterior p) x = 0 :=
  connection.curvatureCoordinatesInExtChartAt_coordinateBianchi_finiteDimensional
    exterior p x mem

/-- A nonzero output contradicts the theorem without supplying naturality, regularity, or Bianchi. -/
theorem nonzero_unconditional_chart_bianchi_blocked
    (connection : PrincipalConnectionData smoothBundle)
    (exterior : PrincipalConnectionExteriorDerivativeData connection)
    (p : P) (x : EP) (mem : x ∈ (extChartAt IP p).target)
    (nonzero :
      letI : CompleteSpace EG := FiniteDimensional.complete ℝ EG
      letI : ENat.LEInfty (minSmoothness ℝ 3) := by
        rw [minSmoothness_of_isRCLikeNormedField]
        infer_instance
      groupLieAlgebraCoordinateCovariantExteriorDerivativeTwoWithin (I := IG) (G := G)
        (connection.connectionCoordinatesInExtChartAt p) (extChartAt IP p).target
        (connection.curvatureCoordinatesInExtChartAt exterior p) x ≠ 0) : False :=
  nonzero (connection.curvatureCoordinatesInExtChartAt_coordinateBianchi_finiteDimensional
    exterior p x mem)

end

end YangMills.Geometry.PrincipalCurvatureCoordinateBianchi.Probes
