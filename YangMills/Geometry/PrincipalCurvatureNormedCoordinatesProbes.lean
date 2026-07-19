/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Geometry.PrincipalCurvatureNormedCoordinates

/-! Hostile probes for exact same-connection principal-curvature coordinate carriers. -/

namespace YangMills.Geometry.PrincipalCurvatureNormedCoordinates.Probes

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
    [FiniteDimensional ℝ EG]

omit [FiniteDimensional ℝ EG] in
/-- The connection coordinate carrier is definitionally tied to the exact connection form. -/
theorem exact_connection_carrier
    (connection : PrincipalConnectionData smoothBundle)
    (map : EP → P) (source : Set EP) :
    connection.connectionCoordinatePullbackWithin map source =
      connection.pointwise.form.normedCoordinatePullbackWithinAlong
        (groupLieAlgebraModelEquiv IG) 1 map source := rfl

/-- The curvature coordinate carrier is definitionally the pullback of the derived curvature. -/
theorem exact_derived_curvature_carrier
    (connection : PrincipalConnectionData smoothBundle)
    (exterior : PrincipalConnectionExteriorDerivativeData connection)
    (map : EP → P) (source : Set EP) :
    connection.curvatureCoordinatePullbackWithin exterior map source =
      (connection.curvatureForm exterior).toForm.normedCoordinatePullbackWithinAlong
        (groupLieAlgebraModelEquiv IG) 2 map source := rfl

omit [FiniteDimensional ℝ EG] in
/-- The derivative carrier retains the exact certificate indexed by the same connection. -/
theorem exact_derivative_carrier
    (connection : PrincipalConnectionData smoothBundle)
    (exterior : PrincipalConnectionExteriorDerivativeData connection)
    (map : EP → P) (source : Set EP) :
    exterior.coordinatePullbackWithin map source =
      exterior.certificate.derivative.toForm.normedCoordinatePullbackWithinAlong
        (groupLieAlgebraModelEquiv IG) 2 map source := rfl

/-- The exact same-connection coordinate curvature equation is reusable. -/
theorem exact_coordinate_curvature_equation
    (connection : PrincipalConnectionData smoothBundle)
    (exterior : PrincipalConnectionExteriorDerivativeData connection)
    (map : EP → P) (source : Set EP) :
    letI : CompleteSpace EG := FiniteDimensional.complete ℝ EG
    letI : ENat.LEInfty (minSmoothness ℝ 3) := by
      rw [minSmoothness_of_isRCLikeNormedField]
      infer_instance
    connection.curvatureCoordinatePullbackWithin exterior map source = fun x =>
      exterior.coordinatePullbackWithin map source x + (1 / 2 : ℝ) •
        ContinuousAlternatingMap.continuousBilinearWedgeOneMany
          (groupLieAlgebraCoordinateBracketCLM (I := IG) (G := G)) 1
          (connection.connectionCoordinatePullbackWithin map source x)
          (connection.connectionCoordinatePullbackWithin map source x) :=
  connection.curvatureCoordinatePullbackWithin_eq exterior map source

/-- The corner-aware inverse-chart specialization retains the exact equation. -/
theorem exact_chart_curvature_equation
    (connection : PrincipalConnectionData smoothBundle)
    (exterior : PrincipalConnectionExteriorDerivativeData connection) (p : P) :
    letI : CompleteSpace EG := FiniteDimensional.complete ℝ EG
    letI : ENat.LEInfty (minSmoothness ℝ 3) := by
      rw [minSmoothness_of_isRCLikeNormedField]
      infer_instance
    connection.curvatureCoordinatesInExtChartAt exterior p = fun x =>
      exterior.coordinatesInExtChartAt p x + (1 / 2 : ℝ) •
        ContinuousAlternatingMap.continuousBilinearWedgeOneMany
          (groupLieAlgebraCoordinateBracketCLM (I := IG) (G := G)) 1
          (connection.connectionCoordinatesInExtChartAt p x)
          (connection.connectionCoordinatesInExtChartAt p x) :=
  connection.curvatureCoordinatesInExtChartAt_eq exterior p

/-- An unrelated two-form cannot replace the coordinate pullback of the derived curvature. -/
theorem unrelated_curvature_blocked
    (connection : PrincipalConnectionData smoothBundle)
    (exterior : PrincipalConnectionExteriorDerivativeData connection)
    (map : EP → P) (source : Set EP)
    (wrong : NormedSpaceDifferentialForm EP EG 2)
    (different : wrong ≠
      ManifoldDifferentialForm.normedCoordinatePullbackWithinAlong
        (groupLieAlgebraModelEquiv IG) 2 (connection.curvatureForm exterior).toForm map source)
    (claimed : connection.curvatureCoordinatePullbackWithin exterior map source = wrong) : False := by
  apply different
  rw [← claimed]
  rfl

omit [FiniteDimensional ℝ EG] in
/-- An unrelated derivative carrier cannot replace the exact connection-indexed certificate. -/
theorem unrelated_derivative_blocked
    (connection : PrincipalConnectionData smoothBundle)
    (exterior : PrincipalConnectionExteriorDerivativeData connection)
    (map : EP → P) (source : Set EP)
    (wrong : NormedSpaceDifferentialForm EP EG 2)
    (different : wrong ≠
      ManifoldDifferentialForm.normedCoordinatePullbackWithinAlong
        (groupLieAlgebraModelEquiv IG) 2 exterior.certificate.derivative.toForm map source)
    (claimed : exterior.coordinatePullbackWithin map source = wrong) : False := by
  apply different
  rw [← claimed]
  rfl

end

end YangMills.Geometry.PrincipalCurvatureNormedCoordinates.Probes
