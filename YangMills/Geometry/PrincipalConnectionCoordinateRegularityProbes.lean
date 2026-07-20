/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Geometry.PrincipalConnectionCoordinateRegularity

/-!
# Hostile probes for principal connection coordinate regularity

The probes expose target-wide and pointwise `C∞` regularity of the exact corner-aware coordinate
carrier derived from the same principal connection. No coordinate regularity witness is supplied.
-/

namespace YangMills.Geometry.PrincipalConnectionCoordinateRegularity.Probes

open Set
open scoped Manifold ContDiff

universe uEG uHG uEB uHB uEP uHP uG uB uP

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
    [FiniteDimensional ℝ EP]

/-- Intrinsic smoothness controls the exact whole one-form-valued coordinate carrier. -/
theorem exact_chart_connection_regular
    (connection : PrincipalConnectionData smoothBundle) (p : P) :
    ContDiffOn ℝ ∞ (connection.connectionCoordinatesInExtChartAt p)
      (extChartAt IP p).target :=
  connection.connectionCoordinatesInExtChartAt_contDiffOn p

/-- Pointwise regularity remains attached to actual chart-target membership. -/
theorem exact_chart_connection_regular_on_target
    (connection : PrincipalConnectionData smoothBundle) (p : P) (x : EP)
    (hx : x ∈ (extChartAt IP p).target) :
    ContDiffWithinAt ℝ ∞ (connection.connectionCoordinatesInExtChartAt p)
      (extChartAt IP p).target x :=
  connection.connectionCoordinatesInExtChartAt_contDiffWithinAt p x hx

/-- A claim that the exact chart-coordinate connection is nonsmooth contradicts intrinsic
connection smoothness; no unrelated coordinate carrier can replace it. -/
theorem nonsmooth_exact_chart_coordinates_blocked
    (connection : PrincipalConnectionData smoothBundle) (p : P)
    (nonsmooth : ¬ ContDiffOn ℝ ∞ (connection.connectionCoordinatesInExtChartAt p)
      (extChartAt IP p).target) : False :=
  nonsmooth (connection.connectionCoordinatesInExtChartAt_contDiffOn p)

end YangMills.Geometry.PrincipalConnectionCoordinateRegularity.Probes
