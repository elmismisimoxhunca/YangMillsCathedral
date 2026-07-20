/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Geometry.PrincipalCurvatureCoordinateBianchi
import YangMills.Geometry.PrincipalCurvatureSmoothDescent

/-!
# Chartwise Bianchi bridge for smoothly descended curvature

The exact principal curvature has two already-derived consequences: its horizontal/right-adjoint-
equivariant representative descends to a smooth adjoint-bundle-valued two-form, and its
finite-dimensional inverse-chart coordinate covariant derivative vanishes. This module joins those
facts through the same connection, exterior certificate, structure certificate, local section, and
tangent lifts.

The result is deliberately a chartwise principal-representative bridge. It does not invent a global
positive-degree adjoint-bundle covariant exterior derivative or call the coordinate expression an
intrinsic adjoint-valued three-form.
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

/-- The exact smooth descended curvature has its expected coordinate in every designated principal
chart, while the same principal representative obeys derived coordinate Bianchi throughout the
inverse extended chart centered at that chart's local section.

The second conjunct remains a principal total-space coordinate statement because no intrinsic
positive-degree adjoint-bundle covariant exterior derivative is yet available. -/
theorem smoothBaseCurvature_chartwiseBianchiBridge_finiteDimensional
    (connection : PrincipalConnectionData smoothBundle)
    (exterior : PrincipalConnectionExteriorDerivativeData connection)
    (certificate :
      PrincipalCurvatureStructureCertificate smoothBundle connection exterior)
    (chart : PrincipalBundleLocalTrivialization torsor)
    (chart_mem : chart ∈ bundle.trivializationAtlas)
    {b : B} (hb : b ∈ chart.baseSet)
    (v : Fin 2 → TangentSpace IB b) :
    AdjointBundle.DifferentialForm.inCoordinates
        (connection.smoothBaseCurvature exterior certificate).toForm chart hb v =
      groupLieAlgebraModelEquiv IG
        ((connection.curvatureForm exterior).toForm
          (principalBundleLocalSection chart b)
          (fun i => principalBundleLocalTangentLift (IB := IB) (IP := IP)
            chart b (v i))) ∧
    ∀ x : EP,
      x ∈ (extChartAt IP (principalBundleLocalSection chart b)).target →
      letI : CompleteSpace EG := FiniteDimensional.complete ℝ EG
      letI : ENat.LEInfty (minSmoothness ℝ 3) := by
        rw [minSmoothness_of_isRCLikeNormedField]
        infer_instance
      groupLieAlgebraCoordinateCovariantExteriorDerivativeTwoWithin (I := IG) (G := G)
        (connection.connectionCoordinatesInExtChartAt
          (principalBundleLocalSection chart b))
        (extChartAt IP (principalBundleLocalSection chart b)).target
        (connection.curvatureCoordinatesInExtChartAt exterior
          (principalBundleLocalSection chart b)) x = 0 := by
  constructor
  · change AdjointBundle.DifferentialForm.inCoordinates
        (PrincipalTwoForm.selectedBaseForm (IB := IB) (bundle := bundle)
          (connection.curvatureForm exterior).toForm) chart hb v = _
    exact PrincipalTwoForm.selectedBaseForm_inCoordinates smoothBundle
      (connection.curvatureForm exterior).toForm
      certificate.horizontal certificate.right_ad_equivariant chart chart_mem hb v
  · intro x hx
    exact connection.curvatureCoordinatesInExtChartAt_coordinateBianchi_finiteDimensional
      exterior (principalBundleLocalSection chart b) x hx

end PrincipalConnectionData

end

end YangMills.Geometry
