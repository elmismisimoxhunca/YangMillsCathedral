/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Geometry.PrincipalCurvatureSmoothDescentBianchiBridge

/-!
# Hostile probes for the smooth-descent/principal-Bianchi bridge

These probes lock the descended coordinate to the same principal curvature and reject a nonzero
coordinate Bianchi output. They do not claim an intrinsic adjoint-bundle three-form.
-/

namespace YangMills.Geometry.PrincipalCurvatureSmoothDescentBianchiBridge.Probes

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

variable
    (connection : PrincipalConnectionData smoothBundle)
    (exterior : PrincipalConnectionExteriorDerivativeData connection)
    (certificate : PrincipalCurvatureStructureCertificate smoothBundle connection exterior)
    (chart : PrincipalBundleLocalTrivialization torsor)
    (chart_mem : chart ∈ bundle.trivializationAtlas)
    {b : B} (hb : b ∈ chart.baseSet)
    (v : Fin 2 → TangentSpace IB b)

include certificate chart_mem hb v

/-- The bridge exposes both exact descent coordinates and same-representative coordinate Bianchi. -/
theorem exact_descended_coordinate_and_principal_bianchi :
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
          (principalBundleLocalSection chart b)) x = 0 :=
  connection.smoothBaseCurvature_chartwiseBianchiBridge_finiteDimensional
    exterior certificate chart chart_mem hb v

/-- An unrelated descended coordinate cannot replace the exact selected principal representative. -/
theorem mismatched_descended_coordinate_blocked
    (different :
      AdjointBundle.DifferentialForm.inCoordinates
          (connection.smoothBaseCurvature exterior certificate).toForm chart hb v ≠
        groupLieAlgebraModelEquiv IG
          ((connection.curvatureForm exterior).toForm
            (principalBundleLocalSection chart b)
            (fun i => principalBundleLocalTangentLift (IB := IB) (IP := IP)
              chart b (v i)))) : False :=
  different (connection.smoothBaseCurvature_chartwiseBianchiBridge_finiteDimensional
    exterior certificate chart chart_mem hb v).1

/-- A nonzero principal-representative Bianchi output contradicts the same chartwise bridge. -/
theorem nonzero_principal_representative_bianchi_blocked
    (x : EP) (hx : x ∈ (extChartAt IP (principalBundleLocalSection chart b)).target)
    (nonzero :
      letI : CompleteSpace EG := FiniteDimensional.complete ℝ EG
      letI : ENat.LEInfty (minSmoothness ℝ 3) := by
        rw [minSmoothness_of_isRCLikeNormedField]
        infer_instance
      groupLieAlgebraCoordinateCovariantExteriorDerivativeTwoWithin (I := IG) (G := G)
        (connection.connectionCoordinatesInExtChartAt
          (principalBundleLocalSection chart b))
        (extChartAt IP (principalBundleLocalSection chart b)).target
        (connection.curvatureCoordinatesInExtChartAt exterior
          (principalBundleLocalSection chart b)) x ≠ 0) : False :=
  nonzero ((connection.smoothBaseCurvature_chartwiseBianchiBridge_finiteDimensional
    exterior certificate chart chart_mem hb v).2 x hx)

end

end YangMills.Geometry.PrincipalCurvatureSmoothDescentBianchiBridge.Probes
