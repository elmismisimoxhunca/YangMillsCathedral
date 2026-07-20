/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Geometry.PrincipalConnectionLocalCurvatureCoherence

/-!
# Hostile probes for local curvature coherence
-/

namespace YangMills.Geometry.PrincipalConnectionLocalCurvatureCoherence.Probes

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
    [ChartedSpace HG G] [LieGroup IG ∞ G]
    [ChartedSpace HB B] [IsManifold IB ∞ B]
    [ChartedSpace HP P] [IsManifold IP ∞ P]
    {torsor : PrincipalBundleTorsorData G B P}
    {bundle : TopologicalPrincipalBundleData torsor}
    {smoothBundle : SmoothPrincipalBundleData IB IG IP torsor bundle}

omit [FiniteDimensional ℝ EB] in
/-- The exact descended curvature is the curvature of the same exact local potential. -/
theorem exact_local_curvature_coherence
    (connection : PrincipalConnectionData smoothBundle)
    (exterior : PrincipalConnectionExteriorDerivativeData connection)
    (certificate : PrincipalCurvatureStructureCertificate smoothBundle connection exterior)
    (chart : PrincipalBundleLocalTrivialization torsor)
    (chart_mem : chart ∈ bundle.trivializationAtlas) (b : B) :
    letI : CompleteSpace EG := FiniteDimensional.complete ℝ EG
    letI : ENat.LEInfty (minSmoothness ℝ 3) := by
      rw [minSmoothness_of_isRCLikeNormedField]
      infer_instance
    Set.EqOn (connection.localCurvatureInBaseExtChartAt exterior certificate chart b)
      (groupLieAlgebraCoordinateCurvatureWithin (I := IG) (G := G)
        (connection.localPotentialInBaseExtChartAt chart b)
        (AdjointBundle.DifferentialForm.baseExtChartDomain (IB := IB) chart b))
      (AdjointBundle.DifferentialForm.baseExtChartDomain (IB := IB) chart b) :=
  connection.localCurvatureInBaseExtChartAt_eqOn_coordinateCurvature
    exterior certificate chart chart_mem b

omit [FiniteDimensional ℝ EB] in
/-- A changed local curvature at an in-domain point contradicts exact same-potential coherence. -/
theorem mismatched_local_curvature_coherence_blocked
    (connection : PrincipalConnectionData smoothBundle)
    (exterior : PrincipalConnectionExteriorDerivativeData connection)
    (certificate : PrincipalCurvatureStructureCertificate smoothBundle connection exterior)
    (chart : PrincipalBundleLocalTrivialization torsor)
    (chart_mem : chart ∈ bundle.trivializationAtlas) (b : B)
    (x : EB)
    (hx : x ∈ AdjointBundle.DifferentialForm.baseExtChartDomain (IB := IB) chart b)
    (wrong :
      letI : CompleteSpace EG := FiniteDimensional.complete ℝ EG
      letI : ENat.LEInfty (minSmoothness ℝ 3) := by
        rw [minSmoothness_of_isRCLikeNormedField]
        infer_instance
      connection.localCurvatureInBaseExtChartAt exterior certificate chart b x ≠
        groupLieAlgebraCoordinateCurvatureWithin (I := IG) (G := G)
          (connection.localPotentialInBaseExtChartAt chart b)
          (AdjointBundle.DifferentialForm.baseExtChartDomain (IB := IB) chart b) x) : False :=
  wrong (connection.localCurvatureInBaseExtChartAt_eqOn_coordinateCurvature
    exterior certificate chart chart_mem b hx)

end

end YangMills.Geometry.PrincipalConnectionLocalCurvatureCoherence.Probes
