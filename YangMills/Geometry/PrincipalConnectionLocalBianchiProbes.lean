/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Geometry.PrincipalConnectionLocalBianchi

/-!
# Hostile probes for exact-overlap local Bianchi
-/

namespace YangMills.Geometry.PrincipalConnectionLocalBianchi.Probes

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

omit [IsTopologicalGroup G] [FiniteDimensional ℝ EB] in
/-- The calculus domain has genuine unique derivatives. -/
theorem exact_domain_uniqueDiff
    (chart : PrincipalBundleLocalTrivialization torsor) (b : B) :
    UniqueDiffOn ℝ (AdjointBundle.DifferentialForm.baseExtChartDomain (IB := IB) chart b) :=
  AdjointBundle.DifferentialForm.baseExtChartDomain_uniqueDiffOn chart b

omit [IsTopologicalGroup G] [IsManifold IB ∞ B] [FiniteDimensional ℝ EB] in
/-- Every admitted point satisfies the exact closure-of-interior condition. -/
theorem exact_domain_closure_interior
    (chart : PrincipalBundleLocalTrivialization torsor) (b : B) (x : EB)
    (hx : x ∈ AdjointBundle.DifferentialForm.baseExtChartDomain (IB := IB) chart b) :
    x ∈ closure (interior
      (AdjointBundle.DifferentialForm.baseExtChartDomain (IB := IB) chart b)) :=
  AdjointBundle.DifferentialForm.baseExtChartDomain_subset_closure_interior chart b hx

omit [FiniteDimensional ℝ EG] [FiniteDimensional ℝ EP]
    [LieGroup IG (minSmoothness ℝ 3) G] in
/-- The exact local potential has the required full within-overlap regularity. -/
theorem exact_local_potential_regularity
    (connection : PrincipalConnectionData smoothBundle)
    (chart : PrincipalBundleLocalTrivialization torsor)
    (chart_mem : chart ∈ bundle.trivializationAtlas) (b : B) :
    ContDiffOn ℝ ∞ (connection.localPotentialInBaseExtChartAt chart b)
      (AdjointBundle.DifferentialForm.baseExtChartDomain (IB := IB) chart b) :=
  connection.localPotentialInBaseExtChartAt_contDiffOn chart chart_mem b

/-- The exact same-chain local `dF + [A∧F]` expression vanishes on the overlap. -/
theorem exact_local_bianchi
    (connection : PrincipalConnectionData smoothBundle)
    (exterior : PrincipalConnectionExteriorDerivativeData connection)
    (certificate : PrincipalCurvatureStructureCertificate smoothBundle connection exterior)
    (chart : PrincipalBundleLocalTrivialization torsor)
    (chart_mem : chart ∈ bundle.trivializationAtlas)
    (b : B) (x : EB)
    (hx : x ∈ AdjointBundle.DifferentialForm.baseExtChartDomain (IB := IB) chart b) :
    connection.localCurvatureCovariantExteriorExpression exterior certificate chart b x = 0 :=
  connection.localCurvatureCovariantExteriorExpression_eq_zero
    exterior certificate chart chart_mem b x hx

/-- A nonzero substituted Bianchi expression contradicts the derived theorem. -/
theorem nonzero_local_bianchi_blocked
    (connection : PrincipalConnectionData smoothBundle)
    (exterior : PrincipalConnectionExteriorDerivativeData connection)
    (certificate : PrincipalCurvatureStructureCertificate smoothBundle connection exterior)
    (chart : PrincipalBundleLocalTrivialization torsor)
    (chart_mem : chart ∈ bundle.trivializationAtlas)
    (b : B) (x : EB)
    (hx : x ∈ AdjointBundle.DifferentialForm.baseExtChartDomain (IB := IB) chart b)
    (wrong : connection.localCurvatureCovariantExteriorExpression
      exterior certificate chart b x ≠ 0) : False :=
  wrong (connection.localCurvatureCovariantExteriorExpression_eq_zero
    exterior certificate chart chart_mem b x hx)

end

end YangMills.Geometry.PrincipalConnectionLocalBianchi.Probes
