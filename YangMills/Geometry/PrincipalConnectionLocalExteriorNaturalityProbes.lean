/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Geometry.PrincipalConnectionLocalExteriorNaturality

/-!
# Hostile probes for local-section exterior naturality
-/

namespace YangMills.Geometry.PrincipalConnectionLocalExteriorNaturality.Probes

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

omit [FiniteDimensional ℝ EG] [FiniteDimensional ℝ EB] [FiniteDimensional ℝ EP] in
/-- The derivative carrier remains tied to the exact certificate, section, lifts, and tangent map. -/
theorem exact_local_exterior_carrier
    (connection : PrincipalConnectionData smoothBundle)
    (exterior : PrincipalConnectionExteriorDerivativeData connection)
    (chart : PrincipalBundleLocalTrivialization torsor) (b : B)
    (x : EB)
    (hx : x ∈ AdjointBundle.DifferentialForm.baseExtChartDomain (IB := IB) chart b)
    (vectors : Fin 2 → EB) :
    connection.localExteriorDerivativeInBaseExtChartAt exterior chart b x vectors =
      groupLieAlgebraModelEquiv IG
        (exterior.certificate.derivative.toForm
          (principalBundleLocalSection chart ((extChartAt IB b).symm x))
          (fun i => principalBundleLocalTangentLift (IB := IB) (IP := IP) chart
            ((extChartAt IB b).symm x)
            (mfderivWithin (modelWithCornersSelf ℝ EB) IB (extChartAt IB b).symm
              (Set.range ⇑IB) x (vectors i)))) :=
  connection.localExteriorDerivativeInBaseExtChartAt_apply exterior chart b x hx vectors

omit [FiniteDimensional ℝ EG] [FiniteDimensional ℝ EB] [FiniteDimensional ℝ EP] in
/-- Outside the exact overlap, no geometric derivative value is smuggled through totalization. -/
theorem exact_local_exterior_outside_zero
    (connection : PrincipalConnectionData smoothBundle)
    (exterior : PrincipalConnectionExteriorDerivativeData connection)
    (chart : PrincipalBundleLocalTrivialization torsor) (b : B) (x : EB)
    (hx : x ∉ AdjointBundle.DifferentialForm.baseExtChartDomain (IB := IB) chart b) :
    connection.localExteriorDerivativeInBaseExtChartAt exterior chart b x = 0 :=
  connection.localExteriorDerivativeInBaseExtChartAt_of_not_mem exterior chart b x hx

omit [FiniteDimensional ℝ EG] [FiniteDimensional ℝ EB] in
/-- Local-section pullback commutes with the certified exterior derivative on the exact fixed set. -/
theorem exact_local_exterior_naturality
    (connection : PrincipalConnectionData smoothBundle)
    (exterior : PrincipalConnectionExteriorDerivativeData connection)
    (chart : PrincipalBundleLocalTrivialization torsor)
    (chart_mem : chart ∈ bundle.trivializationAtlas) (b : B) :
    Set.EqOn
      (connection.localExteriorDerivativeInBaseExtChartAt exterior chart b)
      (extDerivWithin (connection.localPotentialInBaseExtChartAt chart b)
        (AdjointBundle.DifferentialForm.baseExtChartDomain (IB := IB) chart b))
      (AdjointBundle.DifferentialForm.baseExtChartDomain (IB := IB) chart b) :=
  connection.localExteriorDerivativeInBaseExtChartAt_eqOn_extDerivWithin
    exterior chart chart_mem b

omit [FiniteDimensional ℝ EG] [FiniteDimensional ℝ EB] in
/-- Any changed local derivative contradicts the derived exact-set naturality theorem. -/
theorem mismatched_local_exterior_naturality_blocked
    (connection : PrincipalConnectionData smoothBundle)
    (exterior : PrincipalConnectionExteriorDerivativeData connection)
    (chart : PrincipalBundleLocalTrivialization torsor)
    (chart_mem : chart ∈ bundle.trivializationAtlas) (b : B)
    (x : EB)
    (hx : x ∈ AdjointBundle.DifferentialForm.baseExtChartDomain (IB := IB) chart b)
    (wrong : connection.localExteriorDerivativeInBaseExtChartAt exterior chart b x ≠
      extDerivWithin (connection.localPotentialInBaseExtChartAt chart b)
        (AdjointBundle.DifferentialForm.baseExtChartDomain (IB := IB) chart b) x) : False :=
  wrong (connection.localExteriorDerivativeInBaseExtChartAt_eqOn_extDerivWithin
    exterior chart chart_mem b hx)

end

end YangMills.Geometry.PrincipalConnectionLocalExteriorNaturality.Probes
