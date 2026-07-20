/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Geometry.AdjointBundleDifferentialFormBaseCoordinateSmooth

/-!
# Hostile probes for smooth adjoint-form base coordinates
-/

namespace YangMills.Geometry.AdjointBundleDifferentialFormBaseCoordinateSmooth.Probes

open Set
open scoped Manifold ContDiff Bundle Topology
open YangMills.Mathematics

universe uEG uHG uEB uHB uEP uHP uG uB uP

noncomputable section

variable
    {EG : Type uEG} {HG : Type uHG}
    [NormedAddCommGroup EG] [NormedSpace ℝ EG] [TopologicalSpace HG]
    {EB : Type uEB} {HB : Type uHB}
    [NormedAddCommGroup EB] [NormedSpace ℝ EB] [FiniteDimensional ℝ EB] [TopologicalSpace HB]
    {EP : Type uEP} {HP : Type uHP}
    [NormedAddCommGroup EP] [NormedSpace ℝ EP] [TopologicalSpace HP]
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

/-- Every fixed tuple gives a smooth coordinate evaluation on the exact overlap. -/
theorem exact_tuple_coordinate_regularity
    {k : ℕ} (form : AdjointBundle.DifferentialForm.Smooth smoothBundle k)
    (chart : PrincipalBundleLocalTrivialization torsor)
    (chart_mem : chart ∈ bundle.trivializationAtlas) (b : B)
    (vectors : Fin k → EB) :
    ContDiffOn ℝ ∞ (fun x => form.toForm.inBaseExtChartAt chart b x vectors)
      (AdjointBundle.DifferentialForm.baseExtChartDomain (IB := IB) chart b) :=
  form.inBaseExtChartAt_apply_contDiffOn chart chart_mem b vectors

/-- The complete alternating-map-valued coordinate carrier is smooth within the exact overlap. -/
theorem exact_whole_coordinate_regularity
    {k : ℕ} (form : AdjointBundle.DifferentialForm.Smooth smoothBundle k)
    (chart : PrincipalBundleLocalTrivialization torsor)
    (chart_mem : chart ∈ bundle.trivializationAtlas) (b : B) :
    ContDiffOn ℝ ∞ (form.toForm.inBaseExtChartAt chart b)
      (AdjointBundle.DifferentialForm.baseExtChartDomain (IB := IB) chart b) :=
  form.inBaseExtChartAt_contDiffOn chart chart_mem b

/-- A nonsmooth substituted coordinate carrier contradicts exact smooth-form regularity. -/
theorem nonsmooth_coordinate_carrier_blocked
    {k : ℕ} (form : AdjointBundle.DifferentialForm.Smooth smoothBundle k)
    (chart : PrincipalBundleLocalTrivialization torsor)
    (chart_mem : chart ∈ bundle.trivializationAtlas) (b : B)
    (wrong : ¬ ContDiffOn ℝ ∞ (form.toForm.inBaseExtChartAt chart b)
      (AdjointBundle.DifferentialForm.baseExtChartDomain (IB := IB) chart b)) : False :=
  wrong (form.inBaseExtChartAt_contDiffOn chart chart_mem b)

/-- Pointwise regularity retains explicit membership in the meaningful overlap. -/
theorem exact_pointwise_coordinate_regularity
    {k : ℕ} (form : AdjointBundle.DifferentialForm.Smooth smoothBundle k)
    (chart : PrincipalBundleLocalTrivialization torsor)
    (chart_mem : chart ∈ bundle.trivializationAtlas) (b : B)
    (x : EB)
    (hx : x ∈ AdjointBundle.DifferentialForm.baseExtChartDomain (IB := IB) chart b) :
    ContDiffWithinAt ℝ ∞ (form.toForm.inBaseExtChartAt chart b)
      (AdjointBundle.DifferentialForm.baseExtChartDomain (IB := IB) chart b) x :=
  form.inBaseExtChartAt_contDiffWithinAt chart chart_mem b x hx

end

end YangMills.Geometry.AdjointBundleDifferentialFormBaseCoordinateSmooth.Probes
