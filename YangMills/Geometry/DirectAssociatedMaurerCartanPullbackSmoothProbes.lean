/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Geometry.DirectAssociatedMaurerCartanPullbackSmooth

/-!
# Hostile probes for direct Maurer--Cartan pullback smoothness
-/

namespace YangMills.Geometry.DirectAssociatedMaurerCartanPullbackSmooth.Probes

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

/-- Smoothness is derived directly, with no `PrincipalConnectionData` argument. -/
theorem exact_connection_free_smoothness
    (gauge : SmoothGaugeTransformation smoothBundle) :
    gauge.associatedMaurerCartanPullback.IsSmooth (groupLieAlgebraModelEquiv IG) :=
  gauge.associatedMaurerCartanPullback_isSmooth

/-- The direct smooth package retains the exact raw Maurer--Cartan carrier. -/
theorem exact_direct_smooth_carrier
    (gauge : SmoothGaugeTransformation smoothBundle) :
    gauge.associatedMaurerCartanPullbackSmoothForm.toForm =
      gauge.associatedMaurerCartanPullback :=
  gauge.associatedMaurerCartanPullbackSmoothForm_toForm

/-- A nonsmoothness claim contradicts direct tangent-map regularity. -/
theorem nonsmooth_direct_pullback_blocked
    (gauge : SmoothGaugeTransformation smoothBundle)
    (wrong : ¬ gauge.associatedMaurerCartanPullback.IsSmooth
      (groupLieAlgebraModelEquiv IG)) : False :=
  wrong gauge.associatedMaurerCartanPullback_isSmooth

/-- Replacing the smooth package carrier is rejected. -/
theorem mismatched_direct_smooth_carrier_blocked
    (gauge : SmoothGaugeTransformation smoothBundle)
    (wrong : gauge.associatedMaurerCartanPullbackSmoothForm.toForm ≠
      gauge.associatedMaurerCartanPullback) : False :=
  wrong gauge.associatedMaurerCartanPullbackSmoothForm_toForm

end

end YangMills.Geometry.DirectAssociatedMaurerCartanPullbackSmooth.Probes
