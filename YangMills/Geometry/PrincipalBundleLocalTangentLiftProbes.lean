/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Geometry.PrincipalBundleLocalTangentLift

/-!
# Hostile probes for principal local sections and tangent lifts
-/

namespace YangMills.Geometry.Probes

open Set
open scoped Manifold ContDiff

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
    {IG : ModelWithCorners ℝ EG HG}
    {IB : ModelWithCorners ℝ EB HB}
    {IP : ModelWithCorners ℝ EP HP}
    [ChartedSpace HG G] [LieGroup IG ∞ G]
    [ChartedSpace HB B] [IsManifold IB ∞ B]
    [ChartedSpace HP P] [IsManifold IP ∞ P]
    {torsor : PrincipalBundleTorsorData G B P}
    {bundle : TopologicalPrincipalBundleData torsor}
    (smoothBundle : SmoothPrincipalBundleData IB IG IP torsor bundle)

omit [IsTopologicalGroup G] in
/-- The designated local section cannot move the base point on its chart domain. -/
theorem base_moving_principalBundle_localSection_blocked
    (chart : PrincipalBundleLocalTrivialization torsor)
    {b : B} (hb : b ∈ chart.baseSet)
    (mismatch : torsor.projection (principalBundleLocalSection chart b) ≠ b) : False :=
  mismatch (principalBundleLocalSection_projection chart hb)

/-- An atlas local section cannot be nonsmooth on its exact chart domain. -/
theorem nonsmooth_principalBundle_localSection_blocked
    (smoothBundle : SmoothPrincipalBundleData IB IG IP torsor bundle)
    (chart : PrincipalBundleLocalTrivialization torsor)
    (chart_mem : chart ∈ bundle.trivializationAtlas)
    (failure : ¬ContMDiffOn IB IP ∞
      (principalBundleLocalSection chart) chart.baseSet) : False :=
  failure (principalBundleLocalSection_contMDiffOn smoothBundle chart chart_mem)

/-- The local tangent lift cannot fail to recover the input tangent vector after projection. -/
theorem disconnected_principalBundle_localTangentLift_blocked
    (smoothBundle : SmoothPrincipalBundleData IB IG IP torsor bundle)
    (chart : PrincipalBundleLocalTrivialization torsor)
    (chart_mem : chart ∈ bundle.trivializationAtlas)
    {b : B} (hb : b ∈ chart.baseSet)
    (v : TangentSpace IB b)
    (mismatch :
      mfderiv IP IB torsor.projection (principalBundleLocalSection chart b)
          (principalBundleLocalTangentLift (IB := IB) (IP := IP) chart b v) ≠ v) : False :=
  mismatch (principalBundleLocalTangentLift_rightInverse
    smoothBundle chart chart_mem hb v)

/-- The exact differential composition cannot be replaced by a nonidentity endomorphism. -/
theorem nonidentity_principalBundle_projectionLiftComposition_blocked
    (smoothBundle : SmoothPrincipalBundleData IB IG IP torsor bundle)
    (chart : PrincipalBundleLocalTrivialization torsor)
    (chart_mem : chart ∈ bundle.trivializationAtlas)
    {b : B} (hb : b ∈ chart.baseSet)
    (mismatch :
      (mfderiv IP IB torsor.projection (principalBundleLocalSection chart b)).comp
          (principalBundleLocalTangentLift (IB := IB) (IP := IP) chart b) ≠
        ContinuousLinearMap.id ℝ (TangentSpace IB b)) : False :=
  mismatch (principalBundleProjectionDifferential_comp_localTangentLift
    smoothBundle chart chart_mem hb)

end

end YangMills.Geometry.Probes
