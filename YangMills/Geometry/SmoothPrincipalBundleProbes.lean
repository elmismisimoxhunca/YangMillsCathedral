/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Geometry.SmoothPrincipalBundle

/-!
# Hostile probes for smooth principal bundles

These probes isolate smooth projection/action and both directions of every designated atlas chart.
They do not mention connections or curvature.
-/

namespace YangMills.Geometry.Probes

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

/-- A nonsmooth projection cannot pass the smooth bundle layer. -/
theorem nonsmooth_bundle_projection_blocked
    (smoothBundle : SmoothPrincipalBundleData IB IG IP torsor bundle)
    (nonsmooth : ¬ContMDiff IP IB ∞ torsor.projection) : False :=
  nonsmooth smoothBundle.projection_smooth

/-- A nonsmooth right action cannot pass the smooth bundle layer. -/
theorem nonsmooth_bundle_rightAction_blocked
    (smoothBundle : SmoothPrincipalBundleData IB IG IP torsor bundle)
    (nonsmooth : ¬ContMDiff (IP.prod IG) IP ∞
      fun pg : P × G => torsor.rightAction pg.1 pg.2) : False :=
  nonsmooth smoothBundle.rightAction_smooth

/-- Every chart belonging to the designated atlas must be smooth on its source. -/
theorem nonsmooth_atlas_chart_blocked
    (smoothBundle : SmoothPrincipalBundleData IB IG IP torsor bundle)
    (chart : PrincipalBundleLocalTrivialization torsor)
    (memAtlas : chart ∈ bundle.trivializationAtlas)
    (nonsmooth : ¬ContMDiffOn IP (IB.prod IG) ∞ chart.toPartialHomeomorph
      chart.toPartialHomeomorph.source) : False :=
  nonsmooth (smoothBundle.trivialization_smooth chart memAtlas)

/-- Every inverse atlas chart must be smooth on its target. -/
theorem nonsmooth_inverse_atlas_chart_blocked
    (smoothBundle : SmoothPrincipalBundleData IB IG IP torsor bundle)
    (chart : PrincipalBundleLocalTrivialization torsor)
    (memAtlas : chart ∈ bundle.trivializationAtlas)
    (nonsmooth : ¬ContMDiffOn (IB.prod IG) IP ∞ chart.toPartialHomeomorph.symm
      chart.toPartialHomeomorph.target) : False :=
  nonsmooth (smoothBundle.inverse_trivialization_smooth chart memAtlas)

/-- The selected chart at every base point inherits both smoothness directions. -/
theorem selected_smooth_trivialization
    (smoothBundle : SmoothPrincipalBundleData IB IG IP torsor bundle) (b : B) :
    ContMDiffOn IP (IB.prod IG) ∞
        (bundle.trivializationAt b).toPartialHomeomorph
        (bundle.trivializationAt b).toPartialHomeomorph.source ∧
      ContMDiffOn (IB.prod IG) IP ∞
        (bundle.trivializationAt b).toPartialHomeomorph.symm
        (bundle.trivializationAt b).toPartialHomeomorph.target :=
  ⟨smoothBundle.trivialization_smooth _ (bundle.trivializationAt_mem_atlas b),
    smoothBundle.inverse_trivialization_smooth _ (bundle.trivializationAt_mem_atlas b)⟩

/-- The product principal bundle is positive consistency evidence for the smooth interface. -/
theorem trivial_smoothPrincipalBundle_exists
    (IB : ModelWithCorners ℝ EB HB)
    (IG : ModelWithCorners ℝ EG HG)
    {G : Type uG} {B : Type uB}
    [Group G] [TopologicalSpace G] [TopologicalSpace B] [IsTopologicalGroup G]
    [ChartedSpace HG G] [LieGroup IG ∞ G]
    [ChartedSpace HB B] [IsManifold IB ∞ B] :
    Nonempty (SmoothPrincipalBundleData IB IG (IB.prod IG)
      (PrincipalBundleTorsorData.trivial G B)
      (TopologicalPrincipalBundleData.trivial G B)) :=
  ⟨SmoothPrincipalBundleData.trivial IB IG⟩

end YangMills.Geometry.Probes
