/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Geometry.TopologicalPrincipalBundle
import Mathlib.Geometry.Manifold.Algebra.LieGroup

/-!
# Smooth principal bundles

This module adds manifold structures and smooth compatibility to the topological principal-bundle
atlas. It does not define connections or curvature.
-/

namespace YangMills.Geometry

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

/-- Smooth compatibility data for a fixed topological principal bundle.

Every designated local homeomorphism and its inverse are smooth on their declared domains. This
makes smooth overlap compatibility derivable rather than storing unrelated transition functions. -/
structure SmoothPrincipalBundleData
    (IB : ModelWithCorners ℝ EB HB)
    (IG : ModelWithCorners ℝ EG HG)
    (IP : ModelWithCorners ℝ EP HP)
    [ChartedSpace HB B] [IsManifold IB ∞ B]
    [ChartedSpace HG G] [LieGroup IG ∞ G]
    [ChartedSpace HP P] [IsManifold IP ∞ P]
    (torsor : PrincipalBundleTorsorData G B P)
    (bundle : TopologicalPrincipalBundleData torsor) : Prop where
  /-- The bundle projection is smooth. -/
  projection_smooth : ContMDiff IP IB ∞ torsor.projection
  /-- The uncurried right action is smooth. -/
  rightAction_smooth :
    ContMDiff (IP.prod IG) IP ∞ fun pg : P × G => torsor.rightAction pg.1 pg.2
  /-- Every chart in the designated atlas is smooth on its source. -/
  trivialization_smooth : ∀ chart ∈ bundle.trivializationAtlas,
    ContMDiffOn IP (IB.prod IG) ∞ chart.toPartialHomeomorph
      chart.toPartialHomeomorph.source
  /-- Every inverse chart is smooth on its target. -/
  inverse_trivialization_smooth : ∀ chart ∈ bundle.trivializationAtlas,
    ContMDiffOn (IB.prod IG) IP ∞ chart.toPartialHomeomorph.symm
      chart.toPartialHomeomorph.target

namespace SmoothPrincipalBundleData

/-- The global product principal bundle has its expected smooth structure. -/
def trivial
    (IB : ModelWithCorners ℝ EB HB)
    (IG : ModelWithCorners ℝ EG HG)
    {G : Type uG} {B : Type uB}
    [Group G] [TopologicalSpace G] [TopologicalSpace B] [IsTopologicalGroup G]
    [ChartedSpace HG G] [LieGroup IG ∞ G]
    [ChartedSpace HB B] [IsManifold IB ∞ B] :
    SmoothPrincipalBundleData IB IG (IB.prod IG)
      (PrincipalBundleTorsorData.trivial G B)
      (TopologicalPrincipalBundleData.trivial G B) := by
  refine {
    projection_smooth := contMDiff_fst
    rightAction_smooth := ?_
    trivialization_smooth := ?_
    inverse_trivialization_smooth := ?_
  }
  · exact (contMDiff_fst.comp contMDiff_fst).prodMk
      ((contMDiff_snd.comp contMDiff_fst).mul contMDiff_snd)
  · intro chart memAtlas
    simp only [TopologicalPrincipalBundleData.trivial, Set.mem_singleton_iff] at memAtlas
    subst chart
    exact contMDiff_id.contMDiffOn
  · intro chart memAtlas
    simp only [TopologicalPrincipalBundleData.trivial, Set.mem_singleton_iff] at memAtlas
    subst chart
    exact contMDiff_id.contMDiffOn

end SmoothPrincipalBundleData

end YangMills.Geometry
