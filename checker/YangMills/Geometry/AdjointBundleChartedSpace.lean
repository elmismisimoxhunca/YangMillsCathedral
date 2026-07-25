/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Geometry.SmoothAdjointBundleTransition
import Mathlib.Geometry.Manifold.ChartedSpace

/-!
# Charted-space atlas on the adjoint quotient

The selected promoted adjoint-bundle trivializations, explicitly transported through the canonical
tangent-model equivalence, define a charted-space structure directly on the existing orbit quotient
and its existing quotient topology. A second definition composes these
product charts with the base manifold charts to use the standard product model.

These are explicit structures derived from a fixed principal-bundle atlas, not global instances.
No compatibility groupoid, manifold, `FiberBundle`, or `VectorBundle` structure is claimed here.
-/

namespace YangMills.Geometry

open Set
open scoped Manifold ContDiff

universe uEG uHG uEB uHB uG uB uP

noncomputable section

variable
    {EG : Type uEG} {HG : Type uHG}
    [NormedAddCommGroup EG] [NormedSpace ℝ EG] [TopologicalSpace HG]
    {EB : Type uEB} {HB : Type uHB}
    [NormedAddCommGroup EB] [NormedSpace ℝ EB] [TopologicalSpace HB]
    {G : Type uG} {B : Type uB} {P : Type uP}
    [Group G] [TopologicalSpace G] [TopologicalSpace B] [TopologicalSpace P]
    [IsTopologicalGroup G]
    {IG : ModelWithCorners ℝ EG HG}
    {IB : ModelWithCorners ℝ EB HB}
    [ChartedSpace HG G] [LieGroup IG ∞ G]
    [ChartedSpace HB B]
    {torsor : PrincipalBundleTorsorData G B P}
    (bundle : TopologicalPrincipalBundleData torsor)

set_option backward.isDefEq.respectTransparency false in
/-- Product-coordinate charted-space structure on the actual adjoint quotient. Its atlas consists
exactly of the promoted charts from the designated principal atlas, and its selected chart at `z`
comes from the principal chart selected at the projection of `z`. -/
@[reducible]
def AdjointBundle.productChartedSpace :
    ChartedSpace (B × EG) (AdjointBundle (I := IG) torsor) where
  atlas :=
    (fun chart : PrincipalBundleLocalTrivialization torsor =>
      (AdjointBundle.modelBundleTrivialization (I := IG) bundle chart).toOpenPartialHomeomorph) ''
      bundle.trivializationAtlas
  chartAt := fun z =>
    (AdjointBundle.modelBundleTrivialization (I := IG) bundle
      (bundle.trivializationAt (AdjointBundle.projection torsor z))).toOpenPartialHomeomorph
  mem_chart_source := fun z =>
    AdjointBundle.mem_source_bundleTrivializationAt (I := IG) bundle z
  chart_mem_atlas := fun z => Set.mem_image_of_mem _
    (bundle.trivializationAt_mem_atlas (AdjointBundle.projection torsor z))

set_option backward.isDefEq.respectTransparency false in
/-- The selected product chart is definitionally the promoted trivialization selected at the
associated point's base projection. -/
theorem AdjointBundle.productChartedSpace_chartAt
    (z : AdjointBundle (I := IG) torsor) :
    (AdjointBundle.productChartedSpace (IG := IG) bundle).chartAt z =
      (AdjointBundle.modelBundleTrivialization (I := IG) bundle
        (bundle.trivializationAt (AdjointBundle.projection torsor z))).toOpenPartialHomeomorph :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The product atlas contains exactly promoted designated principal charts. -/
theorem AdjointBundle.mem_productChartedSpace_atlas_iff
    (e : OpenPartialHomeomorph (AdjointBundle (I := IG) torsor) (B × EG)) :
    e ∈ (AdjointBundle.productChartedSpace (IG := IG) bundle).atlas ↔
      ∃ chart ∈ bundle.trivializationAtlas,
        (AdjointBundle.modelBundleTrivialization (I := IG) bundle chart).toOpenPartialHomeomorph = e := by
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Composing the quotient product charts with the base charts gives the standard product model
`ModelProd HB EG`, while retaining the same quotient topology and selected associated atlas. -/
@[reducible]
def AdjointBundle.modelChartedSpace :
    ChartedSpace (ModelProd HB EG) (AdjointBundle (I := IG) torsor) := by
  letI : ChartedSpace (B × EG) (AdjointBundle (I := IG) torsor) :=
    AdjointBundle.productChartedSpace (IG := IG) bundle
  exact ChartedSpace.comp (ModelProd HB EG) (B × EG)
    (AdjointBundle (I := IG) torsor)

end

end YangMills.Geometry
