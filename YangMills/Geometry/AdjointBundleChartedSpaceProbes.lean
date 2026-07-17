/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Geometry.AdjointBundleChartedSpace

/-!
# Hostile probes for the adjoint quotient charted-space atlas
-/

namespace YangMills.Geometry.Probes

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
/-- The selected chart cannot be disconnected from the principal chart selected at the same base. -/
theorem disconnected_adjointBundle_chartAt_blocked
    (z : AdjointBundle (I := IG) torsor)
    (mismatch : (AdjointBundle.productChartedSpace (IG := IG) bundle).chartAt z ≠
      (AdjointBundle.modelBundleTrivialization (I := IG) bundle
        (bundle.trivializationAt (AdjointBundle.projection torsor z))).toOpenPartialHomeomorph) :
    False :=
  mismatch (AdjointBundle.productChartedSpace_chartAt (IG := IG) bundle z)

set_option backward.isDefEq.respectTransparency false in
/-- Every selected chart must contain its adjoint point in its source. -/
theorem selected_adjointBundle_chart_misses_point_blocked
    (z : AdjointBundle (I := IG) torsor)
    (missing : z ∉ ((AdjointBundle.productChartedSpace (IG := IG) bundle).chartAt z).source) :
    False :=
  missing (AdjointBundle.mem_source_bundleTrivializationAt (I := IG) bundle z)

set_option backward.isDefEq.respectTransparency false in
/-- Every promoted designated principal chart remains in the associated atlas. -/
theorem promoted_adjointBundle_chart_missing_from_atlas_blocked
    (chart : PrincipalBundleLocalTrivialization torsor)
    (chart_mem : chart ∈ bundle.trivializationAtlas)
    (missing :
      (AdjointBundle.modelBundleTrivialization (I := IG) bundle chart).toOpenPartialHomeomorph ∉
        (AdjointBundle.productChartedSpace (IG := IG) bundle).atlas) : False :=
  missing (Set.mem_image_of_mem _ chart_mem)

set_option backward.isDefEq.respectTransparency false in
/-- An inhabited adjoint quotient cannot receive an empty associated atlas. -/
theorem empty_adjointBundle_chartedSpace_atlas_blocked
    [Nonempty (AdjointBundle (I := IG) torsor)]
    (emptyAtlas : (AdjointBundle.productChartedSpace (IG := IG) bundle).atlas = ∅) : False := by
  let z : AdjointBundle (I := IG) torsor := Classical.choice inferInstance
  have selectedMem :=
    (AdjointBundle.productChartedSpace (IG := IG) bundle).chart_mem_atlas z
  rw [emptyAtlas] at selectedMem
  exact selectedMem

include bundle in
/-- The standard-model charted structure is constructible from the exact product atlas; no manifold
or vector-bundle assumption is needed. -/
theorem model_adjointBundle_chartedSpace_available :
    Nonempty (ChartedSpace (ModelProd HB EG) (AdjointBundle (I := IG) torsor)) :=
  ⟨AdjointBundle.modelChartedSpace (IG := IG) bundle⟩

end

end YangMills.Geometry.Probes
