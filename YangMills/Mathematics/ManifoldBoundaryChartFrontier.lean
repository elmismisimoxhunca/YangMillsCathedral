/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary

/-!
# Boundary points in arbitrary extended charts

An intrinsic manifold boundary point maps to the frontier of the model-with-corners range in every
eligible chart around it. Mathlib directly gives membership in the frontier of that chart's target;
relative openness of the target and closedness of the model range upgrade this to the model frontier.
-/

namespace YangMills.Mathematics

open Set
open scoped Manifold ContDiff Topology

noncomputable section

/-- Every eligible chart sends an intrinsic boundary point to the frontier of the exact
model-with-corners range. -/
theorem chartCoordinate_mem_frontier_range_of_isBoundaryPoint
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {e : OpenPartialHomeomorph M H} {x : M}
    (he : e ∈ atlas H M) (hxe : x ∈ e.source) (boundary : I.IsBoundaryPoint x) :
    e.extend I x ∈ frontier (Set.range I) := by
  have boundaryChart : e.extend I x ∈ frontier (e.extend I).target :=
    (I.isBoundaryPoint_iff_of_mem_atlas (n := (1 : WithTop ℕ∞))
      (by norm_num) he hxe).mp boundary
  have targetMem : e.extend I x ∈ (e.extend I).target :=
    (e.extend I).map_source (by simpa [e.extend_source] using hxe)
  have rangeMem : e.extend I x ∈ Set.range I := e.extend_target_subset_range targetMem
  rw [frontier, I.isClosed_range.closure_eq]
  refine ⟨rangeMem, ?_⟩
  intro interiorRange
  have interiorTarget : e.extend I x ∈ interior (e.extend I).target := by
    apply e.mem_interior_extend_target (e.map_source hxe)
    simpa [OpenPartialHomeomorph.extend_coe] using interiorRange
  rw [frontier] at boundaryChart
  exact boundaryChart.2 interiorTarget

end

end YangMills.Mathematics
