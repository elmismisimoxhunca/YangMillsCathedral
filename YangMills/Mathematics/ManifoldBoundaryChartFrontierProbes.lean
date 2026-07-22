/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Mathematics.ManifoldBoundaryChartFrontier

/-!
# Hostile probes for arbitrary-chart boundary frontier membership
-/

namespace YangMills.Mathematics.ManifoldBoundaryChartFrontier.Probes

open Set
open scoped Manifold ContDiff Topology

noncomputable section

/-- Intrinsic boundary membership reaches the model-range frontier in every eligible chart, not
only in the preferred chart. -/
theorem exact_arbitrary_chart_frontier
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {e : OpenPartialHomeomorph M H} {x : M}
    (he : e ∈ atlas H M) (hxe : x ∈ e.source) (boundary : I.IsBoundaryPoint x) :
    e.extend I x ∈ frontier (Set.range I) :=
  chartCoordinate_mem_frontier_range_of_isBoundaryPoint he hxe boundary

/-- A claimed model-interior coordinate for an intrinsic boundary point contradicts the exact
arbitrary-chart frontier theorem. -/
theorem interior_coordinate_for_boundary_blocked
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {e : OpenPartialHomeomorph M H} {x : M}
    (he : e ∈ atlas H M) (hxe : x ∈ e.source) (boundary : I.IsBoundaryPoint x)
    (wrongInterior : e.extend I x ∈ interior (Set.range I)) : False := by
  have frontierMem := chartCoordinate_mem_frontier_range_of_isBoundaryPoint he hxe boundary
  rw [frontier] at frontierMem
  exact frontierMem.2 wrongInterior

end

end YangMills.Mathematics.ManifoldBoundaryChartFrontier.Probes
