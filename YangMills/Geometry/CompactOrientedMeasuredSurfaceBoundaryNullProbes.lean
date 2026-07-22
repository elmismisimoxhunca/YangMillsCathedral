/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Geometry.CompactOrientedMeasuredSurfaceBoundaryNull

/-!
# Hostile probes for compact-surface boundary nullity
-/

namespace YangMills.Geometry.CompactOrientedMeasuredSurfaceBoundaryNull.Probes

open Set MeasureTheory
open scoped Manifold ContDiff Topology

noncomputable section

universe uE uH uSurface

variable
    {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    {H : Type uH} [TopologicalSpace H]
    {Surface : Type uSurface} [TopologicalSpace Surface]
    [MeasurableSpace Surface] [BorelSpace Surface]
    {I : ModelWithCorners ℝ E H} [ChartedSpace H Surface] [IsManifold I ∞ Surface]
    [CompactSpace Surface] [T2Space Surface] [SecondCountableTopology Surface]

/-- Every preferred chart piece of the intrinsic boundary is null under the designated measure. -/
theorem exact_local_boundary_null
    (surface : CompactOrientedMeasuredSurfaceData I Surface) (center : Surface) :
    surface.areaMeasure (I.boundary Surface ∩ (extChartAt I center).source) = 0 :=
  surface.boundary_inter_extChartAt_source_null center

/-- The full boundary is null; no separate gluing witness may choose otherwise. -/
theorem exact_full_boundary_null
    (surface : CompactOrientedMeasuredSurfaceData I Surface) :
    surface.areaMeasure (I.boundary Surface) = 0 :=
  surface.boundary_null

/-- A claimed strictly positive boundary area contradicts the derived chart-density theorem. -/
theorem positive_boundary_area_blocked
    (surface : CompactOrientedMeasuredSurfaceData I Surface)
    (wrongPositive : 0 < surface.areaMeasure (I.boundary Surface)) : False := by
  rw [surface.boundary_null] at wrongPositive
  exact (lt_irrefl 0 wrongPositive)

end

end YangMills.Geometry.CompactOrientedMeasuredSurfaceBoundaryNull.Probes
