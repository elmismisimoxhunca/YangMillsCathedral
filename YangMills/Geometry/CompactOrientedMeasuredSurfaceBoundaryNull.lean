/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Geometry.CompactOrientedMeasuredSurface
import YangMills.Mathematics.ManifoldBoundaryChartFrontier
import Mathlib.Analysis.Convex.Measure

/-!
# Nullity of compact-surface manifold boundaries

The designated surface measure has a positive smooth density relative to additive Haar measure in
every extended chart. The convex model range has Haar-null frontier. Arbitrary-chart boundary
frontier membership therefore makes each chart piece of the manifold boundary null, and compactness
of the boundary supplies a finite chart cover. Thus boundary nullity is derived rather than stored.
-/

namespace YangMills.Geometry

open YangMills.Mathematics
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

namespace CompactOrientedMeasuredSurfaceData

/-- The part of the intrinsic boundary lying in any preferred extended-chart source has zero
surface area. -/
theorem boundary_inter_extChartAt_source_null
    (surface : CompactOrientedMeasuredSurfaceData I Surface) (center : Surface) :
    surface.areaMeasure (I.boundary Surface ∩ (extChartAt I center).source) = 0 := by
  let f := extChartAt I center
  let frontierRange := frontier (Set.range I)
  have haarFrontierNull : Measure.addHaar frontierRange = 0 :=
    I.convex_range.addHaar_frontier Measure.addHaar
  have restrictedHaarFrontierNull :
      (Measure.addHaar.restrict f.target) frontierRange = 0 := by
    rw [Measure.restrict_apply measurableSet_frontier]
    exact measure_mono_null inter_subset_left haarFrontierNull
  have weightedFrontierNull :
      ((Measure.addHaar.restrict f.target).withDensity
        (fun coordinate => ENNReal.ofReal (surface.coordinateDensity center coordinate)))
          frontierRange = 0 :=
    (withDensity_absolutelyContinuous _ _) restrictedHaarFrontierNull
  have mapFrontierNull :
      Measure.map f (surface.areaMeasure.restrict f.source) frontierRange = 0 := by
    rw [surface.areaMeasure_chart center]
    exact weightedFrontierNull
  have preimageFrontierNull :
      (surface.areaMeasure.restrict f.source) (f ⁻¹' frontierRange) = 0 := by
    rw [← Measure.map_apply_of_aemeasurable (surface.chart_aemeasurable center)
      measurableSet_frontier]
    exact mapFrontierNull
  have boundaryPieceSubset : I.boundary Surface ∩ f.source ⊆ f ⁻¹' frontierRange := by
    intro point membership
    exact chartCoordinate_mem_frontier_range_of_isBoundaryPoint
      (e := chartAt H center) (chart_mem_atlas H center)
      (by simpa [f, extChartAt, OpenPartialHomeomorph.extend_source] using membership.2)
      membership.1
  have restrictedBoundaryNull :
      (surface.areaMeasure.restrict f.source) (I.boundary Surface ∩ f.source) = 0 :=
    measure_mono_null boundaryPieceSubset preimageFrontierNull
  rw [Measure.restrict_apply (surface.boundary_isClosed.measurableSet.inter
    (isOpen_extChartAt_source center).measurableSet)] at restrictedBoundaryNull
  simpa [f, inter_assoc] using restrictedBoundaryNull

/-- The full intrinsic manifold boundary has zero designated surface area. This follows from the
chart density law and compactness; it is not an independent surface or gluing assumption. -/
theorem boundary_null
    (surface : CompactOrientedMeasuredSurfaceData I Surface) :
    surface.areaMeasure (I.boundary Surface) = 0 := by
  classical
  obtain ⟨centers, cover⟩ := surface.boundary_isCompact.elim_finite_subcover
    (fun center : Surface => (extChartAt I center).source)
    (fun center => isOpen_extChartAt_source center)
    (fun point _ => Set.mem_iUnion.mpr ⟨point, mem_extChartAt_source point⟩)
  let pieces : Surface → Set Surface :=
    fun center => I.boundary Surface ∩ (extChartAt I center).source
  have piecesNull : ∀ center, surface.areaMeasure (pieces center) = 0 := by
    intro center
    exact surface.boundary_inter_extChartAt_source_null center
  have finiteUnionNull : surface.areaMeasure (⋃ center ∈ centers, pieces center) = 0 := by
    clear cover
    induction centers using Finset.induction_on with
    | empty => simp
    | @insert center centers notMem induction =>
        rw [Finset.set_biUnion_insert]
        exact measure_union_null (piecesNull center) induction
  apply measure_mono_null ?_ finiteUnionNull
  intro point boundaryPoint
  obtain ⟨center, centerMem, sourceMem⟩ := Set.mem_iUnion₂.mp (cover boundaryPoint)
  exact Set.mem_iUnion₂.mpr ⟨center, centerMem, boundaryPoint, sourceMem⟩

end CompactOrientedMeasuredSurfaceData

end

end YangMills.Geometry
