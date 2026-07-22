/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Geometry.CompactSurfaceBoundaryCirclePresentation

/-!
# Hostile probes for compact-surface boundary circle presentations
-/

namespace YangMills.Geometry.CompactSurfaceBoundaryCirclePresentation.Probes

open Set
open scoped Manifold ContDiff

universe uE uH uSurface

variable
    {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    {H : Type uH} [TopologicalSpace H]
    {Surface : Type uSurface} [TopologicalSpace Surface]
    [MeasurableSpace Surface] [BorelSpace Surface]
    {I : ModelWithCorners ℝ E H} [ChartedSpace H Surface] [IsManifold I ∞ Surface]
    [CompactSpace Surface] [T2Space Surface] [SecondCountableTopology Surface]
    {surface : CompactOrientedMeasuredSurfaceData I Surface}

/-- Finiteness concerns the exact connected-component quotient of the actual boundary. -/
@[reducible] def exact_boundary_component_finiteness
    (presentation : CompactSurfaceBoundaryCirclePresentationData surface) :
    Finite surface.BoundaryComponent :=
  presentation.boundaryComponentFinite

/-- Every exact component is presented by a smooth embedded genuine unit circle. -/
theorem exact_smooth_embedded_circle
    (presentation : CompactSurfaceBoundaryCirclePresentationData surface)
    (component : surface.BoundaryComponent) :
    Manifold.IsSmoothEmbedding (𝓡 1) I ∞ (presentation.parameterization component) ∧
      ContMDiff (𝓡 1) I ∞ (presentation.parameterization component) ∧
      Topology.IsEmbedding (presentation.parameterization component) :=
  ⟨presentation.parameterization_smoothEmbedding component,
    presentation.parameterization_smooth component,
    presentation.parameterization_embedding component⟩

/-- Each circle range is exactly one connected component of Mathlib's boundary. -/
theorem exact_component_range
    (presentation : CompactSurfaceBoundaryCirclePresentationData surface)
    (component : surface.BoundaryComponent) :
    Set.range (presentation.parameterization component) =
      compactSurfaceBoundaryComponentSet surface component :=
  presentation.parameterization_range component

/-- Every actual boundary point is covered by the circle indexed by its own exact component. -/
theorem exact_boundary_point_coverage
    (presentation : CompactSurfaceBoundaryCirclePresentationData surface)
    {point : Surface} (boundaryMembership : point ∈ I.boundary Surface) :
    ∃ circlePoint : Circle,
      presentation.parameterization
        (ConnectedComponents.mk ⟨point, boundaryMembership⟩) circlePoint = point :=
  presentation.boundary_point_mem_parameterization boundaryMembership

/-- The full family of circle ranges covers exactly the actual boundary and nothing else. -/
theorem exact_boundary_cover
    (presentation : CompactSurfaceBoundaryCirclePresentationData surface) :
    I.boundary Surface =
      ⋃ component : surface.BoundaryComponent,
        Set.range (presentation.parameterization component) :=
  presentation.boundary_eq_iUnion_range

/-- Distinct exact components cannot share a parameterized boundary point. -/
theorem exact_distinct_component_disjointness
    (presentation : CompactSurfaceBoundaryCirclePresentationData surface)
    {first second : surface.BoundaryComponent} (different : first ≠ second) :
    Disjoint (Set.range (presentation.parameterization first))
      (Set.range (presentation.parameterization second)) :=
  presentation.parameterization_ranges_disjoint different

/-- Every circle parameterization is injective, blocking doubled traversal as a component
presentation. -/
theorem exact_circle_injective
    (presentation : CompactSurfaceBoundaryCirclePresentationData surface)
    (component : surface.BoundaryComponent) :
    Function.Injective (presentation.parameterization component) :=
  presentation.parameterization_injective component

/-- A proposed unrelated circle range is rejected. -/
theorem unrelated_circle_range_blocked
    (presentation : CompactSurfaceBoundaryCirclePresentationData surface)
    (component : surface.BoundaryComponent) (wrong : Set Surface)
    (different : wrong ≠ compactSurfaceBoundaryComponentSet surface component)
    (claimed : Set.range (presentation.parameterization component) = wrong) : False := by
  apply different
  rw [← claimed]
  exact presentation.parameterization_range component

/-- Closed surfaces remain admissible and have no boundary-component labels. -/
theorem exact_closed_surface_has_no_components
    (presentation : CompactSurfaceBoundaryCirclePresentationData surface)
    (closedSurface : I.boundary Surface = ∅) :
    IsEmpty surface.BoundaryComponent :=
  presentation.boundaryComponent_isEmpty_of_boundary_eq_empty closedSurface

end YangMills.Geometry.CompactSurfaceBoundaryCirclePresentation.Probes
