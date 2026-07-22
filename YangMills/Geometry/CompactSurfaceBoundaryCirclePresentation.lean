/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Geometry.CompactOrientedMeasuredSurface
import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.Geometry.Manifold.SmoothEmbedding

/-!
# Exact circle presentations of compact-surface boundary components

Pinned Mathlib defines the exact boundary set of a manifold with corners but does not yet package
that subtype as a general smooth submanifold. This file therefore records source-facing boundary
circle presentations explicitly: every actual connected component of the exact boundary is the
range of one smooth embedded copy of Mathlib's genuine unit-circle manifold, with no extra or
missing boundary points.

Closed surfaces are retained: their boundary-component carrier may be empty. A later sewing datum
must separately select a positive number of components. No gluing or Yang--Mills law is constructed.
-/

namespace YangMills.Geometry

open Set
open scoped Manifold ContDiff

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

/-- Exact points in one connected component of Mathlib's manifold boundary. -/
def compactSurfaceBoundaryComponentSet
    (surface : CompactOrientedMeasuredSurfaceData I Surface)
    (component : surface.BoundaryComponent) : Set Surface :=
  {point | ∃ boundaryMembership : point ∈ I.boundary Surface,
    ConnectedComponents.mk ⟨point, boundaryMembership⟩ = component}

/-- Finite smooth circle presentation of every exact boundary component. -/
structure CompactSurfaceBoundaryCirclePresentationData
    (surface : CompactOrientedMeasuredSurfaceData I Surface) where
  /-- Finiteness is source-required. It is not inferred from arbitrary compact-space component
  theory. -/
  boundaryComponentFinite : Finite surface.BoundaryComponent
  /-- One actual unit-circle parameterization for each exact component. -/
  parameterization : surface.BoundaryComponent → Circle → Surface
  /-- Genuine smooth embedding: both topological embedding and immersion are retained. -/
  parameterization_smoothEmbedding : ∀ component,
    Manifold.IsSmoothEmbedding (𝓡 1) I ∞ (parameterization component)
  /-- No auxiliary circles: the range is exactly one connected component of the actual boundary. -/
  parameterization_range : ∀ component,
    Set.range (parameterization component) =
      compactSurfaceBoundaryComponentSet surface component

namespace CompactSurfaceBoundaryCirclePresentationData

variable {surface : CompactOrientedMeasuredSurfaceData I Surface}

/-- Install the exact finite component instance only locally when needed. -/
@[reducible] noncomputable def boundaryComponentFiniteness
    (presentation : CompactSurfaceBoundaryCirclePresentationData surface) :
    Finite surface.BoundaryComponent :=
  presentation.boundaryComponentFinite

/-- A closed surface has no boundary-component labels; the circle-presentation record remains
vacuously compatible with closed surfaces. -/
theorem boundaryComponent_isEmpty_of_boundary_eq_empty
    (_presentation : CompactSurfaceBoundaryCirclePresentationData surface)
    (closedSurface : I.boundary Surface = ∅) : IsEmpty surface.BoundaryComponent := by
  constructor
  intro component
  refine Quotient.inductionOn component ?_
  intro boundaryPoint
  have : (boundaryPoint : Surface) ∈ (∅ : Set Surface) := by
    rw [← closedSurface]
    exact boundaryPoint.property
  exact this

/-- Every actual boundary point lies on its exact connected-component circle. -/
theorem boundary_point_mem_parameterization
    (presentation : CompactSurfaceBoundaryCirclePresentationData surface)
    {point : Surface} (boundaryMembership : point ∈ I.boundary Surface) :
    ∃ circlePoint : Circle,
      presentation.parameterization
        (ConnectedComponents.mk ⟨point, boundaryMembership⟩) circlePoint = point := by
  have membership : point ∈ compactSurfaceBoundaryComponentSet surface
      (ConnectedComponents.mk ⟨point, boundaryMembership⟩) :=
    ⟨boundaryMembership, rfl⟩
  rw [← presentation.parameterization_range] at membership
  exact membership

/-- The union of all exact circle ranges is literally Mathlib's manifold boundary. -/
theorem boundary_eq_iUnion_range
    (presentation : CompactSurfaceBoundaryCirclePresentationData surface) :
    I.boundary Surface =
      ⋃ component : surface.BoundaryComponent,
        Set.range (presentation.parameterization component) := by
  ext point
  constructor
  · intro boundaryMembership
    obtain ⟨circlePoint, equality⟩ :=
      presentation.boundary_point_mem_parameterization boundaryMembership
    exact Set.mem_iUnion.mpr ⟨ConnectedComponents.mk ⟨point, boundaryMembership⟩,
      ⟨circlePoint, equality⟩⟩
  · intro membership
    obtain ⟨component, componentMembership⟩ := Set.mem_iUnion.mp membership
    rw [presentation.parameterization_range] at componentMembership
    exact componentMembership.choose

/-- Distinct component circles have disjoint ranges. -/
theorem parameterization_ranges_disjoint
    (presentation : CompactSurfaceBoundaryCirclePresentationData surface)
    {first second : surface.BoundaryComponent} (different : first ≠ second) :
    Disjoint (Set.range (presentation.parameterization first))
      (Set.range (presentation.parameterization second)) := by
  rw [presentation.parameterization_range, presentation.parameterization_range]
  apply Set.disjoint_left.mpr
  intro point firstMembership secondMembership
  exact different (firstMembership.choose_spec.symm.trans secondMembership.choose_spec)

/-- Every component parameterization is smooth, derived from the genuine smooth embedding. -/
theorem parameterization_smooth
    (presentation : CompactSurfaceBoundaryCirclePresentationData surface)
    (component : surface.BoundaryComponent) :
    ContMDiff (𝓡 1) I ∞ (presentation.parameterization component) :=
  (presentation.parameterization_smoothEmbedding component).contMDiff

/-- Every component parameterization is a topological embedding, derived from the genuine smooth
embedding. -/
theorem parameterization_embedding
    (presentation : CompactSurfaceBoundaryCirclePresentationData surface)
    (component : surface.BoundaryComponent) :
    Topology.IsEmbedding (presentation.parameterization component) :=
  (presentation.parameterization_smoothEmbedding component).isEmbedding

/-- Every component parameterization is injective. -/
theorem parameterization_injective
    (presentation : CompactSurfaceBoundaryCirclePresentationData surface)
    (component : surface.BoundaryComponent) :
    Function.Injective (presentation.parameterization component) :=
  (presentation.parameterization_smoothEmbedding component).isEmbedding.injective

/-- Every parameterized circle point is an actual boundary point in its selected component. -/
theorem parameterization_mem_boundary_component
    (presentation : CompactSurfaceBoundaryCirclePresentationData surface)
    (component : surface.BoundaryComponent) (circlePoint : Circle) :
    ∃ boundaryMembership : presentation.parameterization component circlePoint ∈ I.boundary Surface,
      ConnectedComponents.mk
        ⟨presentation.parameterization component circlePoint, boundaryMembership⟩ = component := by
  have membership : presentation.parameterization component circlePoint ∈
      Set.range (presentation.parameterization component) := ⟨circlePoint, rfl⟩
  rw [presentation.parameterization_range] at membership
  exact membership

end CompactSurfaceBoundaryCirclePresentationData

end

end YangMills.Geometry
