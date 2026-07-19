/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Minkowski.PoincareCoverRepresentation
import YangMills.Minkowski.PoincareTargetTopology

/-!
# Genuine topological covering requirement for the Poincaré lift

The existing lift/pre-cover provides surjectivity, exact affine actions, and physical translation
lifts but deliberately lacks a covering-map law. With the canonical target topology now available,
this module adds a separate uninhabited strengthening requiring Mathlib's genuine `IsCoveringMap`.

The interface derives continuity, local-homeomorphism, openness, quotient-map behavior, and discrete
fibers. It does not construct the inhomogeneous `SL(2,ℂ)` group, prove a two-sheeted kernel law,
install a group structure on the affine target, or claim a universal cover.
-/

namespace YangMills.Minkowski

/-- A Poincaré lift whose exact projection is a genuine topological covering map. -/
structure ProperOrthochronousPoincareCoverData
    (d : EuclideanDimension) (G : Type*)
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    extends ProperOrthochronousPoincareLiftData d G where
  /-- Every target point has an evenly covered neighborhood for the exact projection. -/
  projection_isCoveringMap : IsCoveringMap toProperOrthochronousPoincareLiftData.projection

namespace ProperOrthochronousPoincareCoverData

/-- A genuine covering projection is continuous. -/
theorem projection_continuous
    {d : EuclideanDimension} {G : Type*}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (cover : ProperOrthochronousPoincareCoverData d G) :
    Continuous cover.projection :=
  cover.projection_isCoveringMap.continuous

/-- A genuine covering projection is a local homeomorphism. -/
theorem projection_isLocalHomeomorph
    {d : EuclideanDimension} {G : Type*}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (cover : ProperOrthochronousPoincareCoverData d G) :
    IsLocalHomeomorph cover.projection :=
  cover.projection_isCoveringMap.isLocalHomeomorph

/-- A genuine covering projection is open. -/
theorem projection_isOpenMap
    {d : EuclideanDimension} {G : Type*}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (cover : ProperOrthochronousPoincareCoverData d G) :
    IsOpenMap cover.projection :=
  cover.projection_isCoveringMap.isOpenMap

/-- Covering plus the inherited exact surjectivity makes the projection a quotient map. -/
theorem projection_isQuotientMap
    {d : EuclideanDimension} {G : Type*}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (cover : ProperOrthochronousPoincareCoverData d G) :
    Topology.IsQuotientMap cover.projection :=
  cover.projection_isCoveringMap.isQuotientMap cover.projection_surjective

/-- Every exact projection fiber has the discrete subspace topology. -/
theorem projection_fiber_discrete
    {d : EuclideanDimension} {G : Type*}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (cover : ProperOrthochronousPoincareCoverData d G)
    (target : ProperOrthochronousPoincareTransformation d) :
    DiscreteTopology (cover.projection ⁻¹' ({target} : Set _)) :=
  (cover.projection_isCoveringMap target).discreteTopology_fiber

end ProperOrthochronousPoincareCoverData

end YangMills.Minkowski
