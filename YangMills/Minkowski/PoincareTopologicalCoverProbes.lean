/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Minkowski.PoincareTopologicalCover

/-!
# Hostile probes for the genuine Poincaré covering requirement

These probes distinguish a genuine covering projection from the older surjective action-level
pre-cover. They require local homeomorphism, open/quotient behavior, discrete fibers, and nonempty
fibers without claiming two sheets or an `SL(2,ℂ)` construction.
-/

namespace YangMills.Minkowski.PoincareTopologicalCover.Probes

open YangMills
open YangMills.Minkowski

variable
    {d : EuclideanDimension} {G : Type*}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (cover : ProperOrthochronousPoincareCoverData d G)

/-- The exact inherited projection is a Mathlib covering map. -/
example : IsCoveringMap cover.projection :=
  cover.projection_isCoveringMap

/-- Surjectivity alone is insufficient: the accepted projection is a local homeomorphism. -/
example : IsLocalHomeomorph cover.projection :=
  cover.projection_isLocalHomeomorph

/-- The accepted projection is continuous and open. -/
example : Continuous cover.projection ∧ IsOpenMap cover.projection :=
  ⟨cover.projection_continuous, cover.projection_isOpenMap⟩

/-- Inherited surjectivity upgrades the covering projection to a quotient map. -/
example : Topology.IsQuotientMap cover.projection :=
  cover.projection_isQuotientMap

/-- Every exact fiber is discrete. -/
example (target : ProperOrthochronousPoincareTransformation d) :
    DiscreteTopology (cover.projection ⁻¹' ({target} : Set _)) :=
  cover.projection_fiber_discrete target

/-- Every exact fiber is also nonempty by the inherited surjectivity. -/
example (target : ProperOrthochronousPoincareTransformation d) :
    ∃ liftPoint : G, cover.projection liftPoint = target :=
  cover.projection_surjective target

/-- Translation lifts remain the exact physical translations in the genuine cover. -/
example (a : Spacetime d) :
    cover.projection (cover.translation (Multiplicative.ofAdd a)) =
      ProperOrthochronousPoincareTransformation.pureTranslation d a :=
  cover.projection_translation a

end YangMills.Minkowski.PoincareTopologicalCover.Probes
