/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Minkowski.PoincareTopologicalDoubleCover

/-!
# Hostile probes for two-sheeted Poincaré covering semantics

These probes force every exact affine fiber to contain exactly a `Fin 2`-indexed pair and expose two
distinct lifts. They do not label the pair by matrix signs or claim a concrete kernel.
-/

namespace YangMills.Minkowski.PoincareTopologicalDoubleCover.Probes

open YangMills
open YangMills.Minkowski

variable
    {d : EuclideanDimension} {G : Type*}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (cover : ProperOrthochronousPoincareDoubleCoverData d G)

/-- Every exact affine fiber is equivalent to exactly two labels. -/
example (target : ProperOrthochronousPoincareTransformation d) :
    (cover.projection ⁻¹' ({target} : Set _)) ≃ Fin 2 :=
  cover.fiberEquivFinTwo target

/-- Two distinct lift points exist over every exact target. -/
example (target : ProperOrthochronousPoincareTransformation d) :
    ∃ first second : G,
      cover.projection first = target ∧
      cover.projection second = target ∧
      first ≠ second :=
  cover.exists_two_distinct_lifts target

/-- Fibers are finite as well as discrete. -/
example (target : ProperOrthochronousPoincareTransformation d) :
    Finite (cover.projection ⁻¹' ({target} : Set _)) :=
  cover.projection_fiber_finite target

/-- The underlying projection retains the genuine covering-map law. -/
example : IsCoveringMap cover.projection :=
  cover.projection_isCoveringMap

/-- The exact translation lifts remain connected to physical affine translations. -/
example (a : Spacetime d) :
    cover.projection (cover.translation (Multiplicative.ofAdd a)) =
      ProperOrthochronousPoincareTransformation.pureTranslation d a :=
  cover.projection_translation a

end YangMills.Minkowski.PoincareTopologicalDoubleCover.Probes
