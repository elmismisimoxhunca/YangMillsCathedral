/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Minkowski.PoincareTopologicalCover

/-!
# Two-sheeted Poincaré covering requirement

Streater–Wightman printed p. 12, equations `(1-14)`–`(1-15)`, states that the `SL(2,ℂ)` map onto the
restricted Lorentz group identifies exactly `A` and `-A`. The inhomogeneous construction on printed
p. 14 retains this two-sheeted homogeneous projection.

This module strengthens the genuine covering-space interface by requiring every exact affine fiber
to be equivalent to `Fin 2`. It does not label the sheets as `±1`, construct matrices or a semidirect
product, prove a kernel theorem, or construct an inhabitant.
-/

namespace YangMills.Minkowski

/-- A genuine Poincaré covering projection with exactly two points in every fiber. -/
structure ProperOrthochronousPoincareDoubleCoverData
    (d : EuclideanDimension) (G : Type*)
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    extends ProperOrthochronousPoincareCoverData d G where
  /-- Exact two-sheet semantics at every affine target point. -/
  fiberEquivFinTwo : ∀ target : ProperOrthochronousPoincareTransformation d,
    (toProperOrthochronousPoincareCoverData.projection ⁻¹' ({target} : Set _)) ≃ Fin 2

namespace ProperOrthochronousPoincareDoubleCoverData

/-- Every affine target has two explicitly distinct lift points. -/
theorem exists_two_distinct_lifts
    {d : EuclideanDimension} {G : Type*}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (cover : ProperOrthochronousPoincareDoubleCoverData d G)
    (target : ProperOrthochronousPoincareTransformation d) :
    ∃ first second : G,
      cover.projection first = target ∧
      cover.projection second = target ∧
      first ≠ second := by
  let firstFiber : cover.projection ⁻¹' ({target} : Set _) :=
    (cover.fiberEquivFinTwo target).symm 0
  let secondFiber : cover.projection ⁻¹' ({target} : Set _) :=
    (cover.fiberEquivFinTwo target).symm 1
  refine ⟨firstFiber.1, secondFiber.1, ?_, ?_, ?_⟩
  · exact Set.mem_singleton_iff.mp firstFiber.2
  · exact Set.mem_singleton_iff.mp secondFiber.2
  · intro equality
    have subtypeEquality : firstFiber = secondFiber := Subtype.ext equality
    have finEquality := congrArg (cover.fiberEquivFinTwo target) subtypeEquality
    dsimp [firstFiber, secondFiber] at finEquality
    simp only [Equiv.apply_symm_apply] at finEquality
    exact Fin.zero_ne_one finEquality

/-- Every exact fiber is finite, derived from its equivalence with `Fin 2`. -/
theorem projection_fiber_finite
    {d : EuclideanDimension} {G : Type*}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (cover : ProperOrthochronousPoincareDoubleCoverData d G)
    (target : ProperOrthochronousPoincareTransformation d) :
    Finite (cover.projection ⁻¹' ({target} : Set _)) :=
  Finite.of_equiv (Fin 2) (cover.fiberEquivFinTwo target).symm

end ProperOrthochronousPoincareDoubleCoverData

end YangMills.Minkowski
