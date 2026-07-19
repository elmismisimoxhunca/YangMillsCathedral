/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Mathematics.LieGroupContinuousBracket
import Mathlib.Analysis.Calculus.FDeriv.Bilinear

/-!
# Differential calculus for the finite-dimensional Lie-group bracket

The actual group Lie-algebra bracket is already transported to the normed model as
`groupLieAlgebraCoordinateBracketCLM`. This module exposes its exact evaluation and applies
Mathlib's bounded-bilinear derivative rule to that same map. No auxiliary or disconnected bracket is
accepted.

This is reusable normed-coordinate calculus. It is a prerequisite for a local-model graded Leibniz
calculation, not such a calculation itself, and it does not prove a manifold or covariant Bianchi
identity.
-/

namespace YangMills.Mathematics

open scoped Manifold ContDiff

universe uE uH uG uX

set_option backward.isDefEq.respectTransparency false in
/-- The bundled coordinate bracket evaluates to the exact transported Mathlib tangent bracket. -/
@[simp]
theorem groupLieAlgebraCoordinateBracketCLM_apply
    {E : Type uE} {H : Type uH}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {G : Type uG} [Group G] [TopologicalSpace G] [ChartedSpace H G]
    [LieGroup I (minSmoothness ℝ 3) G] (x y : E) :
    letI : CompleteSpace E := FiniteDimensional.complete ℝ E
    groupLieAlgebraCoordinateBracketCLM (I := I) (G := G) x y =
      groupLieAlgebraModelEquiv (G := G) I
        ⁅(groupLieAlgebraModelEquiv (G := G) I).symm x,
          (groupLieAlgebraModelEquiv (G := G) I).symm y⁆ := by
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Bilinear differentiation of the exact transported group Lie-algebra bracket. Both input
`HasFDerivAt` witnesses determine the output derivative; no differentiability witness for a
separate bracketed function is assumed. -/
theorem groupLieAlgebraCoordinateBracket_hasFDerivAt
    {E : Type uE} {H : Type uH}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {G : Type uG} [Group G] [TopologicalSpace G] [ChartedSpace H G]
    [LieGroup I (minSmoothness ℝ 3) G]
    {X : Type uX} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (first second : X → E) (firstDerivative secondDerivative : X →L[ℝ] E) (x : X)
    (first_hasDerivative : HasFDerivAt first firstDerivative x)
    (second_hasDerivative : HasFDerivAt second secondDerivative x) :
    letI : CompleteSpace E := FiniteDimensional.complete ℝ E
    let bracket := groupLieAlgebraCoordinateBracketCLM (I := I) (G := G)
    HasFDerivAt
      (fun z => groupLieAlgebraModelEquiv (G := G) I
        ⁅(groupLieAlgebraModelEquiv (G := G) I).symm (first z),
          (groupLieAlgebraModelEquiv (G := G) I).symm (second z)⁆)
      (bracket.precompR X (first x) secondDerivative +
        bracket.precompL X firstDerivative (second x)) x := by
  dsimp only
  let bracket := groupLieAlgebraCoordinateBracketCLM (I := I) (G := G)
  change HasFDerivAt (fun z => bracket (first z) (second z))
    (bracket.precompR X (first x) secondDerivative +
      bracket.precompL X firstDerivative (second x)) x
  exact bracket.hasFDerivAt_of_bilinear first_hasDerivative second_hasDerivative

set_option backward.isDefEq.respectTransparency false in
/-- Evaluation of the exact `fderiv` product rule in an arbitrary source direction. -/
theorem groupLieAlgebraCoordinateBracket_fderiv_apply
    {E : Type uE} {H : Type uH}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {G : Type uG} [Group G] [TopologicalSpace G] [ChartedSpace H G]
    [LieGroup I (minSmoothness ℝ 3) G]
    {X : Type uX} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (first second : X → E) (firstDerivative secondDerivative : X →L[ℝ] E)
    (x direction : X)
    (first_hasDerivative : HasFDerivAt first firstDerivative x)
    (second_hasDerivative : HasFDerivAt second secondDerivative x) :
    letI : CompleteSpace E := FiniteDimensional.complete ℝ E
    fderiv ℝ
      (fun z => groupLieAlgebraModelEquiv (G := G) I
        ⁅(groupLieAlgebraModelEquiv (G := G) I).symm (first z),
          (groupLieAlgebraModelEquiv (G := G) I).symm (second z)⁆)
      x direction =
      groupLieAlgebraCoordinateBracketCLM (I := I) (G := G)
        (first x) (secondDerivative direction) +
      groupLieAlgebraCoordinateBracketCLM (I := I) (G := G)
        (firstDerivative direction) (second x) := by
  letI : CompleteSpace E := FiniteDimensional.complete ℝ E
  have derivative := groupLieAlgebraCoordinateBracket_hasFDerivAt
    (I := I) (G := G) first second firstDerivative secondDerivative x
    first_hasDerivative second_hasDerivative
  rw [derivative.fderiv]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Self-bracket specialization used by the forthcoming derivative of `[A ∧ A]`. -/
theorem groupLieAlgebraCoordinateSelfBracket_fderiv_apply
    {E : Type uE} {H : Type uH}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {G : Type uG} [Group G] [TopologicalSpace G] [ChartedSpace H G]
    [LieGroup I (minSmoothness ℝ 3) G]
    {X : Type uX} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (function : X → E) (derivative : X →L[ℝ] E) (x direction : X)
    (hasDerivative : HasFDerivAt function derivative x) :
    letI : CompleteSpace E := FiniteDimensional.complete ℝ E
    fderiv ℝ
      (fun z => groupLieAlgebraModelEquiv (G := G) I
        ⁅(groupLieAlgebraModelEquiv (G := G) I).symm (function z),
          (groupLieAlgebraModelEquiv (G := G) I).symm (function z)⁆)
      x direction =
      groupLieAlgebraCoordinateBracketCLM (I := I) (G := G)
        (function x) (derivative direction) +
      groupLieAlgebraCoordinateBracketCLM (I := I) (G := G)
        (derivative direction) (function x) :=
  groupLieAlgebraCoordinateBracket_fderiv_apply
    (I := I) (G := G) function function derivative derivative x direction
    hasDerivative hasDerivative

end YangMills.Mathematics
