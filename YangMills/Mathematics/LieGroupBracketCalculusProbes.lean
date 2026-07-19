/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Mathematics.LieGroupBracketCalculus

/-!
# Hostile probes for finite-dimensional Lie-group bracket calculus

These probes lock the exact transported bracket, its bounded-bilinear derivative rule, the
self-bracket specialization, and rejection of unrelated bracket or derivative outputs.
-/

namespace YangMills.Mathematics.LieGroupBracketCalculus.Probes

open scoped Manifold ContDiff

universe uE uH uG uX

variable
    {E : Type uE} {H : Type uH}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {G : Type uG} [Group G] [TopologicalSpace G] [ChartedSpace H G]
    [LieGroup I (minSmoothness ℝ 3) G]
    {X : Type uX} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- The calculus map is the exact transported Mathlib tangent bracket. -/
theorem exact_bracket_application (x y : E) :
    letI : CompleteSpace E := FiniteDimensional.complete ℝ E
    groupLieAlgebraCoordinateBracketCLM (I := I) (G := G) x y =
      groupLieAlgebraModelEquiv (G := G) I
        ⁅(groupLieAlgebraModelEquiv (G := G) I).symm x,
          (groupLieAlgebraModelEquiv (G := G) I).symm y⁆ :=
  groupLieAlgebraCoordinateBracketCLM_apply (I := I) (G := G) x y

/-- Both derivatives enter the exact bilinear product rule in their correct slots. -/
theorem exact_fderiv_application
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
        (firstDerivative direction) (second x) :=
  groupLieAlgebraCoordinateBracket_fderiv_apply
    (I := I) (G := G) first second firstDerivative secondDerivative x direction
    first_hasDerivative second_hasDerivative

/-- The self-bracket derivative uses two terms from the same function and derivative. -/
theorem exact_self_bracket_derivative
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
  groupLieAlgebraCoordinateSelfBracket_fderiv_apply
    (I := I) (G := G) function derivative x direction hasDerivative

/-- An unrelated continuous bilinear map cannot masquerade as the transported Lie bracket. -/
theorem unrelated_bracket_map_blocked
    (other : E →L[ℝ] E →L[ℝ] E)
    (different :
      letI : CompleteSpace E := FiniteDimensional.complete ℝ E
      other ≠ groupLieAlgebraCoordinateBracketCLM (I := I) (G := G))
    (claimed : ∀ x y,
      other x y = groupLieAlgebraModelEquiv (G := G) I
        ⁅(groupLieAlgebraModelEquiv (G := G) I).symm x,
          (groupLieAlgebraModelEquiv (G := G) I).symm y⁆) : False := by
  letI : CompleteSpace E := FiniteDimensional.complete ℝ E
  apply different
  ext x y
  rw [claimed, groupLieAlgebraCoordinateBracketCLM_apply]

/-- A malformed derivative value is rejected whenever it differs from the canonical two-term
bilinear derivative. -/
theorem malformed_derivative_blocked
    (first second : X → E) (firstDerivative secondDerivative : X →L[ℝ] E)
    (x direction : X)
    (first_hasDerivative : HasFDerivAt first firstDerivative x)
    (second_hasDerivative : HasFDerivAt second secondDerivative x)
    (wrong : E)
    (different :
      letI : CompleteSpace E := FiniteDimensional.complete ℝ E
      wrong ≠
        groupLieAlgebraCoordinateBracketCLM (I := I) (G := G)
          (first x) (secondDerivative direction) +
        groupLieAlgebraCoordinateBracketCLM (I := I) (G := G)
          (firstDerivative direction) (second x))
    (claimed :
      fderiv ℝ
        (fun z => groupLieAlgebraModelEquiv (G := G) I
          ⁅(groupLieAlgebraModelEquiv (G := G) I).symm (first z),
            (groupLieAlgebraModelEquiv (G := G) I).symm (second z)⁆)
        x direction = wrong) : False := by
  letI : CompleteSpace E := FiniteDimensional.complete ℝ E
  apply different
  exact claimed.symm.trans
    (groupLieAlgebraCoordinateBracket_fderiv_apply
      (I := I) (G := G) first second firstDerivative secondDerivative x direction
      first_hasDerivative second_hasDerivative)

end YangMills.Mathematics.LieGroupBracketCalculus.Probes
