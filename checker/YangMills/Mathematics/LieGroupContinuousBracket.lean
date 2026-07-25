/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Mathematics.LieBracketWedge
import YangMills.Mathematics.LieGroupAdjoint
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Continuity of the finite-dimensional Lie-group tangent bracket

Mathlib constructs the bracket on a Lie group's tangent space algebraically. This module packages
the missing topological bridge: in finite dimension, the bilinear bracket is jointly continuous.
The proof transports the bracket to the normed model, converts both linear variables to continuous
linear maps, and transports continuity back through the canonical tangent/model equivalence.
-/

namespace YangMills.Mathematics

open scoped Manifold ContDiff

universe uE uH uG

set_option backward.isDefEq.respectTransparency false in
/-- The finite-dimensional tangent bracket, transported to the normed model and curried as two
continuous linear variables. -/
noncomputable def groupLieAlgebraCoordinateBracketCLM
    {E : Type uE} {H : Type uH}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H}
    {G : Type uG} [Group G] [TopologicalSpace G] [ChartedSpace H G]
    [LieGroup I (minSmoothness ℝ 3) G] :
    letI : CompleteSpace E := FiniteDimensional.complete ℝ E
    E →L[ℝ] E →L[ℝ] E := by
  let coordinates := groupLieAlgebraModelEquiv (G := G) I
  let bracketLinear : E →ₗ[ℝ] E →ₗ[ℝ] E := LinearMap.mk₂ ℝ
    (fun x y => coordinates ⁅coordinates.symm x, coordinates.symm y⁆)
    (by intro x y z; simp [add_lie])
    (by intro c x y; simp)
    (by intro x y z; simp [lie_add])
    (by intro c x y; simp)
  let bracketInner : E →ₗ[ℝ] (E →L[ℝ] E) :=
    (LinearMap.toContinuousLinearMap : (E →ₗ[ℝ] E) ≃ₗ[ℝ] (E →L[ℝ] E)).comp
      bracketLinear
  exact LinearMap.toContinuousLinearMap bracketInner

set_option backward.isDefEq.respectTransparency false in
/-- The tangent Lie algebra of a sufficiently smooth finite-dimensional real Lie group has a
jointly continuous bracket. -/
noncomputable instance instContinuousLieBracketGroupLieAlgebra
    {E : Type uE} {H : Type uH}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H}
    {G : Type uG} [Group G] [TopologicalSpace G] [ChartedSpace H G]
    [LieGroup I (minSmoothness ℝ 3) G] :
    letI : CompleteSpace E := FiniteDimensional.complete ℝ E
    ContinuousLieBracket (GroupLieAlgebra I G) := by
  let coordinates := groupLieAlgebraModelEquiv (G := G) I
  let bracketContinuousLinear : E →L[ℝ] E →L[ℝ] E :=
    groupLieAlgebraCoordinateBracketCLM (I := I) (G := G)
  have bracket_coordinates_continuous : Continuous fun pair : E × E =>
      coordinates ⁅coordinates.symm pair.1, coordinates.symm pair.2⁆ := by
    exact (bracketContinuousLinear.continuous.comp continuous_fst).clm_apply continuous_snd
  refine ⟨?_⟩
  have input_coordinates : Continuous
      (fun pair : GroupLieAlgebra I G × GroupLieAlgebra I G =>
        (coordinates pair.1, coordinates pair.2)) :=
    (coordinates.continuous.comp continuous_fst).prodMk
      (coordinates.continuous.comp continuous_snd)
  have transported := coordinates.symm.continuous.comp
    (bracket_coordinates_continuous.comp input_coordinates)
  simpa [Function.comp_def, coordinates] using transported

end YangMills.Mathematics
