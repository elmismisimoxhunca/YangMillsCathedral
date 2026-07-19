/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Mathematics.ContinuousBilinearSelfWedgeExteriorDerivative

/-!
# Bianchi identity in finite-dimensional normed Lie-group coordinates

For a one-form `A` valued in the canonical normed coordinate model of a finite-dimensional group
Lie algebra, define

`F_A = dA + (1/2) • [A ∧ A]`

and the degree-two covariant exterior expression

`D_A ω = dω + [A ∧ ω]`.

This module proves `D_A F_A = 0` at every point where `A` is twice continuously differentiable.
The proof combines Mathlib's `d² = 0`, the exact local self-wedge exterior-derivative identity, and
the coordinate cubic Jacobi cancellation. The bracket, curvature, and covariant expression all use
the same canonical transported group Lie bracket.

This is a normed-coordinate theorem. It does not construct or transport a positive-degree covariant
exterior derivative on an arbitrary manifold, identify it with the project's principal connection,
or prove existence of any Yang–Mills field or theory.
-/

namespace YangMills.Mathematics

open scoped Manifold ContDiff

universe uT uE uH uG

variable
    {T : Type uT} [NormedAddCommGroup T] [NormedSpace ℝ T]
    {E : Type uE} {H : Type uH}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {G : Type uG} [Group G] [TopologicalSpace G] [ChartedSpace H G]
    [LieGroup I (minSmoothness ℝ 3) G]

/-- Curvature of a normed-coordinate group-Lie-algebra-valued one-form, with the project's fixed
factor-`1/2` bracket-wedge convention. -/
noncomputable def groupLieAlgebraCoordinateCurvature
    (connection : T → T [⋀^Fin 1]→L[ℝ] E) :
    T → T [⋀^Fin 2]→L[ℝ] E :=
  let bracket := groupLieAlgebraCoordinateBracketCLM (I := I) (G := G)
  fun x => extDeriv connection x + (1 / 2 : ℝ) •
    (connection x).continuousBilinearWedgeOneMany bracket 1 (connection x)

/-- Degree-two covariant exterior expression in the same normed coordinates and with the same
connection and canonical bracket. -/
noncomputable def groupLieAlgebraCoordinateCovariantExteriorDerivativeTwo
    (connection : T → T [⋀^Fin 1]→L[ℝ] E)
    (form : T → T [⋀^Fin 2]→L[ℝ] E) :
    T → T [⋀^Fin 3]→L[ℝ] E :=
  let bracket := groupLieAlgebraCoordinateBracketCLM (I := I) (G := G)
  fun x => extDeriv form x +
    (connection x).continuousBilinearWedgeOneMany bracket 2 (form x)

set_option backward.isDefEq.respectTransparency false in
/-- Exact cubic Jacobi cancellation for the canonical coordinate bracket. -/
@[simp]
theorem groupLieAlgebraCoordinateSelfWedge_cubic
    (connection : T [⋀^Fin 1]→L[ℝ] E) :
    letI : CompleteSpace E := FiniteDimensional.complete ℝ E
    let bracket := groupLieAlgebraCoordinateBracketCLM (I := I) (G := G)
    connection.continuousBilinearWedgeOneMany bracket 2
      (connection.continuousBilinearWedgeOneMany bracket 1 connection) = 0 := by
  ext vectors
  rw [ContinuousAlternatingMap.continuousBilinearWedgeOneMany_apply,
    Fin.sum_univ_three]
  simp only [ContinuousAlternatingMap.continuousBilinearWedgeOneMany_one_apply]
  simp [Fin.removeNth]
  rw [show Fin.succAbove (2 : Fin 3) (1 : Fin 2) = (1 : Fin 3) by decide]
  have pair_eq (x y z : GroupLieAlgebra I G) :
      ⁅x, ⁅y, z⁆⁆ - ⁅x, ⁅z, y⁆⁆ = (2 : ℤ) • ⁅x, ⁅y, z⁆⁆ := by
    rw [← lie_skew z y, lie_neg, sub_neg_eq_add, two_zsmul]
  rw [← map_sub, pair_eq, ← map_sub, pair_eq, ← map_sub, pair_eq,
    map_zsmul, map_zsmul, map_zsmul, ← zsmul_add, ← zsmul_add]
  rw [← map_add, ← map_add, lie_jacobi, map_zero, smul_zero]

set_option backward.isDefEq.respectTransparency false in
/-- Normed-coordinate Bianchi identity for the curvature derived from the exact same connection.
Second-order regularity supplies differentiability of `dA`; no curvature or covariant-derivative
witness is accepted independently. -/
theorem groupLieAlgebraCoordinate_bianchi
    (connection : T → T [⋀^Fin 1]→L[ℝ] E) (x : T)
    (connection_regular : ContDiffAt ℝ 2 connection x) :
    letI : CompleteSpace E := FiniteDimensional.complete ℝ E
    groupLieAlgebraCoordinateCovariantExteriorDerivativeTwo
      (I := I) (G := G) connection
      (groupLieAlgebraCoordinateCurvature (I := I) (G := G) connection) x = 0 := by
  dsimp only [groupLieAlgebraCoordinateCovariantExteriorDerivativeTwo,
    groupLieAlgebraCoordinateCurvature]
  let bracket := groupLieAlgebraCoordinateBracketCLM (I := I) (G := G)
  let selfWedge : T → T [⋀^Fin 2]→L[ℝ] E := fun y =>
    (connection y).continuousBilinearWedgeOneMany bracket 1 (connection y)
  let curvature : T → T [⋀^Fin 2]→L[ℝ] E := fun y =>
    extDeriv connection y + (1 / 2 : ℝ) • selfWedge y
  have connection_differentiable : DifferentiableAt ℝ connection x :=
    connection_regular.differentiableAt (by norm_num)
  have derivative_differentiable : DifferentiableAt ℝ (extDeriv connection) x := by
    change DifferentiableAt ℝ (fun y =>
      ContinuousAlternatingMap.alternatizeUncurryFin (fderiv ℝ connection y)) x
    simpa [Function.comp_def] using
      (ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ T E).differentiableAt.comp x
        ((connection_regular.fderiv_right (by norm_num)).differentiableAt one_ne_zero)
  have selfWedge_differentiable : DifferentiableAt ℝ selfWedge x :=
    (ContinuousAlternatingMap.continuousBilinearSelfWedgeOne_hasFDerivAt
      bracket connection (fderiv ℝ connection x) x
      connection_differentiable.hasFDerivAt).differentiableAt
  have curvature_derivative :
      extDeriv curvature x =
        -(connection x).continuousBilinearWedgeOneMany bracket 2
          (extDeriv connection x) := by
    change extDeriv
      ((extDeriv connection) + (1 / 2 : ℝ) • selfWedge) x = _
    rw [extDeriv_add derivative_differentiable
      (selfWedge_differentiable.const_smul (1 / 2 : ℝ)),
      extDeriv_fun_smul, extDeriv_extDeriv_apply connection_regular (by simp)]
    change 0 + (1 / 2 : ℝ) • extDeriv selfWedge x = _
    rw [show selfWedge = fun y =>
      (connection y).continuousBilinearWedgeOneMany bracket 1 (connection y) by rfl]
    rw [extDeriv_continuousBilinearSelfWedgeOne bracket
      (groupLieAlgebraCoordinateBracketCLM_skew (I := I) (G := G))
      connection (fderiv ℝ connection x) x connection_differentiable.hasFDerivAt]
    module
  rw [curvature_derivative]
  change -(connection x).continuousBilinearWedgeOneMany bracket 2
      (extDeriv connection x) +
    (connection x).continuousBilinearWedgeOneMany bracket 2
      (extDeriv connection x + (1 / 2 : ℝ) • selfWedge x) = 0
  rw [ContinuousAlternatingMap.continuousBilinearWedgeOneMany_add,
    ContinuousAlternatingMap.continuousBilinearWedgeOneMany_smul]
  rw [show selfWedge x =
    (connection x).continuousBilinearWedgeOneMany bracket 1 (connection x) by rfl,
    groupLieAlgebraCoordinateSelfWedge_cubic (I := I) (G := G)]
  simp

end YangMills.Mathematics
