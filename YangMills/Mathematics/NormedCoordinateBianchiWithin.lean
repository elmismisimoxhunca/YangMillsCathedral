/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Mathematics.ContinuousBilinearSelfWedgeExteriorDerivativeWithin
import YangMills.Mathematics.NormedCoordinateBianchi

/-!
# Bianchi identity within a normed-coordinate set

This module gives the within-set form of the finite-dimensional coordinate Bianchi theorem. It keeps
`ContDiffWithinAt`, `UniqueDiffOn`, membership, and closure-of-interior hypotheses explicit, so the
result can later serve honest manifold-chart and manifold-with-corners transport.

Curvature and the degree-two covariant exterior expression are again derived from the same one-form,
set, and canonical transported group bracket. No transport, curvature, derivative, or Bianchi
witness is accepted.
-/

namespace YangMills.Mathematics

open Set
open scoped Manifold ContDiff

universe uT uE uH uG

variable
    {T : Type uT} [NormedAddCommGroup T] [NormedSpace ℝ T]
    {E : Type uE} {H : Type uH}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {G : Type uG} [Group G] [TopologicalSpace G] [ChartedSpace H G]
    [LieGroup I (minSmoothness ℝ 3) G]

/-- Coordinate curvature using `extDerivWithin` on one explicit set. -/
noncomputable def groupLieAlgebraCoordinateCurvatureWithin
    (connection : T → T [⋀^Fin 1]→L[ℝ] E) (s : Set T) :
    T → T [⋀^Fin 2]→L[ℝ] E :=
  let bracket := groupLieAlgebraCoordinateBracketCLM (I := I) (G := G)
  fun x => extDerivWithin connection s x + (1 / 2 : ℝ) •
    (connection x).continuousBilinearWedgeOneMany bracket 1 (connection x)

/-- Degree-two covariant exterior expression using the same connection, set, and bracket. -/
noncomputable def groupLieAlgebraCoordinateCovariantExteriorDerivativeTwoWithin
    (connection : T → T [⋀^Fin 1]→L[ℝ] E) (s : Set T)
    (form : T → T [⋀^Fin 2]→L[ℝ] E) :
    T → T [⋀^Fin 3]→L[ℝ] E :=
  let bracket := groupLieAlgebraCoordinateBracketCLM (I := I) (G := G)
  fun x => extDerivWithin form s x +
    (connection x).continuousBilinearWedgeOneMany bracket 2 (form x)

/-- On `univ`, within-set curvature is exactly the earlier global coordinate curvature. -/
theorem groupLieAlgebraCoordinateCurvatureWithin_univ
    (connection : T → T [⋀^Fin 1]→L[ℝ] E) :
    groupLieAlgebraCoordinateCurvatureWithin (I := I) (G := G) connection Set.univ =
      groupLieAlgebraCoordinateCurvature (I := I) (G := G) connection := by
  funext x
  simp [groupLieAlgebraCoordinateCurvatureWithin,
    groupLieAlgebraCoordinateCurvature, extDerivWithin_univ]

/-- On `univ`, the within-set covariant expression is exactly the earlier global expression. -/
theorem groupLieAlgebraCoordinateCovariantExteriorDerivativeTwoWithin_univ
    (connection : T → T [⋀^Fin 1]→L[ℝ] E)
    (form : T → T [⋀^Fin 2]→L[ℝ] E) :
    groupLieAlgebraCoordinateCovariantExteriorDerivativeTwoWithin
        (I := I) (G := G) connection Set.univ form =
      groupLieAlgebraCoordinateCovariantExteriorDerivativeTwo
        (I := I) (G := G) connection form := by
  funext x
  simp [groupLieAlgebraCoordinateCovariantExteriorDerivativeTwoWithin,
    groupLieAlgebraCoordinateCovariantExteriorDerivativeTwo, extDerivWithin_univ]

set_option backward.isDefEq.respectTransparency false in
/-- Within-set normed-coordinate Bianchi identity. Every hypothesis is attached to the same set and
connection. -/
theorem groupLieAlgebraCoordinate_bianchiWithin
    (connection : T → T [⋀^Fin 1]→L[ℝ] E) (s : Set T) (x : T) {r : ℕ∞}
    (connection_regular : ContDiffWithinAt ℝ r connection s x)
    (regularity_order : minSmoothness ℝ 2 ≤ r)
    (unique_s : UniqueDiffOn ℝ s)
    (mem_closure_interior : x ∈ closure (interior s))
    (mem_s : x ∈ s) :
    letI : CompleteSpace E := FiniteDimensional.complete ℝ E
    groupLieAlgebraCoordinateCovariantExteriorDerivativeTwoWithin
      (I := I) (G := G) connection s
      (groupLieAlgebraCoordinateCurvatureWithin (I := I) (G := G) connection s) x = 0 := by
  dsimp only [groupLieAlgebraCoordinateCovariantExteriorDerivativeTwoWithin,
    groupLieAlgebraCoordinateCurvatureWithin]
  let bracket := groupLieAlgebraCoordinateBracketCLM (I := I) (G := G)
  let selfWedge : T → T [⋀^Fin 2]→L[ℝ] E := fun y =>
    (connection y).continuousBilinearWedgeOneMany bracket 1 (connection y)
  let curvature : T → T [⋀^Fin 2]→L[ℝ] E := fun y =>
    extDerivWithin connection s y + (1 / 2 : ℝ) • selfWedge y
  have unique := unique_s.uniqueDiffWithinAt mem_s
  have connection_differentiable : DifferentiableWithinAt ℝ connection s x :=
    connection_regular.differentiableWithinAt
      (ne_of_gt (lt_of_lt_of_le (by norm_num) regularity_order))
  have derivative_differentiable :
      DifferentiableWithinAt ℝ (extDerivWithin connection s) s x := by
    change DifferentiableWithinAt ℝ (fun y =>
      ContinuousAlternatingMap.alternatizeUncurryFin
        (fderivWithin ℝ connection s y)) s x
    apply (ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ T E).differentiableAt
      |>.comp_differentiableWithinAt x
    exact (connection_regular.fderivWithin_right unique_s
      (le_minSmoothness.trans regularity_order) mem_s).differentiableWithinAt one_ne_zero
  have selfWedge_differentiable : DifferentiableWithinAt ℝ selfWedge s x :=
    ((continuousBilinearWedgeOneCLM bracket).hasFDerivWithinAt_of_bilinear
      connection_differentiable.hasFDerivWithinAt
      connection_differentiable.hasFDerivWithinAt).differentiableWithinAt
  have curvature_derivative :
      extDerivWithin curvature s x =
        -(connection x).continuousBilinearWedgeOneMany bracket 2
          (extDerivWithin connection s x) := by
    change extDerivWithin
      ((extDerivWithin connection s) + (1 / 2 : ℝ) • selfWedge) s x = _
    rw [extDerivWithin_add unique derivative_differentiable
      (selfWedge_differentiable.const_smul (1 / 2 : ℝ)),
      extDerivWithin_smul (1 / 2 : ℝ) selfWedge unique,
      extDerivWithin_extDerivWithin_apply connection_regular regularity_order unique_s
        mem_closure_interior mem_s]
    change 0 + (1 / 2 : ℝ) • extDerivWithin selfWedge s x = _
    rw [show selfWedge = fun y =>
      (connection y).continuousBilinearWedgeOneMany bracket 1 (connection y) by rfl]
    rw [extDerivWithin_continuousBilinearSelfWedgeOne bracket
      (groupLieAlgebraCoordinateBracketCLM_skew (I := I) (G := G))
      connection s x connection_differentiable unique]
    module
  rw [curvature_derivative]
  change -(connection x).continuousBilinearWedgeOneMany bracket 2
      (extDerivWithin connection s x) +
    (connection x).continuousBilinearWedgeOneMany bracket 2
      (extDerivWithin connection s x + (1 / 2 : ℝ) • selfWedge x) = 0
  rw [ContinuousAlternatingMap.continuousBilinearWedgeOneMany_add,
    ContinuousAlternatingMap.continuousBilinearWedgeOneMany_smul]
  rw [show selfWedge x =
    (connection x).continuousBilinearWedgeOneMany bracket 1 (connection x) by rfl,
    groupLieAlgebraCoordinateSelfWedge_cubic (I := I) (G := G)]
  simp

end YangMills.Mathematics
