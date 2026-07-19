/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Mathematics.ContinuousBilinearSelfWedgeExteriorDerivative

/-!
# Hostile probes for the self-wedge exterior derivative

The probes lock the operator-norm bound, exact bundled wedge, derived whole-form differentiability,
the minus-two exterior-derivative identity, and its canonical group-coordinate specialization.
-/

namespace YangMills.Mathematics.ContinuousBilinearSelfWedgeExteriorDerivative.Probes

open scoped Manifold ContDiff

universe uT uV uE uH uG

variable
    {T : Type uT} [NormedAddCommGroup T] [NormedSpace ℝ T]
    {V : Type uV} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The exact degree-one wedge obeys the proved bilinear operator-norm bound. -/
theorem exact_operator_norm_bound
    (bilinear : V →L[ℝ] V →L[ℝ] V)
    (alpha beta : T [⋀^Fin 1]→L[ℝ] V) :
    ‖alpha.continuousBilinearWedgeOneMany bilinear 1 beta‖ ≤
      2 * ‖bilinear‖ * ‖alpha‖ * ‖beta‖ :=
  norm_continuousBilinearWedgeOneMany_one_le bilinear alpha beta

/-- Bundling as a curried continuous bilinear map does not change the wedge carrier. -/
theorem exact_bundled_wedge
    (bilinear : V →L[ℝ] V →L[ℝ] V)
    (alpha beta : T [⋀^Fin 1]→L[ℝ] V) :
    continuousBilinearWedgeOneCLM bilinear alpha beta =
      alpha.continuousBilinearWedgeOneMany bilinear 1 beta :=
  rfl

/-- Whole-form self-wedge differentiability is derived from the same input derivative. -/
theorem exact_whole_self_wedge_derivative
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (bilinear : V →L[ℝ] V →L[ℝ] V)
    (form : X → T [⋀^Fin 1]→L[ℝ] V)
    (formDerivative : X →L[ℝ] (T [⋀^Fin 1]→L[ℝ] V)) (x : X)
    (form_hasDerivative : HasFDerivAt form formDerivative x) :
    HasFDerivAt
      (fun y => (form y).continuousBilinearWedgeOneMany bilinear 1 (form y))
      ((continuousBilinearWedgeOneCLM bilinear).precompR X (form x) formDerivative +
        (continuousBilinearWedgeOneCLM bilinear).precompL X formDerivative (form x)) x :=
  ContinuousAlternatingMap.continuousBilinearSelfWedgeOne_hasFDerivAt
    bilinear form formDerivative x form_hasDerivative

/-- The full Mathlib exterior derivative has the exact minus-two self-wedge formula. -/
theorem exact_extDeriv_neg_two
    (bilinear : V →L[ℝ] V →L[ℝ] V)
    (skew : ∀ first second, bilinear first second = -bilinear second first)
    (form : T → T [⋀^Fin 1]→L[ℝ] V)
    (formDerivative : T →L[ℝ] (T [⋀^Fin 1]→L[ℝ] V)) (x : T)
    (form_hasDerivative : HasFDerivAt form formDerivative x) :
    extDeriv
      (fun y => (form y).continuousBilinearWedgeOneMany bilinear 1 (form y)) x =
      (-2 : ℝ) •
        (form x).continuousBilinearWedgeOneMany bilinear 2 (extDeriv form x) :=
  extDeriv_continuousBilinearSelfWedgeOne
    bilinear skew form formDerivative x form_hasDerivative

/-- Any wrong sign, factor, or output three-form conflicts with the exact identity. -/
theorem malformed_extDeriv_blocked
    (bilinear : V →L[ℝ] V →L[ℝ] V)
    (skew : ∀ first second, bilinear first second = -bilinear second first)
    (form : T → T [⋀^Fin 1]→L[ℝ] V)
    (formDerivative : T →L[ℝ] (T [⋀^Fin 1]→L[ℝ] V)) (x : T)
    (form_hasDerivative : HasFDerivAt form formDerivative x)
    (wrong : T [⋀^Fin 3]→L[ℝ] V)
    (different : wrong ≠ (-2 : ℝ) •
      (form x).continuousBilinearWedgeOneMany bilinear 2 (extDeriv form x))
    (claimed : extDeriv
      (fun y => (form y).continuousBilinearWedgeOneMany bilinear 1 (form y)) x = wrong) :
    False := by
  apply different
  exact claimed.symm.trans
    (extDeriv_continuousBilinearSelfWedgeOne
      bilinear skew form formDerivative x form_hasDerivative)

variable
    {E : Type uE} {H : Type uH}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {G : Type uG} [Group G] [TopologicalSpace G] [ChartedSpace H G]
    [LieGroup I (minSmoothness ℝ 3) G]

/-- The canonical transported group bracket satisfies the same exact exterior-derivative identity. -/
theorem exact_group_coordinate_extDeriv
    (form : T → T [⋀^Fin 1]→L[ℝ] E)
    (formDerivative : T →L[ℝ] (T [⋀^Fin 1]→L[ℝ] E)) (x : T)
    (form_hasDerivative : HasFDerivAt form formDerivative x) :
    letI : CompleteSpace E := FiniteDimensional.complete ℝ E
    extDeriv
      (fun y => (form y).continuousBilinearWedgeOneMany
        (groupLieAlgebraCoordinateBracketCLM (I := I) (G := G)) 1 (form y)) x =
      (-2 : ℝ) • (form x).continuousBilinearWedgeOneMany
        (groupLieAlgebraCoordinateBracketCLM (I := I) (G := G)) 2
        (extDeriv form x) :=
  extDeriv_groupLieAlgebraCoordinateSelfWedgeOne
    (I := I) (G := G) form formDerivative x form_hasDerivative

end YangMills.Mathematics.ContinuousBilinearSelfWedgeExteriorDerivative.Probes
