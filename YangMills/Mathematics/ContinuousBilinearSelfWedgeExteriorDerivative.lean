/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Mathematics.ContinuousBilinearSelfWedgeExteriorAlternation

/-!
# Exterior derivative of a continuous bilinear self-wedge

The degree-one wedge operation has operator norm at most
`2 ‖B‖ ‖α‖ ‖β‖`. This bound packages it as a curried continuous bilinear map between spaces of
continuous alternating forms. Mathlib's bounded-bilinear calculus then derives differentiability of
the whole self-wedge form-valued function from the same input derivative.

Combining that result with the previously proved coefficient alternation identifies the latter with
Mathlib's `extDeriv` and proves the exact local-model identity

`d(A ∧_B A) = -2 • (A ∧_B dA)`

for every skew continuous bilinear map. The canonical finite-dimensional group coordinate bracket
receives an exact specialization. This remains normed-space mathematics; no arbitrary-manifold,
covariant, or Bianchi theorem is asserted.
-/

namespace YangMills.Mathematics

open scoped Manifold ContDiff

universe uT uV uE uH uG

variable
    {T : Type uT} [NormedAddCommGroup T] [NormedSpace ℝ T]
    {V : Type uV} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Operator-norm bound for the degree-one continuous bilinear wedge. -/
theorem norm_continuousBilinearWedgeOneMany_one_le
    (bilinear : V →L[ℝ] V →L[ℝ] V)
    (alpha beta : T [⋀^Fin 1]→L[ℝ] V) :
    ‖alpha.continuousBilinearWedgeOneMany bilinear 1 beta‖ ≤
      2 * ‖bilinear‖ * ‖alpha‖ * ‖beta‖ := by
  refine ContinuousAlternatingMap.opNorm_le_bound
    (f := alpha.continuousBilinearWedgeOneMany bilinear 1 beta)
    (M := 2 * ‖bilinear‖ * ‖alpha‖ * ‖beta‖) (by positivity) ?_
  intro vectors
  rw [ContinuousAlternatingMap.continuousBilinearWedgeOneMany_one_apply,
    Fin.prod_univ_two]
  have first_term :
      ‖bilinear (alpha (fun _ => vectors 0)) (beta (fun _ => vectors 1))‖ ≤
        ‖bilinear‖ * ‖alpha‖ * ‖beta‖ * (‖vectors 0‖ * ‖vectors 1‖) := calc
    _ ≤ ‖bilinear‖ * ‖alpha (fun _ => vectors 0)‖ *
        ‖beta (fun _ => vectors 1)‖ := bilinear.le_opNorm₂ _ _
    _ ≤ ‖bilinear‖ * (‖alpha‖ * ‖vectors 0‖) *
        (‖beta‖ * ‖vectors 1‖) := by
      gcongr
      · simpa using alpha.le_opNorm (fun _ : Fin 1 => vectors 0)
      · simpa using beta.le_opNorm (fun _ : Fin 1 => vectors 1)
    _ = _ := by ring
  have second_term :
      ‖bilinear (alpha (fun _ => vectors 1)) (beta (fun _ => vectors 0))‖ ≤
        ‖bilinear‖ * ‖alpha‖ * ‖beta‖ * (‖vectors 0‖ * ‖vectors 1‖) := calc
    _ ≤ ‖bilinear‖ * ‖alpha (fun _ => vectors 1)‖ *
        ‖beta (fun _ => vectors 0)‖ := bilinear.le_opNorm₂ _ _
    _ ≤ ‖bilinear‖ * (‖alpha‖ * ‖vectors 1‖) *
        (‖beta‖ * ‖vectors 0‖) := by
      gcongr
      · simpa using alpha.le_opNorm (fun _ : Fin 1 => vectors 1)
      · simpa using beta.le_opNorm (fun _ : Fin 1 => vectors 0)
    _ = _ := by ring
  calc
    _ ≤ ‖bilinear (alpha (fun _ => vectors 0)) (beta (fun _ => vectors 1))‖ +
        ‖bilinear (alpha (fun _ => vectors 1)) (beta (fun _ => vectors 0))‖ :=
      norm_sub_le _ _
    _ ≤ _ := add_le_add first_term second_term
    _ = _ := by ring

/-- The degree-one wedge as a curried continuous bilinear map between alternating-form spaces. -/
noncomputable def continuousBilinearWedgeOneCLM
    (bilinear : V →L[ℝ] V →L[ℝ] V) :
    (T [⋀^Fin 1]→L[ℝ] V) →L[ℝ]
      (T [⋀^Fin 1]→L[ℝ] V) →L[ℝ] (T [⋀^Fin 2]→L[ℝ] V) := by
  let algebraic :
      (T [⋀^Fin 1]→L[ℝ] V) →ₗ[ℝ]
        (T [⋀^Fin 1]→L[ℝ] V) →ₗ[ℝ] (T [⋀^Fin 2]→L[ℝ] V) :=
    LinearMap.mk₂ ℝ
      (fun alpha beta => alpha.continuousBilinearWedgeOneMany bilinear 1 beta)
      (by intro; simp)
      (by intro; simp)
      (by intro; simp)
      (by intro; simp)
  exact algebraic.mkContinuous₂ (2 * ‖bilinear‖)
    (fun alpha beta => norm_continuousBilinearWedgeOneMany_one_le bilinear alpha beta)

/-- Exact evaluation of the bundled degree-one wedge. -/
@[simp]
theorem continuousBilinearWedgeOneCLM_apply
    (bilinear : V →L[ℝ] V →L[ℝ] V)
    (alpha beta : T [⋀^Fin 1]→L[ℝ] V) :
    continuousBilinearWedgeOneCLM bilinear alpha beta =
      alpha.continuousBilinearWedgeOneMany bilinear 1 beta :=
  rfl

/-- Differentiability of the whole self-wedge form-valued function is derived from the same exact
one-form-valued input derivative. -/
theorem ContinuousAlternatingMap.continuousBilinearSelfWedgeOne_hasFDerivAt
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (bilinear : V →L[ℝ] V →L[ℝ] V)
    (form : X → T [⋀^Fin 1]→L[ℝ] V)
    (formDerivative : X →L[ℝ] (T [⋀^Fin 1]→L[ℝ] V)) (x : X)
    (form_hasDerivative : HasFDerivAt form formDerivative x) :
    HasFDerivAt
      (fun y => (form y).continuousBilinearWedgeOneMany bilinear 1 (form y))
      ((continuousBilinearWedgeOneCLM bilinear).precompR X (form x) formDerivative +
        (continuousBilinearWedgeOneCLM bilinear).precompL X formDerivative (form x)) x := by
  simpa only [continuousBilinearWedgeOneCLM_apply] using
    (continuousBilinearWedgeOneCLM bilinear).hasFDerivAt_of_bilinear
      form_hasDerivative form_hasDerivative

/-- Exact normed-space self-wedge Leibniz identity. Whole-form differentiability is derived rather
than accepted as a separate witness. -/
theorem extDeriv_continuousBilinearSelfWedgeOne
    (bilinear : V →L[ℝ] V →L[ℝ] V)
    (skew : ∀ first second, bilinear first second = -bilinear second first)
    (form : T → T [⋀^Fin 1]→L[ℝ] V)
    (formDerivative : T →L[ℝ] (T [⋀^Fin 1]→L[ℝ] V)) (x : T)
    (form_hasDerivative : HasFDerivAt form formDerivative x) :
    extDeriv
      (fun y => (form y).continuousBilinearWedgeOneMany bilinear 1 (form y)) x =
      (-2 : ℝ) •
        (form x).continuousBilinearWedgeOneMany bilinear 2 (extDeriv form x) := by
  ext vectors
  rw [extDeriv_apply
    (ContinuousAlternatingMap.continuousBilinearSelfWedgeOne_hasFDerivAt
      bilinear form formDerivative x form_hasDerivative).differentiableAt]
  exact continuousBilinearSelfWedgeExteriorAlternationAt_eq_neg_two
    bilinear skew form formDerivative x vectors form_hasDerivative

set_option backward.isDefEq.respectTransparency false in
/-- Exact self-wedge exterior-derivative identity for the canonical transported finite-dimensional
group Lie-algebra coordinate bracket. -/
theorem extDeriv_groupLieAlgebraCoordinateSelfWedgeOne
    {E : Type uE} {H : Type uH}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {G : Type uG} [Group G] [TopologicalSpace G] [ChartedSpace H G]
    [LieGroup I (minSmoothness ℝ 3) G]
    {T : Type uT} [NormedAddCommGroup T] [NormedSpace ℝ T]
    (form : T → T [⋀^Fin 1]→L[ℝ] E)
    (formDerivative : T →L[ℝ] (T [⋀^Fin 1]→L[ℝ] E)) (x : T)
    (form_hasDerivative : HasFDerivAt form formDerivative x) :
    letI : CompleteSpace E := FiniteDimensional.complete ℝ E
    extDeriv
      (fun y => (form y).continuousBilinearWedgeOneMany
        (groupLieAlgebraCoordinateBracketCLM (I := I) (G := G)) 1 (form y)) x =
      (-2 : ℝ) • (form x).continuousBilinearWedgeOneMany
        (groupLieAlgebraCoordinateBracketCLM (I := I) (G := G)) 2
        (extDeriv form x) := by
  exact extDeriv_continuousBilinearSelfWedgeOne _
    (groupLieAlgebraCoordinateBracketCLM_skew (I := I) (G := G))
    form formDerivative x form_hasDerivative

end YangMills.Mathematics
