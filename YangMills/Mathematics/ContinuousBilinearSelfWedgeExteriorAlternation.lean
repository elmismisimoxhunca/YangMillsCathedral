/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Mathematics.ContinuousBilinearWedgeCalculus
import YangMills.Mathematics.NormedSpaceExteriorDerivative

/-!
# Exterior alternation of a continuous bilinear self-wedge

For a skew continuous bilinear map `B` and a differentiable one-form-valued function `A`, this
module alternates the already-derived fixed-coefficient derivatives of `A ∧_B A`. The resulting
three-form value is exactly

`-2 • (A ∧_B dA)`.

The left side is deliberately named `continuousBilinearSelfWedgeExteriorAlternationAt`: it is the
explicit alternating sum of coefficient derivatives. Identifying it with Mathlib's `extDeriv` of
the whole self-wedge function still requires differentiability of that form-valued function and is
not claimed here. The actual finite-dimensional group coordinate bracket is proved skew and receives
an exact specialization.
-/

namespace YangMills.Mathematics

open scoped Manifold ContDiff

universe uT uV uE uH uG

variable
    {T : Type uT} [NormedAddCommGroup T] [NormedSpace ℝ T]
    {V : Type uV} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Exterior alternating sum of the fixed two-vector coefficient derivatives of the self-wedge. -/
noncomputable def continuousBilinearSelfWedgeExteriorAlternationAt
    (bilinear : V →L[ℝ] V →L[ℝ] V)
    (form : T → T [⋀^Fin 1]→L[ℝ] V) (x : T) (vectors : Fin 3 → T) : V :=
  ∑ i : Fin 3, (-1 : ℤ) ^ (i : ℕ) •
    fderiv ℝ
      (fun y => (form y).continuousBilinearWedgeOneMany bilinear 1 (form y)
        (i.removeNth vectors)) x (vectors i)

/-- Tuple-valued version of the self-wedge coefficient derivative rule. -/
theorem ContinuousAlternatingMap.continuousBilinearSelfWedgeOne_fderiv_tuple
    (bilinear : V →L[ℝ] V →L[ℝ] V)
    (form : T → T [⋀^Fin 1]→L[ℝ] V)
    (formDerivative : T →L[ℝ] (T [⋀^Fin 1]→L[ℝ] V))
    (x direction : T) (pair : Fin 2 → T)
    (form_hasDerivative : HasFDerivAt form formDerivative x) :
    fderiv ℝ
      (fun y => (form y).continuousBilinearWedgeOneMany bilinear 1 (form y) pair)
      x direction =
      (bilinear (form x (fun _ => pair 0))
          (formDerivative direction (fun _ => pair 1)) +
        bilinear (formDerivative direction (fun _ => pair 0))
          (form x (fun _ => pair 1))) -
      (bilinear (form x (fun _ => pair 1))
          (formDerivative direction (fun _ => pair 0)) +
        bilinear (formDerivative direction (fun _ => pair 1))
          (form x (fun _ => pair 0))) := by
  have pair_eq : pair = fun i => Fin.cases (pair 0) (fun _ => pair 1) i := by
    funext i
    fin_cases i <;> rfl
  rw [pair_eq]
  exact ContinuousAlternatingMap.continuousBilinearSelfWedgeOne_fderiv_apply
    bilinear form formDerivative x direction (pair 0) (pair 1) form_hasDerivative

/-- The exterior alternation of the self-wedge coefficient derivatives is exactly
`-2 • (A ∧_B dA)` for a skew continuous bilinear map. -/
theorem continuousBilinearSelfWedgeExteriorAlternationAt_eq_neg_two
    (bilinear : V →L[ℝ] V →L[ℝ] V)
    (skew : ∀ first second, bilinear first second = -bilinear second first)
    (form : T → T [⋀^Fin 1]→L[ℝ] V)
    (formDerivative : T →L[ℝ] (T [⋀^Fin 1]→L[ℝ] V))
    (x : T) (vectors : Fin 3 → T)
    (form_hasDerivative : HasFDerivAt form formDerivative x) :
    continuousBilinearSelfWedgeExteriorAlternationAt bilinear form x vectors =
      (-2 : ℝ) •
        (form x).continuousBilinearWedgeOneMany bilinear 2 (extDeriv form x) vectors := by
  have evaluated_derivative (vector direction : T) :
      fderiv ℝ (fun y => form y (fun _ => vector)) x direction =
        formDerivative direction (fun _ => vector) := by
    have derivative :=
      (continuousAlternatingOneFormEvaluation (V := V) vector).hasFDerivAt.comp
        x form_hasDerivative
    change fderiv ℝ
      ((continuousAlternatingOneFormEvaluation (V := V) vector) ∘ form) x direction = _
    rw [derivative.fderiv]
    rfl
  unfold continuousBilinearSelfWedgeExteriorAlternationAt
  rw [Fin.sum_univ_three]
  rw [ContinuousAlternatingMap.continuousBilinearSelfWedgeOne_fderiv_tuple
      bilinear form formDerivative x (vectors 0) (Fin.removeNth 0 vectors) form_hasDerivative,
    ContinuousAlternatingMap.continuousBilinearSelfWedgeOne_fderiv_tuple
      bilinear form formDerivative x (vectors 1) (Fin.removeNth 1 vectors) form_hasDerivative,
    ContinuousAlternatingMap.continuousBilinearSelfWedgeOne_fderiv_tuple
      bilinear form formDerivative x (vectors 2) (Fin.removeNth 2 vectors) form_hasDerivative]
  rw [ContinuousAlternatingMap.continuousBilinearWedgeOneMany_apply, Fin.sum_univ_three]
  have exterior_derivative_apply (pair : Fin 2 → T) :
      extDeriv form x pair =
        formDerivative (pair 0) (fun _ => pair 1) -
          formDerivative (pair 1) (fun _ => pair 0) := by
    rw [extDeriv_apply form_hasDerivative.differentiableAt, Fin.sum_univ_two]
    have remove_zero : Fin.removeNth 0 pair = fun _ : Fin 1 => pair 1 := by
      funext i
      fin_cases i
      rfl
    have remove_one : Fin.removeNth 1 pair = fun _ : Fin 1 => pair 0 := by
      funext i
      fin_cases i
      rfl
    rw [remove_zero, remove_one, evaluated_derivative, evaluated_derivative]
    simp [sub_eq_add_neg]
  simp_rw [exterior_derivative_apply]
  simp [Fin.removeNth]
  rw [show Fin.succAbove (2 : Fin 3) (1 : Fin 2) = (1 : Fin 3) by decide]
  rw [skew (formDerivative (vectors 0) (fun _ => vectors 1))
        (form x (fun _ => vectors 2)),
    skew (formDerivative (vectors 0) (fun _ => vectors 2))
        (form x (fun _ => vectors 1)),
    skew (formDerivative (vectors 1) (fun _ => vectors 2))
        (form x (fun _ => vectors 0)),
    skew (formDerivative (vectors 1) (fun _ => vectors 0))
        (form x (fun _ => vectors 2)),
    skew (formDerivative (vectors 2) (fun _ => vectors 0))
        (form x (fun _ => vectors 1)),
    skew (formDerivative (vectors 2) (fun _ => vectors 1))
        (form x (fun _ => vectors 0))]
  module

set_option backward.isDefEq.respectTransparency false in
/-- The canonical finite-dimensional group coordinate bracket is skew. -/
theorem groupLieAlgebraCoordinateBracketCLM_skew
    {E : Type uE} {H : Type uH}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {G : Type uG} [Group G] [TopologicalSpace G] [ChartedSpace H G]
    [LieGroup I (minSmoothness ℝ 3) G] (first second : E) :
    letI : CompleteSpace E := FiniteDimensional.complete ℝ E
    groupLieAlgebraCoordinateBracketCLM (I := I) (G := G) first second =
      -groupLieAlgebraCoordinateBracketCLM (I := I) (G := G) second first := by
  rw [groupLieAlgebraCoordinateBracketCLM_apply,
    groupLieAlgebraCoordinateBracketCLM_apply,
    ← lie_skew ((groupLieAlgebraModelEquiv (G := G) I).symm first)
      ((groupLieAlgebraModelEquiv (G := G) I).symm second), map_neg]

set_option backward.isDefEq.respectTransparency false in
/-- Exact specialization of self-wedge exterior alternation to the canonical transported group
Lie-algebra coordinate bracket. -/
theorem groupLieAlgebraCoordinateSelfWedgeExteriorAlternationAt_eq_neg_two
    {E : Type uE} {H : Type uH}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {G : Type uG} [Group G] [TopologicalSpace G] [ChartedSpace H G]
    [LieGroup I (minSmoothness ℝ 3) G]
    {T : Type uT} [NormedAddCommGroup T] [NormedSpace ℝ T]
    (form : T → T [⋀^Fin 1]→L[ℝ] E)
    (formDerivative : T →L[ℝ] (T [⋀^Fin 1]→L[ℝ] E))
    (x : T) (vectors : Fin 3 → T)
    (form_hasDerivative : HasFDerivAt form formDerivative x) :
    letI : CompleteSpace E := FiniteDimensional.complete ℝ E
    continuousBilinearSelfWedgeExteriorAlternationAt
        (groupLieAlgebraCoordinateBracketCLM (I := I) (G := G)) form x vectors =
      (-2 : ℝ) • (form x).continuousBilinearWedgeOneMany
        (groupLieAlgebraCoordinateBracketCLM (I := I) (G := G)) 2
        (extDeriv form x) vectors := by
  exact continuousBilinearSelfWedgeExteriorAlternationAt_eq_neg_two
    _ (groupLieAlgebraCoordinateBracketCLM_skew (I := I) (G := G))
    form formDerivative x vectors form_hasDerivative

end YangMills.Mathematics
