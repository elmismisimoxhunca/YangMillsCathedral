/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Mathematics.ContinuousBilinearSelfWedgeExteriorDerivative

/-!
# Exterior derivative within a set of a continuous bilinear self-wedge

This module proves the within-set analogue of
`d(A ∧_B A) = -2 • (A ∧_B dA)`. All differentiability and uniqueness hypotheses remain explicit,
matching the local shape needed for manifold charts and manifolds with corners. Whole-wedge
within-set differentiability is derived from the same input one-form; no separate witness is
accepted.
-/

namespace YangMills.Mathematics

open Set

universe uT uV

variable
    {T : Type uT} [NormedAddCommGroup T] [NormedSpace ℝ T]
    {V : Type uV} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Exact within-set derivative of the self-wedge evaluated on an arbitrary two-vector tuple. -/
theorem ContinuousAlternatingMap.continuousBilinearSelfWedgeOne_fderivWithin_tuple
    (bilinear : V →L[ℝ] V →L[ℝ] V)
    (form : T → T [⋀^Fin 1]→L[ℝ] V) (s : Set T)
    (x direction : T) (pair : Fin 2 → T)
    (form_differentiable : DifferentiableWithinAt ℝ form s x)
    (unique : UniqueDiffWithinAt ℝ s x) :
    fderivWithin ℝ
      (fun y => (form y).continuousBilinearWedgeOneMany bilinear 1 (form y) pair)
      s x direction =
      (bilinear (form x (fun _ => pair 0))
          (fderivWithin ℝ form s x direction (fun _ => pair 1)) +
        bilinear (fderivWithin ℝ form s x direction (fun _ => pair 0))
          (form x (fun _ => pair 1))) -
      (bilinear (form x (fun _ => pair 1))
          (fderivWithin ℝ form s x direction (fun _ => pair 0)) +
        bilinear (fderivWithin ℝ form s x direction (fun _ => pair 1))
          (form x (fun _ => pair 0))) := by
  have pair_eq : pair = fun i => Fin.cases (pair 0) (fun _ => pair 1) i := by
    funext i
    fin_cases i <;> rfl
  rw [pair_eq]
  let eval_zero := continuousAlternatingOneFormEvaluation (V := V) (pair 0)
  let eval_one := continuousAlternatingOneFormEvaluation (V := V) (pair 1)
  have derivative_zero : HasFDerivWithinAt (fun y => form y (fun _ => pair 0))
      (eval_zero.comp (fderivWithin ℝ form s x)) s x :=
    eval_zero.hasFDerivAt.comp_hasFDerivWithinAt x
      form_differentiable.hasFDerivWithinAt
  have derivative_one : HasFDerivWithinAt (fun y => form y (fun _ => pair 1))
      (eval_one.comp (fderivWithin ℝ form s x)) s x :=
    eval_one.hasFDerivAt.comp_hasFDerivWithinAt x
      form_differentiable.hasFDerivWithinAt
  have forward := bilinear.hasFDerivWithinAt_of_bilinear derivative_zero derivative_one
  have reverse := bilinear.hasFDerivWithinAt_of_bilinear derivative_one derivative_zero
  have wedge_eq :
      (fun y => (form y).continuousBilinearWedgeOneMany bilinear 1 (form y)
        (fun i => Fin.cases (pair 0) (fun _ => pair 1) i)) =
      (fun y => bilinear (form y (fun _ => pair 0)) (form y (fun _ => pair 1)) -
        bilinear (form y (fun _ => pair 1)) (form y (fun _ => pair 0))) := by
    funext y
    rw [ContinuousAlternatingMap.continuousBilinearWedgeOneMany_one_apply]
    rfl
  rw [wedge_eq]
  change (fderivWithin ℝ
    ((fun y => bilinear (form y (fun _ => pair 0)) (form y (fun _ => pair 1))) -
     (fun y => bilinear (form y (fun _ => pair 1)) (form y (fun _ => pair 0))))
    s x) direction = _
  rw [(forward.sub reverse).fderivWithin unique]
  rfl

/-- Whole-form within-set differentiability of the self-wedge is derived from the same input form. -/
theorem ContinuousAlternatingMap.continuousBilinearSelfWedgeOne_differentiableWithinAt
    (bilinear : V →L[ℝ] V →L[ℝ] V)
    (form : T → T [⋀^Fin 1]→L[ℝ] V) (s : Set T) (x : T)
    (form_differentiable : DifferentiableWithinAt ℝ form s x) :
    DifferentiableWithinAt ℝ
      (fun y => (form y).continuousBilinearWedgeOneMany bilinear 1 (form y)) s x :=
  ((continuousBilinearWedgeOneCLM bilinear).hasFDerivWithinAt_of_bilinear
    form_differentiable.hasFDerivWithinAt
    form_differentiable.hasFDerivWithinAt).differentiableWithinAt

/-- Exact within-set self-wedge exterior-derivative identity. -/
theorem extDerivWithin_continuousBilinearSelfWedgeOne
    (bilinear : V →L[ℝ] V →L[ℝ] V)
    (skew : ∀ first second, bilinear first second = -bilinear second first)
    (form : T → T [⋀^Fin 1]→L[ℝ] V) (s : Set T) (x : T)
    (form_differentiable : DifferentiableWithinAt ℝ form s x)
    (unique : UniqueDiffWithinAt ℝ s x) :
    extDerivWithin
      (fun y => (form y).continuousBilinearWedgeOneMany bilinear 1 (form y)) s x =
      (-2 : ℝ) •
        (form x).continuousBilinearWedgeOneMany bilinear 2
          (extDerivWithin form s x) := by
  have self_differentiable :=
    ContinuousAlternatingMap.continuousBilinearSelfWedgeOne_differentiableWithinAt
      bilinear form s x form_differentiable
  ext vectors
  rw [extDerivWithin_apply self_differentiable unique, Fin.sum_univ_three]
  rw [ContinuousAlternatingMap.continuousBilinearSelfWedgeOne_fderivWithin_tuple
      bilinear form s x (vectors 0) (Fin.removeNth 0 vectors)
      form_differentiable unique,
    ContinuousAlternatingMap.continuousBilinearSelfWedgeOne_fderivWithin_tuple
      bilinear form s x (vectors 1) (Fin.removeNth 1 vectors)
      form_differentiable unique,
    ContinuousAlternatingMap.continuousBilinearSelfWedgeOne_fderivWithin_tuple
      bilinear form s x (vectors 2) (Fin.removeNth 2 vectors)
      form_differentiable unique]
  change _ = (-2 : ℝ) •
    ((form x).continuousBilinearWedgeOneMany bilinear 2
      (extDerivWithin form s x) vectors)
  rw [ContinuousAlternatingMap.continuousBilinearWedgeOneMany_apply, Fin.sum_univ_three]
  have evaluated_derivative (vector direction : T) :
      fderivWithin ℝ (fun y => form y (fun _ => vector)) s x direction =
        fderivWithin ℝ form s x direction (fun _ => vector) := by
    let evaluation := continuousAlternatingOneFormEvaluation (V := V) vector
    have derivative := evaluation.hasFDerivAt.comp_hasFDerivWithinAt
      x form_differentiable.hasFDerivWithinAt
    change (fderivWithin ℝ (evaluation ∘ form) s x) direction = _
    rw [derivative.fderivWithin unique]
    rfl
  have exterior_derivative_apply (pair : Fin 2 → T) :
      extDerivWithin form s x pair =
        fderivWithin ℝ form s x (pair 0) (fun _ => pair 1) -
          fderivWithin ℝ form s x (pair 1) (fun _ => pair 0) := by
    rw [extDerivWithin_apply form_differentiable unique, Fin.sum_univ_two]
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
  rw [skew (fderivWithin ℝ form s x (vectors 0) (fun _ => vectors 1))
        (form x (fun _ => vectors 2)),
    skew (fderivWithin ℝ form s x (vectors 0) (fun _ => vectors 2))
        (form x (fun _ => vectors 1)),
    skew (fderivWithin ℝ form s x (vectors 1) (fun _ => vectors 2))
        (form x (fun _ => vectors 0)),
    skew (fderivWithin ℝ form s x (vectors 1) (fun _ => vectors 0))
        (form x (fun _ => vectors 2)),
    skew (fderivWithin ℝ form s x (vectors 2) (fun _ => vectors 0))
        (form x (fun _ => vectors 1)),
    skew (fderivWithin ℝ form s x (vectors 2) (fun _ => vectors 1))
        (form x (fun _ => vectors 0))]
  module

end YangMills.Mathematics
