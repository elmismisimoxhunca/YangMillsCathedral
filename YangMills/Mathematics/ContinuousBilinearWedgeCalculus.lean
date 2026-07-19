/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Mathematics.ContinuousBilinearWedge

/-!
# Differential calculus for continuous bilinear self-wedge coefficients

Evaluation of a continuous alternating map on a fixed tuple is packaged as a continuous linear map.
Using this exact evaluation map and Mathlib's bounded-bilinear derivative rule, this module derives
the `HasFDerivAt` and evaluated `fderiv` of every fixed two-vector coefficient of
`A ∧_B A` from the derivative of the same one-form-valued function `A`.

This is the coefficient-level calculus needed before expanding the exterior derivative of the
self-wedge. It does not yet prove the exterior-derivative Leibniz identity or Bianchi.
-/

namespace YangMills.Mathematics

universe uT uV uX

variable
    {T : Type uT} [NormedAddCommGroup T] [NormedSpace ℝ T]
    {V : Type uV} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {X : Type uX} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- Evaluation of a continuous alternating map on one fixed tuple, as a continuous linear map on
the space of alternating maps. -/
noncomputable def continuousAlternatingMapEvaluation {n : ℕ} (vectors : Fin n → T) :
    (T [⋀^Fin n]→L[ℝ] V) →L[ℝ] V := by
  let linear : (T [⋀^Fin n]→L[ℝ] V) →ₗ[ℝ] V := {
    toFun := fun form => form vectors
    map_add' := by
      intro first second
      simp
    map_smul' := by
      intro scalar form
      simp
  }
  exact linear.mkContinuous (∏ i, ‖vectors i‖) (fun form => by
    rw [mul_comm]
    exact form.le_opNorm vectors)

/-- Exact evaluation of `continuousAlternatingMapEvaluation`. -/
@[simp]
theorem continuousAlternatingMapEvaluation_apply {n : ℕ} (vectors : Fin n → T)
    (form : T [⋀^Fin n]→L[ℝ] V) :
    continuousAlternatingMapEvaluation vectors form = form vectors :=
  rfl

/-- One-form evaluation at a fixed vector. -/
noncomputable def continuousAlternatingOneFormEvaluation (vector : T) :
    (T [⋀^Fin 1]→L[ℝ] V) →L[ℝ] V :=
  continuousAlternatingMapEvaluation (fun _ => vector)

/-- Exact one-form evaluation. -/
@[simp]
theorem continuousAlternatingOneFormEvaluation_apply (vector : T)
    (form : T [⋀^Fin 1]→L[ℝ] V) :
    continuousAlternatingOneFormEvaluation vector form = form (fun _ => vector) :=
  rfl

/-- The fixed `(u,v)` coefficient of the self-wedge has a derivative derived solely from the exact
one-form-valued input derivative. The four product-rule terms retain their exact slots. -/
theorem ContinuousAlternatingMap.continuousBilinearSelfWedgeOne_hasFDerivAt_apply
    (bilinear : V →L[ℝ] V →L[ℝ] V)
    (form : X → T [⋀^Fin 1]→L[ℝ] V)
    (formDerivative : X →L[ℝ] (T [⋀^Fin 1]→L[ℝ] V))
    (x : X) (u v : T) (form_hasDerivative : HasFDerivAt form formDerivative x) :
    HasFDerivAt
      (fun y => (form y).continuousBilinearWedgeOneMany bilinear 1 (form y)
        (fun i => Fin.cases u (fun _ => v) i))
      ((bilinear.precompR X (form x (fun _ => u))
          ((continuousAlternatingOneFormEvaluation (V := V) v).comp formDerivative) +
        bilinear.precompL X
          ((continuousAlternatingOneFormEvaluation (V := V) u).comp formDerivative)
          (form x (fun _ => v))) -
       (bilinear.precompR X (form x (fun _ => v))
          ((continuousAlternatingOneFormEvaluation (V := V) u).comp formDerivative) +
        bilinear.precompL X
          ((continuousAlternatingOneFormEvaluation (V := V) v).comp formDerivative)
          (form x (fun _ => u)))) x := by
  have derivative_u : HasFDerivAt (fun y => form y (fun _ => u))
      ((continuousAlternatingOneFormEvaluation (V := V) u).comp formDerivative) x :=
    (continuousAlternatingOneFormEvaluation (V := V) u).hasFDerivAt.comp
      x form_hasDerivative
  have derivative_v : HasFDerivAt (fun y => form y (fun _ => v))
      ((continuousAlternatingOneFormEvaluation (V := V) v).comp formDerivative) x :=
    (continuousAlternatingOneFormEvaluation (V := V) v).hasFDerivAt.comp
      x form_hasDerivative
  have first_order := bilinear.hasFDerivAt_of_bilinear derivative_u derivative_v
  have reverse_order := bilinear.hasFDerivAt_of_bilinear derivative_v derivative_u
  have wedge_eq :
      (fun y => (form y).continuousBilinearWedgeOneMany bilinear 1 (form y)
        (fun i => Fin.cases u (fun _ => v) i)) =
      (fun y => bilinear (form y (fun _ => u)) (form y (fun _ => v)) -
        bilinear (form y (fun _ => v)) (form y (fun _ => u))) := by
    funext y
    rw [ContinuousAlternatingMap.continuousBilinearWedgeOneMany_one_apply]
    rfl
  rw [wedge_eq]
  exact first_order.sub reverse_order

/-- Evaluation of the exact four-term `fderiv` formula in a source direction. -/
theorem ContinuousAlternatingMap.continuousBilinearSelfWedgeOne_fderiv_apply
    (bilinear : V →L[ℝ] V →L[ℝ] V)
    (form : X → T [⋀^Fin 1]→L[ℝ] V)
    (formDerivative : X →L[ℝ] (T [⋀^Fin 1]→L[ℝ] V))
    (x direction : X) (u v : T)
    (form_hasDerivative : HasFDerivAt form formDerivative x) :
    fderiv ℝ
      (fun y => (form y).continuousBilinearWedgeOneMany bilinear 1 (form y)
        (fun i => Fin.cases u (fun _ => v) i)) x direction =
      (bilinear (form x (fun _ => u)) (formDerivative direction (fun _ => v)) +
        bilinear (formDerivative direction (fun _ => u)) (form x (fun _ => v))) -
      (bilinear (form x (fun _ => v)) (formDerivative direction (fun _ => u)) +
        bilinear (formDerivative direction (fun _ => v)) (form x (fun _ => u))) := by
  rw [(ContinuousAlternatingMap.continuousBilinearSelfWedgeOne_hasFDerivAt_apply
    bilinear form formDerivative x u v form_hasDerivative).fderiv]
  rfl

end YangMills.Mathematics
