/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Mathematics.ContinuousBilinearWedgeCalculus

/-!
# Hostile probes for continuous bilinear self-wedge calculus

These probes lock exact tuple evaluation, the derived same-input `HasFDerivAt` rule, all four
product-rule slots, and rejection of malformed or unrelated derivative outputs.
-/

namespace YangMills.Mathematics.ContinuousBilinearWedgeCalculus.Probes

universe uT uV uX

variable
    {T : Type uT} [NormedAddCommGroup T] [NormedSpace ℝ T]
    {V : Type uV} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {X : Type uX} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- The continuous evaluation map retains the exact tuple and form. -/
theorem exact_tuple_evaluation {n : ℕ} (vectors : Fin n → T)
    (form : T [⋀^Fin n]→L[ℝ] V) :
    continuousAlternatingMapEvaluation vectors form = form vectors :=
  rfl

/-- The coefficient derivative is derived from the exact same one-form-valued input derivative. -/
theorem exact_self_wedge_hasFDerivAt
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
          (form x (fun _ => u)))) x :=
  ContinuousAlternatingMap.continuousBilinearSelfWedgeOne_hasFDerivAt_apply
    bilinear form formDerivative x u v form_hasDerivative

/-- The evaluated derivative contains exactly the two forward-order and two reverse-order terms. -/
theorem exact_four_term_fderiv
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
        bilinear (formDerivative direction (fun _ => v)) (form x (fun _ => u))) :=
  ContinuousAlternatingMap.continuousBilinearSelfWedgeOne_fderiv_apply
    bilinear form formDerivative x direction u v form_hasDerivative

/-- A derivative output with a missing, swapped, or sign-changed term is rejected whenever it differs
from the exact four-term expression. -/
theorem malformed_derivative_blocked
    (bilinear : V →L[ℝ] V →L[ℝ] V)
    (form : X → T [⋀^Fin 1]→L[ℝ] V)
    (formDerivative : X →L[ℝ] (T [⋀^Fin 1]→L[ℝ] V))
    (x direction : X) (u v : T)
    (form_hasDerivative : HasFDerivAt form formDerivative x)
    (wrong : V)
    (different : wrong ≠
      (bilinear (form x (fun _ => u)) (formDerivative direction (fun _ => v)) +
        bilinear (formDerivative direction (fun _ => u)) (form x (fun _ => v))) -
      (bilinear (form x (fun _ => v)) (formDerivative direction (fun _ => u)) +
        bilinear (formDerivative direction (fun _ => v)) (form x (fun _ => u))))
    (claimed : fderiv ℝ
      (fun y => (form y).continuousBilinearWedgeOneMany bilinear 1 (form y)
        (fun i => Fin.cases u (fun _ => v) i)) x direction = wrong) : False := by
  apply different
  exact claimed.symm.trans
    (ContinuousAlternatingMap.continuousBilinearSelfWedgeOne_fderiv_apply
      bilinear form formDerivative x direction u v form_hasDerivative)

end YangMills.Mathematics.ContinuousBilinearWedgeCalculus.Probes
