/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Mathematics.ContinuousBilinearSelfWedgeExteriorDerivativeWithin

/-!
# Hostile probes for within-set self-wedge differentiation
-/

namespace YangMills.Mathematics.ContinuousBilinearSelfWedgeExteriorDerivativeWithin.Probes

open Set

universe uT uV

variable
    {T : Type uT} [NormedAddCommGroup T] [NormedSpace ℝ T]
    {V : Type uV} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The arbitrary tuple keeps all four exact within-set derivative slots. -/
theorem exact_tuple_fderivWithin
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
          (form x (fun _ => pair 0))) :=
  ContinuousAlternatingMap.continuousBilinearSelfWedgeOne_fderivWithin_tuple
    bilinear form s x direction pair form_differentiable unique

/-- Whole-wedge within-set differentiability is derived from the same input form. -/
theorem exact_derived_differentiability
    (bilinear : V →L[ℝ] V →L[ℝ] V)
    (form : T → T [⋀^Fin 1]→L[ℝ] V) (s : Set T) (x : T)
    (form_differentiable : DifferentiableWithinAt ℝ form s x) :
    DifferentiableWithinAt ℝ
      (fun y => (form y).continuousBilinearWedgeOneMany bilinear 1 (form y)) s x :=
  ContinuousAlternatingMap.continuousBilinearSelfWedgeOne_differentiableWithinAt
    bilinear form s x form_differentiable

/-- The exact within-set exterior derivative has coefficient `-2`. -/
theorem exact_extDerivWithin_neg_two
    (bilinear : V →L[ℝ] V →L[ℝ] V)
    (skew : ∀ first second, bilinear first second = -bilinear second first)
    (form : T → T [⋀^Fin 1]→L[ℝ] V) (s : Set T) (x : T)
    (form_differentiable : DifferentiableWithinAt ℝ form s x)
    (unique : UniqueDiffWithinAt ℝ s x) :
    extDerivWithin
      (fun y => (form y).continuousBilinearWedgeOneMany bilinear 1 (form y)) s x =
      (-2 : ℝ) •
        (form x).continuousBilinearWedgeOneMany bilinear 2
          (extDerivWithin form s x) :=
  extDerivWithin_continuousBilinearSelfWedgeOne
    bilinear skew form s x form_differentiable unique

/-- A malformed within-set exterior derivative is contradictory whenever it differs from the exact
minus-two expression. -/
theorem malformed_extDerivWithin_blocked
    (bilinear : V →L[ℝ] V →L[ℝ] V)
    (skew : ∀ first second, bilinear first second = -bilinear second first)
    (form : T → T [⋀^Fin 1]→L[ℝ] V) (s : Set T) (x : T)
    (form_differentiable : DifferentiableWithinAt ℝ form s x)
    (unique : UniqueDiffWithinAt ℝ s x)
    (wrong : T [⋀^Fin 3]→L[ℝ] V)
    (different : wrong ≠ (-2 : ℝ) •
      (form x).continuousBilinearWedgeOneMany bilinear 2
        (extDerivWithin form s x))
    (claimed : extDerivWithin
      (fun y => (form y).continuousBilinearWedgeOneMany bilinear 1 (form y)) s x = wrong) :
    False := by
  apply different
  exact claimed.symm.trans
    (extDerivWithin_continuousBilinearSelfWedgeOne
      bilinear skew form s x form_differentiable unique)

end YangMills.Mathematics.ContinuousBilinearSelfWedgeExteriorDerivativeWithin.Probes
