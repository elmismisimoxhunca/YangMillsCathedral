/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Mathematics.MixedPartialLieBracket

namespace YangMills.Mathematics.MixedPartialLieBracket.Probes

open Set
open scoped ContDiff

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Unrestricted Schwarz symmetry gives the exact mixed-partial bracket cancellation. -/
theorem exact_global_cancellation
    (F : E × E → E) (a X Y : E) (hF : ContDiffAt ℝ 2 F (a, a))
    (hsecond : fderiv ℝ F (a, a) (0, X) = X)
    (hfirst : fderiv ℝ F (a, a) (Y, 0) = Y) :
    VectorField.lieBracket ℝ
      (fun x => fderiv ℝ F (x, a) (0, X))
      (fun x => fderiv ℝ F (a, x) (Y, 0)) a = 0 :=
  lieBracket_mixed_partial_eq_zero F a X Y hF hsecond hfirst

/-- The corner-safe theorem retains the exact set and within derivatives. -/
theorem exact_within_cancellation
    (F : E × E → E) (t : Set E) (a X Y : E)
    (ht : UniqueDiffOn ℝ t) (ha : a ∈ t)
    (haa : (a, a) ∈ closure (interior (t ×ˢ t)))
    (hF : ContDiffWithinAt ℝ 2 F (t ×ˢ t) (a, a))
    (hsecond : fderivWithin ℝ F (t ×ˢ t) (a, a) (0, X) = X)
    (hfirst : fderivWithin ℝ F (t ×ˢ t) (a, a) (Y, 0) = Y) :
    VectorField.lieBracketWithin ℝ
      (fun x => fderivWithin ℝ F (t ×ˢ t) (x, a) (0, X))
      (fun x => fderivWithin ℝ F (t ×ˢ t) (a, x) (Y, 0)) t a = 0 :=
  lieBracketWithin_mixed_partial_eq_zero F t a X Y ht ha haa hF hsecond hfirst

/-- A nonzero mixed-partial bracket contradicts the exact within-set hypotheses. -/
theorem nonzero_within_bracket_blocked
    (F : E × E → E) (t : Set E) (a X Y : E)
    (ht : UniqueDiffOn ℝ t) (ha : a ∈ t)
    (haa : (a, a) ∈ closure (interior (t ×ˢ t)))
    (hF : ContDiffWithinAt ℝ 2 F (t ×ˢ t) (a, a))
    (hsecond : fderivWithin ℝ F (t ×ˢ t) (a, a) (0, X) = X)
    (hfirst : fderivWithin ℝ F (t ×ˢ t) (a, a) (Y, 0) = Y)
    (nonzero : VectorField.lieBracketWithin ℝ
      (fun x => fderivWithin ℝ F (t ×ˢ t) (x, a) (0, X))
      (fun x => fderivWithin ℝ F (t ×ˢ t) (a, x) (Y, 0)) t a ≠ 0) : False :=
  nonzero (lieBracketWithin_mixed_partial_eq_zero F t a X Y
    ht ha haa hF hsecond hfirst)

end

end YangMills.Mathematics.MixedPartialLieBracket.Probes
