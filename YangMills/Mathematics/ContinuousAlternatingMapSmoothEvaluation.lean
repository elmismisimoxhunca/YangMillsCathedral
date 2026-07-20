/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Analysis.Normed.Module.Alternating.Uncurry.Fin

/-!
# Smooth families of continuous alternating maps from evaluations

For a finite-dimensional domain, smoothness of every fixed-tuple evaluation reconstructs smoothness
of a family valued in finite-arity continuous alternating maps. The proof handles arity zero
separately and reconstructs successors by currying and alternatization.
-/

namespace YangMills.Mathematics

open Set
open scoped ContDiff

noncomputable section

universe uD uE uF

variable {D : Type uD} [NormedAddCommGroup D] [NormedSpace ℝ D]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {F : Type uF} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A family of finite-dimensional-domain continuous alternating maps is smooth when all its
fixed-tuple evaluations are smooth. -/
theorem contDiffOn_continuousAlternatingMap_of_apply [FiniteDimensional ℝ E]
    {k : ℕ} {f : D → ContinuousAlternatingMap ℝ E F (Fin k)} {s : Set D}
    (h : ∀ v : Fin k → E, ContDiffOn ℝ ∞ (fun x => f x v) s) :
    ContDiffOn ℝ ∞ f s := by
  induction k with
  | zero =>
      let emptyTuple : Fin 0 → E := fun i => Fin.elim0 i
      have heval : ContDiffOn ℝ ∞ (fun x => f x emptyTuple) s := h emptyTuple
      have hreconstructed : ContDiffOn ℝ ∞
          ((ContinuousAlternatingMap.constOfIsEmptyLIE ℝ E F (Fin 0)) ∘
            (fun x => f x emptyTuple)) s :=
        (ContinuousAlternatingMap.constOfIsEmptyLIE ℝ E F (Fin 0)).contDiff.comp_contDiffOn heval
      exact hreconstructed.congr fun x hx => by
        apply ContinuousAlternatingMap.ext
        intro v
        have hv : v = emptyTuple := Subsingleton.elim _ _
        subst v
        simp [emptyTuple]
  | succ k ih =>
      have hcurried : ContDiffOn ℝ ∞ (fun x => (f x).curryLeft) s := by
        rw [contDiffOn_clm_apply]
        intro y
        apply ih
        intro v
        simpa only [ContinuousAlternatingMap.curryLeft_apply_apply] using
          h (Matrix.vecCons y v)
      have huncurried : ContDiffOn ℝ ∞
          ((ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ E F) ∘
            (fun x => (f x).curryLeft)) s :=
        (ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ E F).contDiff.comp_contDiffOn hcurried
      have hscaled : ContDiffOn ℝ ∞
          (fun x => ((k + 1 : ℕ) : ℝ)⁻¹ •
            ((ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ E F) ((f x).curryLeft))) s :=
        huncurried.const_smul (((k + 1 : ℕ) : ℝ)⁻¹)
      exact hscaled.congr fun x hx => by
        rw [ContinuousAlternatingMap.alternatizeUncurryFinCLM_apply]
        rw [ContinuousAlternatingMap.alternatizeUncurryFin_curryLeft]
        push_cast
        rw [← Nat.cast_smul_eq_nsmul ℝ, ← mul_smul]
        simp only [Nat.cast_add, Nat.cast_one]
        rw [inv_mul_cancel₀ (by positivity), one_smul]

end

end YangMills.Mathematics
