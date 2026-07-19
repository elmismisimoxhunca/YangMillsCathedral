/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Mathematics.SchwartzDirectionalEvaluation

/-!
# Hostile probes for continuous Schwartz directional-jet evaluation

The probes ensure that the bundled functional remains tied to the exact point, ordered direction
tuple, and iterated Fréchet derivative rather than to an unrelated continuous functional.
-/

namespace SchwartzMap.DirectionalEvaluation.Probes

noncomputable section

/-- The continuous functional cannot be disconnected from the designated directional jet. -/
theorem exact_directional_jet
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {k : ℕ} (directions : Fin k → E) (x : E) (f : SchwartzMap E ℂ) :
    SchwartzMap.iteratedDirectionalEvaluationCLM directions x f =
      iteratedFDeriv ℝ k (f : E → ℂ) x directions :=
  SchwartzMap.iteratedDirectionalEvaluationCLM_apply directions x f

/-- Kernel membership is exactly vanishing of the selected jet, not a disconnected witness. -/
theorem exact_kernel_membership
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {k : ℕ} (directions : Fin k → E) (x : E) (f : SchwartzMap E ℂ) :
    f ∈ (SchwartzMap.iteratedDirectionalEvaluationCLM directions x).ker ↔
      iteratedFDeriv ℝ k (f : E → ℂ) x directions = 0 := by
  change SchwartzMap.iteratedDirectionalEvaluationCLM directions x f = 0 ↔ _
  rw [SchwartzMap.iteratedDirectionalEvaluationCLM_apply]

/-- A nonzero selected jet is rejected from the exact kernel. -/
theorem nonzero_jet_blocked
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {k : ℕ} (directions : Fin k → E) (x : E) (f : SchwartzMap E ℂ)
    (hne : iteratedFDeriv ℝ k (f : E → ℂ) x directions ≠ 0) :
    f ∉ (SchwartzMap.iteratedDirectionalEvaluationCLM directions x).ker := by
  rw [exact_kernel_membership]
  exact hne

end

end SchwartzMap.DirectionalEvaluation.Probes
