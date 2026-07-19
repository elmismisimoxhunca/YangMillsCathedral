/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import Mathlib.Analysis.Distribution.TemperedDistribution

/-!
# Continuous directional-jet evaluation on Schwartz space

This module packages evaluation of an iterated real directional derivative of a complex Schwartz
function as a continuous complex-linear functional. It is reusable functional-analysis
infrastructure: continuity comes from Mathlib's continuous iterated line-derivative operator and
the tempered delta distribution. No Yang–Mills or Osterwalder–Schrader assumption appears here.
-/

namespace SchwartzMap

open LineDeriv

noncomputable section

/-- Evaluate the `k`-fold real directional derivative of a complex Schwartz function at one point,
packaged as a continuous complex-linear functional on the exact Schwartz topology. -/
def iteratedDirectionalEvaluationCLM
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {k : ℕ} (directions : Fin k → E) (x : E) :
    SchwartzMap E ℂ →L[ℂ] ℂ :=
  (TemperedDistribution.delta x).comp
    (LineDeriv.iteratedLineDerivOpCLM ℂ (SchwartzMap E ℂ) directions)

/-- The bundled functional evaluates the exact iterated Fréchet derivative on the supplied ordered
direction tuple. -/
@[simp]
theorem iteratedDirectionalEvaluationCLM_apply
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {k : ℕ} (directions : Fin k → E) (x : E) (f : SchwartzMap E ℂ) :
    iteratedDirectionalEvaluationCLM directions x f =
      iteratedFDeriv ℝ k (f : E → ℂ) x directions := by
  change TemperedDistribution.delta x (∂^{directions} f) = _
  rw [TemperedDistribution.delta_apply,
    SchwartzMap.iteratedLineDerivOp_eq_iteratedFDeriv]

/-- Vanishing of one exact directional jet cuts out a closed complex Schwartz subspace. -/
theorem isClosed_iteratedDirectionalEvaluationCLM_ker
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {k : ℕ} (directions : Fin k → E) (x : E) :
    IsClosed (((iteratedDirectionalEvaluationCLM directions x).ker :
      Submodule ℂ (SchwartzMap E ℂ)) : Set (SchwartzMap E ℂ)) :=
  (iteratedDirectionalEvaluationCLM directions x).isClosed_ker

end

end SchwartzMap
