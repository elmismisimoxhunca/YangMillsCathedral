/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Mathematics.SchwartzHausdorff
import Mathlib.Analysis.LocallyConvex.WithSeminorms

/-!
# Continuous point evaluation on Schwartz space

Point evaluation is controlled by the zeroth standard Schwartz seminorm. This module packages
point evaluation as a continuous real-linear map on arbitrary real Schwartz spaces and proves that
these maps separate Schwartz functions. The result is reusable infrastructure for closed
support-vanishing submodules and half-line quotient constructions.
-/

namespace SchwartzMap

noncomputable section

variable {E F : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Real-linear evaluation of a Schwartz map at one point. -/
def pointEvaluationLinearMap (x : E) : SchwartzMap E F →ₗ[ℝ] F where
  toFun f := f x
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Point evaluation is continuous because pointwise norm is bounded by the zeroth Schwartz
seminorm. -/
theorem continuous_pointEvaluationLinearMap (x : E) :
    Continuous (pointEvaluationLinearMap (F := F) x) := by
  apply WithSeminorms.continuous_normedSpace_rng (𝕝 := ℝ) (𝕝₂ := ℝ)
    (τ₁₂ := RingHom.id ℝ) F (schwartz_withSeminorms ℝ E F)
  refine ⟨{(0, 0)}, 1, ?_⟩
  intro f
  simp only [Seminorm.comp_apply, pointEvaluationLinearMap, one_smul,
    Finset.sup_singleton, schwartzSeminormFamily_apply]
  exact norm_le_seminorm ℝ f x

/-- Continuous real-linear point evaluation. -/
noncomputable def pointEvaluationCLM (x : E) : SchwartzMap E F →L[ℝ] F :=
  { pointEvaluationLinearMap (F := F) x with
    cont := continuous_pointEvaluationLinearMap (F := F) x }

/-- Continuous-linear packaging preserves exact evaluation. -/
@[simp]
theorem pointEvaluationCLM_apply (x : E) (f : SchwartzMap E F) :
    pointEvaluationCLM (F := F) x f = f x :=
  rfl

/-- Every point-evaluation kernel is closed when the codomain is Hausdorff. -/
theorem isClosed_pointEvaluationCLM_ker [T2Space F] (x : E) :
    IsClosed (LinearMap.ker (pointEvaluationCLM (F := F) x : SchwartzMap E F →ₗ[ℝ] F) :
      Set (SchwartzMap E F)) :=
  (pointEvaluationCLM (F := F) x).isClosed_ker

/-- A nonzero Schwartz map is detected by at least one point evaluation. -/
theorem exists_pointEvaluationCLM_ne_zero (f : SchwartzMap E F) (hf : f ≠ 0) :
    ∃ x : E, pointEvaluationCLM (F := F) x f ≠ 0 := by
  by_contra h
  push Not at h
  apply hf
  ext x
  exact h x

/-- Equality of all point evaluations determines the exact Schwartz map. -/
theorem eq_of_pointEvaluationCLM_eq
    {f g : SchwartzMap E F}
    (h : ∀ x : E, pointEvaluationCLM (F := F) x f =
      pointEvaluationCLM (F := F) x g) :
    f = g := by
  ext x
  exact h x

end

end SchwartzMap
