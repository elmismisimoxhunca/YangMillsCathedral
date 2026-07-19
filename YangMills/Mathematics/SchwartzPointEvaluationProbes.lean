/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Mathematics.SchwartzPointEvaluation

/-!
# Hostile probes for continuous Schwartz point evaluation

The probes require exact values, closed kernels, detection of every nonzero map, and determination
of the whole Schwartz map by its evaluations.
-/

namespace YangMills.Mathematics.SchwartzPointEvaluation.Probes

noncomputable section

variable {E F : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Continuous-linear evaluation cannot replace the selected point or function value. -/
theorem exact_point_evaluation (x : E) (f : SchwartzMap E F) :
    SchwartzMap.pointEvaluationCLM (F := F) x f = f x :=
  rfl

/-- Every point kernel is an actual closed subspace when values are Hausdorff. -/
theorem exact_closed_evaluation_kernel [T2Space F] (x : E) :
    IsClosed (LinearMap.ker
      (SchwartzMap.pointEvaluationCLM (F := F) x : SchwartzMap E F →ₗ[ℝ] F) :
        Set (SchwartzMap E F)) :=
  SchwartzMap.isClosed_pointEvaluationCLM_ker (F := F) x

/-- A nonzero Schwartz map cannot evade all point probes. -/
theorem nonzero_map_detected (f : SchwartzMap E F) (hf : f ≠ 0) :
    ∃ x : E, SchwartzMap.pointEvaluationCLM (F := F) x f ≠ 0 :=
  SchwartzMap.exists_pointEvaluationCLM_ne_zero f hf

/-- Disconnected replacement by a different function with identical point probes is blocked. -/
theorem all_evaluations_determine_map
    {f g : SchwartzMap E F}
    (h : ∀ x : E, SchwartzMap.pointEvaluationCLM (F := F) x f =
      SchwartzMap.pointEvaluationCLM (F := F) x g) :
    f = g :=
  SchwartzMap.eq_of_pointEvaluationCLM_eq h

end

end YangMills.Mathematics.SchwartzPointEvaluation.Probes
