/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Mathematics.ContinuousAlternatingMapSmoothEvaluation

/-!
# Hostile probes for alternating-map smoothness reconstruction
-/

namespace YangMills.Mathematics.ContinuousAlternatingMapSmoothEvaluation.Probes

open Set
open scoped ContDiff

universe uD uE uF

variable {D : Type uD} [NormedAddCommGroup D] [NormedSpace ℝ D]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {F : Type uF} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Empty-arity reconstruction is covered explicitly. -/
theorem exact_arity_zero
    {f : D → ContinuousAlternatingMap ℝ E F (Fin 0)} {s : Set D}
    (h : ∀ v : Fin 0 → E, ContDiffOn ℝ ∞ (fun x => f x v) s) :
    ContDiffOn ℝ ∞ f s :=
  contDiffOn_continuousAlternatingMap_of_apply h

/-- Degree-two reconstruction exercises the successor curry/alternatization path. -/
theorem exact_arity_two
    {f : D → ContinuousAlternatingMap ℝ E F (Fin 2)} {s : Set D}
    (h : ∀ v : Fin 2 → E, ContDiffOn ℝ ∞ (fun x => f x v) s) :
    ContDiffOn ℝ ∞ f s :=
  contDiffOn_continuousAlternatingMap_of_apply h

/-- A claimed nonsmooth family contradicts smoothness of all exact fixed-tuple evaluations. -/
theorem nonsmooth_family_blocked
    {k : ℕ} {f : D → ContinuousAlternatingMap ℝ E F (Fin k)} {s : Set D}
    (h : ∀ v : Fin k → E, ContDiffOn ℝ ∞ (fun x => f x v) s)
    (wrong : ¬ ContDiffOn ℝ ∞ f s) : False :=
  wrong (contDiffOn_continuousAlternatingMap_of_apply h)

end YangMills.Mathematics.ContinuousAlternatingMapSmoothEvaluation.Probes
