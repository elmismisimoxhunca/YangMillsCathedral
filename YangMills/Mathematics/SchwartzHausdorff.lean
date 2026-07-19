/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import Mathlib.Analysis.Distribution.SchwartzSpace.Basic

/-!
# Hausdorff separation of Schwartz space

Mathlib constructs the Schwartz topology from its standard seminorm family but does not currently
export separation-space instances. The zeroth Schwartz seminorm controls pointwise norm, so the
family separates every nonzero Schwartz map. The general `WithSeminorms.T1_of_separating` theorem
then supplies `T1Space`; the topological additive-group structure upgrades this to `T2Space`.

The structures are named rather than global instances, making this reusable infrastructure safe
against future Mathlib additions.
-/

namespace SchwartzMap

noncomputable section

variable {E F : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The standard Schwartz seminorm family separates every nonzero Schwartz map. -/
theorem exists_schwartzSeminorm_ne_zero (f : SchwartzMap E F) (hf : f ≠ 0) :
    ∃ m : ℕ × ℕ, schwartzSeminormFamily ℝ E F m f ≠ 0 := by
  refine ⟨(0, 0), ?_⟩
  intro hz
  apply hf
  ext x
  apply norm_eq_zero.mp
  apply le_antisymm
  · calc
      ‖f x‖ ≤ SchwartzMap.seminorm ℝ 0 0 f :=
        SchwartzMap.norm_le_seminorm ℝ f x
      _ = 0 := hz
  · exact norm_nonneg _

/-- Named `T1Space` structure for real Schwartz topology. -/
@[reducible]
noncomputable def t1Space : T1Space (SchwartzMap E F) := by
  apply (schwartz_withSeminorms ℝ E F).T1_of_separating
  intro f hf
  exact exists_schwartzSeminorm_ne_zero f hf

/-- Named Hausdorff structure for real Schwartz topology. -/
@[reducible]
noncomputable def t2Space : T2Space (SchwartzMap E F) := by
  letI : T1Space (SchwartzMap E F) := t1Space
  infer_instance

end

end SchwartzMap
