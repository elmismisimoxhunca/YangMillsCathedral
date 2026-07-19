/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Mathematics.SchwartzHausdorff

/-!
# Hostile probes for Schwartz-space Hausdorff separation

The probes require a seminorm to detect every nonzero map and disjoint open neighborhoods to
separate every unequal pair.
-/

namespace YangMills.Mathematics.SchwartzHausdorff.Probes

noncomputable section

variable {E F : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- No nonzero Schwartz map can vanish under the whole defining seminorm family. -/
theorem nonzero_detected_by_standard_seminorm
    (f : SchwartzMap E F) (hf : f ≠ 0) :
    ∃ m : ℕ × ℕ, schwartzSeminormFamily ℝ E F m f ≠ 0 :=
  SchwartzMap.exists_schwartzSeminorm_ne_zero f hf

/-- Installing the named `T1Space` makes every exact singleton closed. -/
theorem exact_singleton_closed (f : SchwartzMap E F) :
    letI : T1Space (SchwartzMap E F) := SchwartzMap.t1Space
    IsClosed ({f} : Set (SchwartzMap E F)) := by
  letI : T1Space (SchwartzMap E F) := SchwartzMap.t1Space
  exact isClosed_singleton

/-- Installing the named Hausdorff structure separates every unequal pair by disjoint opens. -/
theorem exact_disjoint_open_separation
    (f g : SchwartzMap E F) (hfg : f ≠ g) :
    letI : T2Space (SchwartzMap E F) := SchwartzMap.t2Space
    ∃ U V : Set (SchwartzMap E F),
      IsOpen U ∧ IsOpen V ∧ f ∈ U ∧ g ∈ V ∧ Disjoint U V := by
  letI : T2Space (SchwartzMap E F) := SchwartzMap.t2Space
  exact t2_separation hfg

end

end YangMills.Mathematics.SchwartzHausdorff.Probes
