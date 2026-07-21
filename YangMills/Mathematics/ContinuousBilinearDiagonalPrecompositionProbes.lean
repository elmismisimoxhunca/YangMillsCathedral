/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Mathematics.ContinuousBilinearDiagonalPrecomposition

/-!
# Probes for continuous bilinear diagonal precomposition

The probes pin precomposition in both slots by one unchanged endomorphism and the exact
finite-dimensional smoothness result.
-/

namespace YangMills.Mathematics.ContinuousBilinearDiagonalPrecomposition.Probes

open scoped ContDiff

universe uE

noncomputable section

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Both arguments use the same exact supplied endomorphism. -/
theorem exact_both_slots
    (pairing : E →L[ℝ] E →L[ℝ] ℝ) (A : E →L[ℝ] E) (v w : E) :
    continuousBilinearDiagonalPrecomp pairing A v w = pairing (A v) (A w) :=
  rfl

/-- The bundled operation has exact finite-dimensional smoothness. -/
theorem exact_smoothness [FiniteDimensional ℝ E]
    (pairing : E →L[ℝ] E →L[ℝ] ℝ) :
    ContDiff ℝ ∞ (continuousBilinearDiagonalPrecomp pairing) :=
  continuousBilinearDiagonalPrecomp_contDiff pairing

/-- A replacement changing either precomposed slot is rejected whenever the values differ. -/
theorem changed_slot_blocked
    (pairing : E →L[ℝ] E →L[ℝ] ℝ) (A : E →L[ℝ] E) (v w : E) (wrong : ℝ)
    (different : wrong ≠ pairing (A v) (A w))
    (claimed : continuousBilinearDiagonalPrecomp pairing A v w = wrong) : False := by
  apply different
  rw [← claimed]
  rfl

end

end YangMills.Mathematics.ContinuousBilinearDiagonalPrecomposition.Probes
