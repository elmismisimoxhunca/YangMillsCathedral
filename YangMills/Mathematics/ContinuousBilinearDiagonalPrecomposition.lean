/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps

/-!
# Smooth diagonal precomposition of a continuous bilinear map

For a fixed continuous bilinear map `B`, this module bundles the operation sending a continuous
linear endomorphism `A` to `(v, w) ↦ B (A v) (A w)`. In finite dimensions this operation is smooth
as a map into the nested continuous-linear-map space.

The proof deliberately uses Mathlib's finite-dimensional characterization of smooth families of
continuous linear maps by all evaluations. This avoids imposing an accidental topology through a
higher-order continuous-linear-map instance.
-/

namespace YangMills.Mathematics

open scoped ContDiff

universe uE

noncomputable section

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Precompose both arguments of a continuous bilinear map by the same continuous linear
endomorphism. -/
noncomputable def continuousBilinearDiagonalPrecomp
    (pairing : E →L[ℝ] E →L[ℝ] ℝ) (A : E →L[ℝ] E) :
    E →L[ℝ] E →L[ℝ] ℝ :=
  ContinuousLinearMap.compL ℝ E (E →L[ℝ] ℝ) (E →L[ℝ] ℝ)
    ((ContinuousLinearMap.compL ℝ E E ℝ).flip A)
    (ContinuousLinearMap.compL ℝ E E (E →L[ℝ] ℝ) pairing A)

@[simp]
theorem continuousBilinearDiagonalPrecomp_apply
    (pairing : E →L[ℝ] E →L[ℝ] ℝ) (A : E →L[ℝ] E) (v w : E) :
    continuousBilinearDiagonalPrecomp pairing A v w = pairing (A v) (A w) :=
  rfl

/-- In finite dimensions, diagonal precomposition of a fixed continuous bilinear map varies
smoothly with the endomorphism. -/
theorem continuousBilinearDiagonalPrecomp_contDiff
    [FiniteDimensional ℝ E] (pairing : E →L[ℝ] E →L[ℝ] ℝ) :
    ContDiff ℝ ∞ (continuousBilinearDiagonalPrecomp pairing) := by
  rw [contDiff_clm_apply_iff]
  intro v
  rw [contDiff_clm_apply_iff]
  intro w
  have hv : ContDiff ℝ ∞ (fun A : E →L[ℝ] E => A v) :=
    contDiff_id.clm_apply contDiff_const
  have hw : ContDiff ℝ ∞ (fun A : E →L[ℝ] E => A w) :=
    contDiff_id.clm_apply contDiff_const
  exact (contDiff_const.clm_apply hv).clm_apply hw

end

end YangMills.Mathematics
