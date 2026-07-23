/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Mathematics.UnitaryMatrixDualFiniteCharacterProjection

/-!
# Hostile probes for finite selected-character projections
-/

namespace YangMills
namespace Mathematics
namespace UnitaryMatrixDualFiniteCharacterProjection
namespace Probes

noncomputable section

universe uG

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]

omit [T2Space G] in
/-- The empty selected-character family gives exactly the zero projection and zero operator norm. -/
theorem exact_empty_projection :
    unitaryMatrixDualFiniteCharacterProjection (G := G) ∅ = 0 ∧
      ‖unitaryMatrixDualFiniteCharacterProjection (G := G) ∅‖ = 0 :=
  ⟨unitaryMatrixDualFiniteCharacterProjection_empty,
    norm_unitaryMatrixDualFiniteCharacterProjection_empty⟩

omit [T2Space G] in
/-- Hostile empty-family probe: assigning nonzero operator norm to the empty projection is
contradictory. -/
theorem nonzero_empty_projection_norm_blocked
    (nonzero : ‖unitaryMatrixDualFiniteCharacterProjection (G := G) ∅‖ ≠ 0) : False :=
  nonzero norm_unitaryMatrixDualFiniteCharacterProjection_empty

/-- Projection coefficients are exact finite coordinate truncation. -/
theorem exact_projection_coefficient
    (s : Finset (UnitaryMatrixDual G)) (f : NormalizedCompactHaarL2 G)
    (q : UnitaryMatrixDual G) :
    unitaryMatrixDualL2CharacterAnalysis q
      (unitaryMatrixDualFiniteCharacterProjection s f) =
      if q ∈ s then unitaryMatrixDualL2CharacterAnalysis q f else 0 :=
  unitaryMatrixDualL2CharacterAnalysis_projection s f q

/-- Hostile in-set coordinate probe: a projected coordinate cannot change. -/
theorem changed_in_set_projection_coefficient_blocked
    (s : Finset (UnitaryMatrixDual G)) (f : NormalizedCompactHaarL2 G)
    {q : UnitaryMatrixDual G} (hq : q ∈ s) {changed : ℂ}
    (hchanged : changed ≠ unitaryMatrixDualL2CharacterAnalysis q f)
    (changedCoordinate : unitaryMatrixDualL2CharacterAnalysis q
      (unitaryMatrixDualFiniteCharacterProjection s f) = changed) : False := by
  apply hchanged
  rw [← changedCoordinate, unitaryMatrixDualL2CharacterAnalysis_projection, if_pos hq]

/-- Hostile off-set coordinate probe: projected coordinates outside the finite set vanish. -/
theorem nonzero_off_set_projection_coefficient_blocked
    (s : Finset (UnitaryMatrixDual G)) (f : NormalizedCompactHaarL2 G)
    {q : UnitaryMatrixDual G} (hq : q ∉ s)
    (nonzero : unitaryMatrixDualL2CharacterAnalysis q
      (unitaryMatrixDualFiniteCharacterProjection s f) ≠ 0) : False := by
  apply nonzero
  rw [unitaryMatrixDualL2CharacterAnalysis_projection, if_neg hq]

/-- Every finite projection is exactly idempotent. -/
theorem exact_projection_idempotence
    (s : Finset (UnitaryMatrixDual G)) (f : NormalizedCompactHaarL2 G) :
    unitaryMatrixDualFiniteCharacterProjection s
      (unitaryMatrixDualFiniteCharacterProjection s f) =
      unitaryMatrixDualFiniteCharacterProjection s f :=
  unitaryMatrixDualFiniteCharacterProjection_idempotent s f

/-- Projection onto the exact coefficient support gives finite Fourier inversion. -/
theorem exact_support_inversion
    (c : UnitaryMatrixDualCharacterCoefficients G) :
    unitaryMatrixDualFiniteCharacterProjection c.support
      (unitaryMatrixDualL2CharacterSynthesis G c) =
      unitaryMatrixDualL2CharacterSynthesis G c :=
  unitaryMatrixDualFiniteCharacterProjection_support_synthesis c

/-- Hostile inversion probe: denying exact support inversion is contradictory. -/
theorem failed_support_inversion_blocked
    (c : UnitaryMatrixDualCharacterCoefficients G)
    (failed : unitaryMatrixDualFiniteCharacterProjection c.support
      (unitaryMatrixDualL2CharacterSynthesis G c) ≠
      unitaryMatrixDualL2CharacterSynthesis G c) : False :=
  failed (unitaryMatrixDualFiniteCharacterProjection_support_synthesis c)

/-- Every in-set character coefficient of the projection residual vanishes. -/
theorem exact_projection_residual_coordinate
    (s : Finset (UnitaryMatrixDual G)) (f : NormalizedCompactHaarL2 G)
    {q : UnitaryMatrixDual G} (hq : q ∈ s) :
    unitaryMatrixDualL2CharacterAnalysis q
      (f - unitaryMatrixDualFiniteCharacterProjection s f) = 0 :=
  unitaryMatrixDualL2CharacterAnalysis_projection_residual_eq_zero s f hq

/-- Projection and residual are exactly orthogonal. -/
theorem exact_projection_residual_orthogonality
    (s : Finset (UnitaryMatrixDual G)) (f : NormalizedCompactHaarL2 G) :
    inner ℂ (unitaryMatrixDualFiniteCharacterProjection s f)
      (f - unitaryMatrixDualFiniteCharacterProjection s f) = 0 :=
  inner_unitaryMatrixDualFiniteCharacterProjection_residual_eq_zero s f

/-- Hostile orthogonality probe: a nonzero projection-residual inner product is contradictory. -/
theorem nonorthogonal_projection_residual_blocked
    (s : Finset (UnitaryMatrixDual G)) (f : NormalizedCompactHaarL2 G)
    (nonzero : inner ℂ (unitaryMatrixDualFiniteCharacterProjection s f)
      (f - unitaryMatrixDualFiniteCharacterProjection s f) ≠ 0) : False :=
  nonzero (inner_unitaryMatrixDualFiniteCharacterProjection_residual_eq_zero s f)

/-- Exact finite Fourier Pythagorean remainder identity. -/
theorem exact_projection_Pythagorean_remainder
    (s : Finset (UnitaryMatrixDual G)) (f : NormalizedCompactHaarL2 G) :
    ‖f‖ ^ 2 =
      (∑ q ∈ s, ‖unitaryMatrixDualL2CharacterAnalysis q f‖ ^ 2) +
        ‖f - unitaryMatrixDualFiniteCharacterProjection s f‖ ^ 2 :=
  norm_sq_eq_sum_characterAnalysis_add_projection_residual s f

/-- Every finite Fourier projection is norm-nonincreasing. -/
theorem exact_projection_norm_contraction
    (s : Finset (UnitaryMatrixDual G)) (f : NormalizedCompactHaarL2 G) :
    ‖unitaryMatrixDualFiniteCharacterProjection s f‖ ≤ ‖f‖ :=
  norm_unitaryMatrixDualFiniteCharacterProjection_le s f

/-- The operator norm is at most one. -/
theorem exact_projection_operator_norm_le_one
    (s : Finset (UnitaryMatrixDual G)) :
    ‖unitaryMatrixDualFiniteCharacterProjection s‖ ≤ 1 :=
  norm_unitaryMatrixDualFiniteCharacterProjection_le_one s

/-- A nonempty finite character projection has operator norm exactly one. -/
theorem exact_nonempty_projection_operator_norm
    (s : Finset (UnitaryMatrixDual G)) (hs : s.Nonempty) :
    ‖unitaryMatrixDualFiniteCharacterProjection s‖ = 1 :=
  norm_unitaryMatrixDualFiniteCharacterProjection_eq_one s hs

/-- Hostile operator-normalization probe: changing the norm of a nonempty projection is
contradictory. -/
theorem changed_nonempty_projection_operator_norm_blocked
    (s : Finset (UnitaryMatrixDual G)) (hs : s.Nonempty) {changed : ℝ}
    (hchanged : changed ≠ 1)
    (changedNorm : ‖unitaryMatrixDualFiniteCharacterProjection s‖ = changed) : False := by
  apply hchanged
  rw [← changedNorm]
  exact norm_unitaryMatrixDualFiniteCharacterProjection_eq_one s hs

/-- Hostile contraction probe: norm expansion by a finite projection is contradictory. -/
theorem projection_norm_expansion_blocked
    (s : Finset (UnitaryMatrixDual G)) (f : NormalizedCompactHaarL2 G)
    (expanded : ‖f‖ < ‖unitaryMatrixDualFiniteCharacterProjection s f‖) : False :=
  (not_lt_of_ge (norm_unitaryMatrixDualFiniteCharacterProjection_le s f)) expanded

end

end Probes
end UnitaryMatrixDualFiniteCharacterProjection
end Mathematics
end YangMills
