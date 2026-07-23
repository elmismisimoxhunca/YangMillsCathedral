/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Mathematics.UnitaryMatrixDualCharacterBessel

/-!
# Finite selected-character Fourier projections

For every finite set `s` of selected irreducible classes, this file constructs the bounded linear
operator

`P_s f = ∑ q ∈ s, ⟪χ_q, f⟫ χ_q`.

It proves exact coordinate truncation, idempotence, exact finite-synthesis inversion when the
support lies in `s`, residual orthogonality, the finite Parseval norm formula, and the Pythagorean
remainder identity. This is a genuine finite orthogonal Fourier projection.

No countable ordering, limit of projections, density, completeness, or infinite inversion theorem is
assumed or derived.
-/

namespace YangMills
namespace Mathematics

noncomputable section

universe uG

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]

/-- Bounded linear projection onto the span of a finite set of selected irreducible characters. -/
noncomputable def unitaryMatrixDualFiniteCharacterProjection
    (s : Finset (UnitaryMatrixDual G)) :
    NormalizedCompactHaarL2 G →L[ℂ] NormalizedCompactHaarL2 G :=
  ∑ q ∈ s, (unitaryMatrixDualL2CharacterAnalysis q).smulRight
    (unitaryMatrixDualL2CharacterVector q)

omit [T2Space G] in
/-- Projection onto the empty character family is the zero operator. -/
@[simp]
theorem unitaryMatrixDualFiniteCharacterProjection_empty :
    unitaryMatrixDualFiniteCharacterProjection (G := G) ∅ = 0 := by
  simp [unitaryMatrixDualFiniteCharacterProjection]

omit [T2Space G] in
/-- Pointwise finite Fourier-projection formula. -/
@[simp]
theorem unitaryMatrixDualFiniteCharacterProjection_apply
    (s : Finset (UnitaryMatrixDual G)) (f : NormalizedCompactHaarL2 G) :
    unitaryMatrixDualFiniteCharacterProjection s f =
      ∑ q ∈ s, unitaryMatrixDualL2CharacterAnalysis q f •
        unitaryMatrixDualL2CharacterVector q := by
  simp [unitaryMatrixDualFiniteCharacterProjection, ContinuousLinearMap.smulRight_apply]

/-- Finitely supported selected-character analysis coefficients restricted to `s`. -/
noncomputable def unitaryMatrixDualFiniteCharacterProjectionCoefficients
    (s : Finset (UnitaryMatrixDual G)) (f : NormalizedCompactHaarL2 G) :
    UnitaryMatrixDualCharacterCoefficients G :=
  ∑ q ∈ s, Finsupp.single q (unitaryMatrixDualL2CharacterAnalysis q f)

omit [T2Space G] in
/-- The finite orthogonal projection is exactly finite selected-character synthesis of its restricted
analysis coefficients. -/
theorem unitaryMatrixDualFiniteCharacterProjection_eq_synthesis
    (s : Finset (UnitaryMatrixDual G)) (f : NormalizedCompactHaarL2 G) :
    unitaryMatrixDualFiniteCharacterProjection s f =
      unitaryMatrixDualL2CharacterSynthesis G
        (unitaryMatrixDualFiniteCharacterProjectionCoefficients s f) := by
  rw [unitaryMatrixDualFiniteCharacterProjection_apply]
  unfold unitaryMatrixDualFiniteCharacterProjectionCoefficients
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro q hq
  calc
    unitaryMatrixDualL2CharacterAnalysis q f • unitaryMatrixDualL2CharacterVector q =
        unitaryMatrixDualL2CharacterAnalysis q f •
          unitaryMatrixDualL2CharacterSynthesis G (Finsupp.single q 1) := rfl
    _ = unitaryMatrixDualL2CharacterSynthesis G
        (unitaryMatrixDualL2CharacterAnalysis q f • Finsupp.single q 1) :=
          (map_smul (unitaryMatrixDualL2CharacterSynthesis G) _ _).symm
    _ = unitaryMatrixDualL2CharacterSynthesis G
        (Finsupp.single q (unitaryMatrixDualL2CharacterAnalysis q f)) := by
          congr 1
          simp

omit [T2Space G] in
/-- Restricted analysis coefficients equal the original coefficient on `s` and zero off `s`. -/
@[simp]
theorem unitaryMatrixDualFiniteCharacterProjectionCoefficients_apply
    (s : Finset (UnitaryMatrixDual G)) (f : NormalizedCompactHaarL2 G)
    (q : UnitaryMatrixDual G) :
    unitaryMatrixDualFiniteCharacterProjectionCoefficients s f q =
      if q ∈ s then unitaryMatrixDualL2CharacterAnalysis q f else 0 := by
  classical
  unfold unitaryMatrixDualFiniteCharacterProjectionCoefficients
  change Finsupp.applyAddHom q
    (∑ r ∈ s, Finsupp.single r (unitaryMatrixDualL2CharacterAnalysis r f)) = _
  rw [map_sum]
  by_cases hq : q ∈ s
  · rw [if_pos hq]
    calc
      (∑ r ∈ s, (Finsupp.applyAddHom q)
          (Finsupp.single r (unitaryMatrixDualL2CharacterAnalysis r f))) =
          (Finsupp.applyAddHom q)
            (Finsupp.single q (unitaryMatrixDualL2CharacterAnalysis q f)) := by
              apply Finset.sum_eq_single_of_mem q hq
              intro r hr hrq
              simp [hrq]
      _ = unitaryMatrixDualL2CharacterAnalysis q f := by simp
  · rw [if_neg hq]
    apply Finset.sum_eq_zero
    intro r hr
    have hrq : r ≠ q := by
      intro equality
      subst r
      exact hq hr
    simp [hrq]

/-- Analysis after finite projection is exact coordinate truncation. -/
theorem unitaryMatrixDualL2CharacterAnalysis_projection
    (s : Finset (UnitaryMatrixDual G)) (f : NormalizedCompactHaarL2 G)
    (q : UnitaryMatrixDual G) :
    unitaryMatrixDualL2CharacterAnalysis q
      (unitaryMatrixDualFiniteCharacterProjection s f) =
      if q ∈ s then unitaryMatrixDualL2CharacterAnalysis q f else 0 := by
  rw [unitaryMatrixDualFiniteCharacterProjection_eq_synthesis,
    unitaryMatrixDualL2CharacterAnalysis_synthesis,
    unitaryMatrixDualFiniteCharacterProjectionCoefficients_apply]

/-- Every finite selected-character projection is idempotent. -/
theorem unitaryMatrixDualFiniteCharacterProjection_idempotent
    (s : Finset (UnitaryMatrixDual G)) (f : NormalizedCompactHaarL2 G) :
    unitaryMatrixDualFiniteCharacterProjection s
      (unitaryMatrixDualFiniteCharacterProjection s f) =
      unitaryMatrixDualFiniteCharacterProjection s f := by
  rw [unitaryMatrixDualFiniteCharacterProjection_apply s
    (unitaryMatrixDualFiniteCharacterProjection s f)]
  conv_rhs => rw [unitaryMatrixDualFiniteCharacterProjection_apply]
  apply Finset.sum_congr rfl
  intro q hq
  rw [unitaryMatrixDualL2CharacterAnalysis_projection, if_pos hq]

/-- Finite projection is exact inversion on every synthesis whose support lies in the projection
set. -/
theorem unitaryMatrixDualFiniteCharacterProjection_synthesis_of_support_subset
    (s : Finset (UnitaryMatrixDual G))
    (c : UnitaryMatrixDualCharacterCoefficients G) (hc : c.support ⊆ s) :
    unitaryMatrixDualFiniteCharacterProjection s
      (unitaryMatrixDualL2CharacterSynthesis G c) =
      unitaryMatrixDualL2CharacterSynthesis G c := by
  rw [unitaryMatrixDualFiniteCharacterProjection_eq_synthesis]
  congr 1
  ext q
  rw [unitaryMatrixDualFiniteCharacterProjectionCoefficients_apply,
    unitaryMatrixDualL2CharacterAnalysis_synthesis]
  by_cases hq : q ∈ s
  · rw [if_pos hq]
  · rw [if_neg hq]
    have hn : q ∉ c.support := fun hm => hq (hc hm)
    exact (by simpa [Finsupp.mem_support_iff] using hn : c q = 0).symm

/-- Projection onto the exact support recovers every finite character synthesis. -/
theorem unitaryMatrixDualFiniteCharacterProjection_support_synthesis
    (c : UnitaryMatrixDualCharacterCoefficients G) :
    unitaryMatrixDualFiniteCharacterProjection c.support
      (unitaryMatrixDualL2CharacterSynthesis G c) =
      unitaryMatrixDualL2CharacterSynthesis G c :=
  unitaryMatrixDualFiniteCharacterProjection_synthesis_of_support_subset c.support c
    (fun _ h => h)

/-- Every selected analysis coordinate of the residual vanishes on the projection set. -/
theorem unitaryMatrixDualL2CharacterAnalysis_projection_residual_eq_zero
    (s : Finset (UnitaryMatrixDual G)) (f : NormalizedCompactHaarL2 G)
    {q : UnitaryMatrixDual G} (hq : q ∈ s) :
    unitaryMatrixDualL2CharacterAnalysis q
      (f - unitaryMatrixDualFiniteCharacterProjection s f) = 0 := by
  rw [map_sub, unitaryMatrixDualL2CharacterAnalysis_projection, if_pos hq, sub_self]

/-- The finite character projection is orthogonal to its residual. -/
theorem inner_unitaryMatrixDualFiniteCharacterProjection_residual_eq_zero
    (s : Finset (UnitaryMatrixDual G)) (f : NormalizedCompactHaarL2 G) :
    inner ℂ (unitaryMatrixDualFiniteCharacterProjection s f)
      (f - unitaryMatrixDualFiniteCharacterProjection s f) = 0 := by
  conv_lhs => lhs; rw [unitaryMatrixDualFiniteCharacterProjection_apply]
  rw [sum_inner]
  apply Finset.sum_eq_zero
  intro q hq
  rw [inner_smul_left]
  change star (unitaryMatrixDualL2CharacterAnalysis q f) *
    unitaryMatrixDualL2CharacterAnalysis q
      (f - unitaryMatrixDualFiniteCharacterProjection s f) = 0
  rw [unitaryMatrixDualL2CharacterAnalysis_projection_residual_eq_zero s f hq, mul_zero]

/-- Exact finite Parseval norm identity for the orthogonal projection. -/
theorem norm_unitaryMatrixDualFiniteCharacterProjection_sq
    (s : Finset (UnitaryMatrixDual G)) (f : NormalizedCompactHaarL2 G) :
    ‖unitaryMatrixDualFiniteCharacterProjection s f‖ ^ 2 =
      ∑ q ∈ s, ‖unitaryMatrixDualL2CharacterAnalysis q f‖ ^ 2 := by
  rw [unitaryMatrixDualFiniteCharacterProjection_apply,
    InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ)]
  rw [(orthonormal_unitaryMatrixDualL2CharacterVector (G := G)).inner_sum
    (fun q => unitaryMatrixDualL2CharacterAnalysis q f)
    (fun q => unitaryMatrixDualL2CharacterAnalysis q f) s]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro q hq
  rw [Complex.sq_norm]
  simp [Complex.normSq_apply]

/-- Exact finite Fourier Pythagorean remainder identity. -/
theorem norm_sq_eq_sum_characterAnalysis_add_projection_residual
    (s : Finset (UnitaryMatrixDual G)) (f : NormalizedCompactHaarL2 G) :
    ‖f‖ ^ 2 =
      (∑ q ∈ s, ‖unitaryMatrixDualL2CharacterAnalysis q f‖ ^ 2) +
        ‖f - unitaryMatrixDualFiniteCharacterProjection s f‖ ^ 2 := by
  have h := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
    (unitaryMatrixDualFiniteCharacterProjection s f)
    (f - unitaryMatrixDualFiniteCharacterProjection s f)
    (inner_unitaryMatrixDualFiniteCharacterProjection_residual_eq_zero s f)
  rw [add_sub_cancel] at h
  nlinarith [norm_unitaryMatrixDualFiniteCharacterProjection_sq s f]

/-- Every finite character projection is norm-nonincreasing. -/
theorem norm_unitaryMatrixDualFiniteCharacterProjection_le
    (s : Finset (UnitaryMatrixDual G)) (f : NormalizedCompactHaarL2 G) :
    ‖unitaryMatrixDualFiniteCharacterProjection s f‖ ≤ ‖f‖ := by
  have hsquare : ‖unitaryMatrixDualFiniteCharacterProjection s f‖ ^ 2 ≤ ‖f‖ ^ 2 := by
    rw [norm_unitaryMatrixDualFiniteCharacterProjection_sq]
    exact sum_norm_unitaryMatrixDualL2CharacterAnalysis_sq_le f s
  nlinarith [norm_nonneg (unitaryMatrixDualFiniteCharacterProjection s f), norm_nonneg f]

/-- The operator norm of every finite character projection is at most one. -/
theorem norm_unitaryMatrixDualFiniteCharacterProjection_le_one
    (s : Finset (UnitaryMatrixDual G)) :
    ‖unitaryMatrixDualFiniteCharacterProjection s‖ ≤ 1 :=
  (unitaryMatrixDualFiniteCharacterProjection s).opNorm_le_bound zero_le_one (by
    intro f
    simpa using norm_unitaryMatrixDualFiniteCharacterProjection_le s f)

omit [T2Space G] in
/-- The empty finite character projection has operator norm zero. -/
@[simp]
theorem norm_unitaryMatrixDualFiniteCharacterProjection_empty :
    ‖unitaryMatrixDualFiniteCharacterProjection (G := G) ∅‖ = 0 := by
  rw [unitaryMatrixDualFiniteCharacterProjection_empty, norm_zero]

/-- A projection onto a nonempty finite character family has operator norm exactly one. -/
theorem norm_unitaryMatrixDualFiniteCharacterProjection_eq_one
    (s : Finset (UnitaryMatrixDual G)) (hs : s.Nonempty) :
    ‖unitaryMatrixDualFiniteCharacterProjection s‖ = 1 := by
  apply le_antisymm (norm_unitaryMatrixDualFiniteCharacterProjection_le_one s)
  obtain ⟨q, hq⟩ := hs
  have supportSubset : (Finsupp.single q (1 : ℂ)).support ⊆ s := by
    intro r hr
    have hrq : r = q := by simpa [Finsupp.mem_support_iff] using hr
    simpa [hrq] using hq
  have fixed : unitaryMatrixDualFiniteCharacterProjection s
      (unitaryMatrixDualL2CharacterVector q) =
      unitaryMatrixDualL2CharacterVector q := by
    exact unitaryMatrixDualFiniteCharacterProjection_synthesis_of_support_subset s
      (Finsupp.single q 1) supportSubset
  have bound := (unitaryMatrixDualFiniteCharacterProjection s).le_opNorm
    (unitaryMatrixDualL2CharacterVector q)
  simpa [fixed, norm_unitaryMatrixDualL2CharacterVector] using bound

end

end Mathematics
end YangMills
