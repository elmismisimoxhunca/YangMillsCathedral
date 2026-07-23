/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Mathematics.RepresentationEquivMatrixCoefficientTransport
import YangMills.Mathematics.CompactUnitaryMatrixCoefficientOrthogonality

/-!
# Haar coefficient orthogonality across equivalent presentations

The inequivalent and single-presentation matrix-coefficient orthogonality formulas are already
proved separately. This file closes the remaining finite-dimensional presentation case. For an
explicit equivalence `E : ρ ≃ σ`, it expands

`σ(g) = E ρ(g) E⁻¹`,

justifies every finite sum/integral exchange, and derives

`∫ conj(σᵢⱼ(g)) ρₖₗ(g) dμ_H = dim(ρ)⁻¹ conj(Eᵢₖ) conj((E⁻¹)ₗⱼ)`.

The formula retains the chosen equivalence because raw coefficients are basis-dependent. It assumes
neither Peter–Weyl completeness nor any infinite representation sum.
-/

namespace YangMills
namespace Mathematics

open MeasureTheory

noncomputable section

universe uG

/-- Exact normalized-Haar pairing of coefficients from two explicitly equivalent coordinate
presentations. Both conjugated change-of-basis factors are forced by the selected equivalence. -/
theorem normalizedCompactHaar_matrixCoefficient_orthogonality_equivalent
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    {m n : ℕ}
    (ρ : G →* Matrix (Fin m) (Fin m) ℂ)
    (σ : G →* Matrix (Fin n) (Fin n) ℂ)
    (equivalence : Representation.Equiv (matrixRepresentation ρ)
      (matrixRepresentation σ))
    (hρ : Continuous ρ) (unitaryρ : ∀ g, star (ρ g) * ρ g = 1)
    [Representation.IsIrreducible (matrixRepresentation ρ)]
    (dimension_pos : 0 < m)
    (targetRow targetColumn : Fin n)
    (sourceRow sourceColumn : Fin m) :
    (∫ g, star (σ g targetRow targetColumn) *
        ρ g sourceRow sourceColumn ∂normalizedCompactHaarMeasure G) =
      (m : ℂ)⁻¹ *
        star (representationEquivMatrix equivalence targetRow sourceRow) *
          star (representationEquivInverseMatrix equivalence
            sourceColumn targetColumn) := by
  let μ := normalizedCompactHaarMeasure G
  letI : IsProbabilityMeasure μ := normalizedCompactHaarMeasure_isProbability G
  let forward := representationEquivMatrix equivalence
  let inverse := representationEquivInverseMatrix equivalence
  have termIntegrable (row column : Fin m) : Integrable (fun g =>
      star (forward targetRow row) * star (ρ g row column) *
        star (inverse column targetColumn) * ρ g sourceRow sourceColumn) μ := by
    have termContinuous : Continuous (fun g =>
        star (forward targetRow row) * star (ρ g row column) *
          star (inverse column targetColumn) * ρ g sourceRow sourceColumn) := by
      fun_prop
    simpa only [integrableOn_univ] using
      termContinuous.continuousOn.integrableOn_compact (μ := μ) isCompact_univ
  calc
    (∫ g, star (σ g targetRow targetColumn) *
        ρ g sourceRow sourceColumn ∂μ) =
        ∫ g, ∑ row, ∑ column,
          star (forward targetRow row) * star (ρ g row column) *
            star (inverse column targetColumn) *
              ρ g sourceRow sourceColumn ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with g
      rw [representationEquiv_matrixCoefficient ρ σ equivalence g]
      change (starRingEnd ℂ) (∑ row, ∑ column,
          forward targetRow row * ρ g row column * inverse column targetColumn) *
            ρ g sourceRow sourceColumn = _
      rw [map_sum]
      simp only [starRingEnd_apply, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro row _
      change (starRingEnd ℂ) (∑ column,
          forward targetRow row * ρ g row column * inverse column targetColumn) *
            ρ g sourceRow sourceColumn = _
      rw [map_sum]
      simp only [starRingEnd_apply, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro column _
      change (starRingEnd ℂ)
          (forward targetRow row * ρ g row column * inverse column targetColumn) *
            ρ g sourceRow sourceColumn = _
      rw [map_mul, map_mul]
      simp only [starRingEnd_apply]
    _ = ∑ row, ∑ column, ∫ g,
          star (forward targetRow row) * star (ρ g row column) *
            star (inverse column targetColumn) *
              ρ g sourceRow sourceColumn ∂μ := by
      rw [integral_finsetSum Finset.univ]
      · apply Finset.sum_congr rfl
        intro row _
        rw [integral_finsetSum Finset.univ]
        intro column _
        exact termIntegrable row column
      · intro row _
        exact integrable_finsetSum _ fun column _ => termIntegrable row column
    _ = ∑ row, ∑ column,
          star (forward targetRow row) * star (inverse column targetColumn) *
            ((m : ℂ)⁻¹ * (if row = sourceRow then 1 else 0) *
              (if column = sourceColumn then 1 else 0)) := by
      apply Finset.sum_congr rfl
      intro row _
      apply Finset.sum_congr rfl
      intro column _
      rw [← normalizedCompactHaar_matrixCoefficient_orthogonality_self
        ρ hρ unitaryρ dimension_pos row sourceRow column sourceColumn]
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with g
      ring
    _ = (m : ℂ)⁻¹ * star (forward targetRow sourceRow) *
          star (inverse sourceColumn targetColumn) := by
      rw [Finset.sum_eq_single sourceRow]
      · rw [Finset.sum_eq_single sourceColumn]
        · simp
          ring
        · intro column _ column_ne
          simp [column_ne]
        · simp
      · intro row _ row_ne
        simp [row_ne]
      · simp

end

end Mathematics
end YangMills
