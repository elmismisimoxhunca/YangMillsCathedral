/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import Mathlib.LinearAlgebra.Matrix.Basis
import YangMills.Mathematics.CompactHaarSchurTrace
import YangMills.Mathematics.UnitaryMatrixRepresentationInverse

/-!
# Haar orthogonality of compact unitary matrix coefficients

This file combines the compact Haar–Schur average, exact trace/dimension normalization, and the
unitary inverse-entry formula. For one irreducible positive-dimensional unitary matrix
representation it proves

`∫ conj(ρ(g)ₐᵣ) ρ(g)ᵦ𝚌 dμ_H = n⁻¹ δₐᵦ δᵣ𝚌`.

For inequivalent irreducible unitary representations it proves the corresponding mixed integral is
zero. The formulas retain all four matrix indices and the exact normalized Haar measure.

Transport across an explicitly supplied equivalence between two differently presented equivalent
representations and Peter–Weyl completeness remain separate tasks.
-/

namespace YangMills
namespace Mathematics

open MeasureTheory

noncomputable section

universe uG

/-- A conjugated matrix unit extracts one conjugated target coefficient and one source
coefficient. -/
theorem unitary_conjugated_single_apply
    {G : Type uG} [Group G] {m n : ℕ}
    (σ : G →* Matrix (Fin m) (Fin m) ℂ)
    (ρ : G →* Matrix (Fin n) (Fin n) ℂ)
    (unitaryσ : ∀ g, star (σ g) * σ g = 1)
    (g : G) (targetRow targetColumn : Fin m)
    (sourceRow sourceColumn : Fin n) :
    (σ (g⁻¹) * Matrix.single targetRow sourceRow (1 : ℂ) * ρ g)
        targetColumn sourceColumn =
      star (σ g targetRow targetColumn) * ρ g sourceRow sourceColumn := by
  classical
  rw [unitaryMatrixRepresentation_inv_eq_conjTranspose σ unitaryσ g]
  simp only [Matrix.mul_apply, Matrix.single_apply,
    Matrix.conjTranspose_apply]
  rw [Finset.sum_eq_single sourceRow]
  · rw [Finset.sum_eq_single targetRow]
    · simp
    · intro index _ index_ne
      simp [Ne.symm index_ne]
    · simp
  · intro index _ index_ne
    have innerZero :
        (∑ targetIndex, star (σ g targetIndex targetColumn) *
          if targetRow = targetIndex ∧ sourceRow = index then 1 else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro targetIndex _
      simp [Ne.symm index_ne]
    rw [innerZero, zero_mul]
  · simp

/-- Trace of a matrix unit is the matching-index Kronecker delta. -/
theorem trace_single_one
    {n : ℕ} (row column : Fin n) :
    Matrix.trace (Matrix.single row column (1 : ℂ)) =
      if row = column then 1 else 0 := by
  classical
  unfold Matrix.trace
  by_cases equality : row = column
  · subst column
    rw [Finset.sum_eq_single row]
    · simp
    · intro index _ index_ne
      simp [Ne.symm index_ne]
    · simp
  · simp only [equality, if_false]
    apply Finset.sum_eq_zero
    intro index _
    simp [equality]

/-- Exact self-orthogonality of all matrix coefficients of an irreducible positive-dimensional
unitary representation. -/
theorem normalizedCompactHaar_matrixCoefficient_orthogonality_self
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    {n : ℕ} (ρ : G →* Matrix (Fin n) (Fin n) ℂ)
    (hρ : Continuous ρ) (unitaryρ : ∀ g, star (ρ g) * ρ g = 1)
    [Representation.IsIrreducible (matrixRepresentation ρ)]
    (dimension_pos : 0 < n)
    (firstRow secondRow firstColumn secondColumn : Fin n) :
    (∫ g, star (ρ g firstRow firstColumn) *
        ρ g secondRow secondColumn ∂normalizedCompactHaarMeasure G) =
      (n : ℂ)⁻¹ * (if firstRow = secondRow then 1 else 0) *
        (if firstColumn = secondColumn then 1 else 0) := by
  let matrixUnit := Matrix.single firstRow secondRow (1 : ℂ)
  have averagedEntry := congrFun (congrFun
    (compactHaarIntertwinerAverage_eq_schurScalar_smul_one
      ρ hρ matrixUnit) firstColumn) secondColumn
  have entryIntegral :
      compactHaarIntertwinerAverage ρ ρ matrixUnit firstColumn secondColumn =
        ∫ g, star (ρ g firstRow firstColumn) *
          ρ g secondRow secondColumn ∂normalizedCompactHaarMeasure G := by
    rw [compactHaarIntertwinerAverage_apply]
    apply integral_congr_ae
    filter_upwards [] with g
    exact unitary_conjugated_single_apply
      ρ ρ unitaryρ g firstRow firstColumn secondRow secondColumn
  rw [entryIntegral,
    compactHaarSchurScalar_eq_inv_natCast_mul_trace
      ρ hρ matrixUnit dimension_pos,
    trace_single_one] at averagedEntry
  simpa [Matrix.one_apply, matrixUnit] using averagedEntry

/-- Mixed matrix coefficients of inequivalent irreducible unitary representations are exactly
orthogonal. Only the target representation needs the inverse/conjugate entry law in this
orientation. -/
theorem normalizedCompactHaar_matrixCoefficient_orthogonality_inequivalent
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    {m n : ℕ}
    (σ : G →* Matrix (Fin m) (Fin m) ℂ)
    (ρ : G →* Matrix (Fin n) (Fin n) ℂ)
    (hσ : Continuous σ) (hρ : Continuous ρ)
    (unitaryσ : ∀ g, star (σ g) * σ g = 1)
    [Representation.IsIrreducible (matrixRepresentation ρ)]
    [Representation.IsIrreducible (matrixRepresentation σ)]
    [IsEmpty (Representation.Equiv
      (matrixRepresentation ρ) (matrixRepresentation σ))]
    (targetRow targetColumn : Fin m)
    (sourceRow sourceColumn : Fin n) :
    (∫ g, star (σ g targetRow targetColumn) *
        ρ g sourceRow sourceColumn ∂normalizedCompactHaarMeasure G) = 0 := by
  let matrixUnit := Matrix.single targetRow sourceRow (1 : ℂ)
  have averageZero :=
    compactHaarIntertwinerAverage_eq_zero_of_irreducible_inequivalent
      σ ρ hσ hρ matrixUnit
  have entryZero := congrFun (congrFun averageZero targetColumn) sourceColumn
  rw [Matrix.zero_apply] at entryZero
  have entryIntegral :
      compactHaarIntertwinerAverage σ ρ matrixUnit targetColumn sourceColumn =
        ∫ g, star (σ g targetRow targetColumn) *
          ρ g sourceRow sourceColumn ∂normalizedCompactHaarMeasure G := by
    rw [compactHaarIntertwinerAverage_apply]
    apply integral_congr_ae
    filter_upwards [] with g
    exact unitary_conjugated_single_apply
      σ ρ unitaryσ g targetRow targetColumn sourceRow sourceColumn
  rw [entryIntegral] at entryZero
  exact entryZero

end

end Mathematics
end YangMills
