/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import Mathlib.LinearAlgebra.Dimension.Constructions
import YangMills.Mathematics.CompactUnitaryCoefficientFourierExtraction

/-!
# Finite matrix-coefficient subspaces of compact irreducible representations

For a finite matrix representation `ρ`, this file packages the synthesis map

`A ↦ (g ↦ ∑ᵢⱼ Aᵢⱼ ρ(g)ᵢⱼ)`

and its range in the full function space `G → ℂ`. For a continuous positive-dimensional
irreducible unitary representation, coefficient orthogonality computes the transform of a synthesized
function exactly as

`f̂(ρ) = n⁻¹ Aᵀ`.

Consequently synthesis is injective, its range is linearly equivalent to the matrix space, and the
coefficient subspace has dimension exactly `n²`. This is a finite algebraic Fourier block. It does
not claim that all such blocks are dense or complete in any continuous or `L²` function carrier.
-/

namespace YangMills
namespace Mathematics

open MeasureTheory

noncomputable section

universe uG

/-- Linear synthesis of a coefficient matrix into the corresponding finite linear combination of
matrix-coefficient functions. -/
def matrixCoefficientSynthesis
    {G : Type uG} [Group G] {n : ℕ}
    (ρ : G →* Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] (G → ℂ) where
  toFun A g := ∑ row, ∑ column, A row column * ρ g row column
  map_add' A B := by
    funext g
    change (∑ row, ∑ column,
        (A row column + B row column) * ρ g row column) =
      (∑ row, ∑ column, A row column * ρ g row column) +
      ∑ row, ∑ column, B row column * ρ g row column
    simp only [add_mul, Finset.sum_add_distrib]
  map_smul' c A := by
    funext g
    change (∑ row, ∑ column,
        (c * A row column) * ρ g row column) =
      c * ∑ row, ∑ column, A row column * ρ g row column
    simp_rw [mul_assoc, ← Finset.mul_sum]

@[simp]
theorem matrixCoefficientSynthesis_apply
    {G : Type uG} [Group G] {n : ℕ}
    (ρ : G →* Matrix (Fin n) (Fin n) ℂ)
    (A : Matrix (Fin n) (Fin n) ℂ) (g : G) :
    matrixCoefficientSynthesis ρ A g =
      ∑ row, ∑ column, A row column * ρ g row column :=
  rfl

/-- Every synthesized coefficient combination is continuous when the matrix representation is
continuous. -/
theorem continuous_matrixCoefficientSynthesis
    {G : Type uG} [Group G] [TopologicalSpace G]
    {n : ℕ} (ρ : G →* Matrix (Fin n) (Fin n) ℂ)
    (hρ : Continuous ρ) (A : Matrix (Fin n) (Fin n) ℂ) :
    Continuous (matrixCoefficientSynthesis ρ A) := by
  change Continuous (fun g =>
    ∑ row, ∑ column, A row column * ρ g row column)
  fun_prop

/-- The normalized-Haar Fourier transform of a synthesized irreducible unitary coefficient block is
exactly inverse dimension times the transpose of its coefficient matrix. -/
theorem normalizedCompactMatrixFourierCoefficient_synthesis
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    {n : ℕ} (ρ : G →* Matrix (Fin n) (Fin n) ℂ)
    (hρ : Continuous ρ) (unitaryρ : ∀ g, star (ρ g) * ρ g = 1)
    [Representation.IsIrreducible (matrixRepresentation ρ)]
    (dimension_pos : 0 < n) (A : Matrix (Fin n) (Fin n) ℂ) :
    normalizedCompactMatrixFourierCoefficient G ρ
        (matrixCoefficientSynthesis ρ A) =
      (n : ℂ)⁻¹ • A.transpose := by
  classical
  let μ := normalizedCompactHaarMeasure G
  letI : IsProbabilityMeasure μ := normalizedCompactHaarMeasure_isProbability G
  ext outputRow outputColumn
  rw [normalizedCompactMatrixFourierCoefficient_apply]
  have integrableTerm (row column : Fin n) :
      Integrable (fun g =>
        A row column *
          (ρ g row column * ρ (g⁻¹) outputRow outputColumn)) μ := by
    have continuousTerm : Continuous (fun g =>
        A row column *
          (ρ g row column * ρ (g⁻¹) outputRow outputColumn)) := by
      fun_prop
    simpa only [integrableOn_univ] using
      continuousTerm.continuousOn.integrableOn_compact
        (μ := μ) isCompact_univ
  calc
    (∫ g, matrixCoefficientSynthesis ρ A g *
        ρ (g⁻¹) outputRow outputColumn ∂μ) =
        ∫ g, ∑ row, ∑ column,
          A row column *
            (ρ g row column * ρ (g⁻¹) outputRow outputColumn) ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with g
      rw [matrixCoefficientSynthesis_apply, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro row _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro column _
      ring
    _ = ∑ row, ∑ column,
        ∫ g, A row column *
          (ρ g row column * ρ (g⁻¹) outputRow outputColumn) ∂μ := by
      rw [integral_finsetSum Finset.univ]
      · apply Finset.sum_congr rfl
        intro row _
        rw [integral_finsetSum Finset.univ]
        intro column _
        exact integrableTerm row column
      · intro row _
        exact integrable_finsetSum _ fun column _ =>
          integrableTerm row column
    _ = ∑ row, ∑ column, A row column *
        ((n : ℂ)⁻¹ * (if outputColumn = row then 1 else 0) *
          (if outputRow = column then 1 else 0)) := by
      apply Finset.sum_congr rfl
      intro row _
      apply Finset.sum_congr rfl
      intro column _
      rw [integral_const_mul]
      have pairing :=
        normalizedCompactHaar_matrixCoefficient_orthogonality_self
          ρ hρ unitaryρ dimension_pos
          outputColumn row outputRow column
      have inversePairing :
          (∫ g, ρ g row column * ρ (g⁻¹) outputRow outputColumn ∂μ) =
            ∫ g, star (ρ g outputColumn outputRow) * ρ g row column ∂μ := by
        apply integral_congr_ae
        filter_upwards [] with g
        rw [unitaryMatrixRepresentation_inv_apply
          ρ unitaryρ g outputRow outputColumn]
        ring
      rw [inversePairing, pairing]
    _ = ((n : ℂ)⁻¹ • A.transpose) outputRow outputColumn := by
      rw [Finset.sum_eq_single outputColumn]
      · rw [Finset.sum_eq_single outputRow]
        · simp
          ring
        · intro column _ column_ne
          simp [Ne.symm column_ne]
        · simp
      · intro row _ row_ne
        apply Finset.sum_eq_zero
        intro column _
        simp [Ne.symm row_ne]
      · simp

/-- Matrix-coefficient synthesis is injective for a positive-dimensional irreducible unitary
representation. Thus coefficient matrices cannot cancel pointwise unless they are equal. -/
theorem matrixCoefficientSynthesis_injective
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    {n : ℕ} (ρ : G →* Matrix (Fin n) (Fin n) ℂ)
    (hρ : Continuous ρ) (unitaryρ : ∀ g, star (ρ g) * ρ g = 1)
    [Representation.IsIrreducible (matrixRepresentation ρ)]
    (dimension_pos : 0 < n) :
    Function.Injective (matrixCoefficientSynthesis ρ) := by
  intro A B functionsEqual
  have transformsEqual := congrArg
    (normalizedCompactMatrixFourierCoefficient G ρ) functionsEqual
  rw [normalizedCompactMatrixFourierCoefficient_synthesis
      ρ hρ unitaryρ dimension_pos A,
    normalizedCompactMatrixFourierCoefficient_synthesis
      ρ hρ unitaryρ dimension_pos B] at transformsEqual
  ext row column
  have entryEqual := congrFun (congrFun transformsEqual column) row
  change (n : ℂ)⁻¹ * A row column =
    (n : ℂ)⁻¹ * B row column at entryEqual
  have dimension_ne_zero : (n : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.ne_of_gt dimension_pos)
  exact mul_left_cancel₀ (inv_ne_zero dimension_ne_zero) entryEqual

/-- The finite matrix-coefficient subspace is the range of coefficient synthesis in the full
function space. -/
def matrixCoefficientSubspace
    {G : Type uG} [Group G] {n : ℕ}
    (ρ : G →* Matrix (Fin n) (Fin n) ℂ) : Submodule ℂ (G → ℂ) :=
  LinearMap.range (matrixCoefficientSynthesis ρ)

/-- For an irreducible unitary representation, synthesis identifies the matrix space with its exact
coefficient subspace. -/
noncomputable def matrixCoefficientSynthesisEquiv
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    {n : ℕ} (ρ : G →* Matrix (Fin n) (Fin n) ℂ)
    (hρ : Continuous ρ) (unitaryρ : ∀ g, star (ρ g) * ρ g = 1)
    [Representation.IsIrreducible (matrixRepresentation ρ)]
    (dimension_pos : 0 < n) :
    Matrix (Fin n) (Fin n) ℂ ≃ₗ[ℂ] matrixCoefficientSubspace ρ :=
  LinearEquiv.ofInjective (matrixCoefficientSynthesis ρ)
    (matrixCoefficientSynthesis_injective
      ρ hρ unitaryρ dimension_pos)

/-- Every matrix-coefficient subspace is finite dimensional, even before irreducibility. -/
noncomputable instance matrixCoefficientSubspace_finiteDimensional
    {G : Type uG} [Group G] {n : ℕ}
    (ρ : G →* Matrix (Fin n) (Fin n) ℂ) :
    FiniteDimensional ℂ (matrixCoefficientSubspace ρ) :=
  Module.Finite.range (matrixCoefficientSynthesis ρ)

/-- A positive-dimensional irreducible unitary `n`-dimensional representation has an exact `n²`
dimensional coefficient subspace. -/
theorem finrank_matrixCoefficientSubspace
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    {n : ℕ} (ρ : G →* Matrix (Fin n) (Fin n) ℂ)
    (hρ : Continuous ρ) (unitaryρ : ∀ g, star (ρ g) * ρ g = 1)
    [Representation.IsIrreducible (matrixRepresentation ρ)]
    (dimension_pos : 0 < n) :
    Module.finrank ℂ (matrixCoefficientSubspace ρ) = n * n := by
  rw [← (matrixCoefficientSynthesisEquiv
    ρ hρ unitaryρ dimension_pos).finrank_eq]
  simp [Module.finrank_matrix]

end

end Mathematics
end YangMills
