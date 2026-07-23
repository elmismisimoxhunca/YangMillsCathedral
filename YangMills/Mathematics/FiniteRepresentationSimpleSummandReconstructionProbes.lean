/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Mathematics.FiniteRepresentationSimpleSummandReconstruction

/-!
# Hostile probes for finite simple-summand reconstruction
-/

namespace YangMills
namespace Mathematics
namespace FiniteRepresentationSimpleSummandReconstruction
namespace Probes

open Module
open scoped MonoidAlgebra

noncomputable section

universe uG

variable {G : Type uG} [Group G]

/-- Analysis is exactly evaluation of the unchanged decomposition equivalence. -/
theorem exact_decomposition_input
    {n summandCount : ℕ} (ρ : G →* Matrix (Fin n) (Fin n) ℂ)
    (summands : Fin summandCount →
      Submodule ℂ[G] (matrixRepresentation ρ).asModule)
    (decomposition : (matrixRepresentation ρ).asModule ≃ₗ[ℂ[G]]
      Π₀ index, summands index)
    (vector : Fin n → ℂ) (index : Fin summandCount) :
    finiteRepresentationDecompositionInput ρ summands decomposition vector index =
      decomposition ((matrixRepresentation ρ).asModuleEquiv.symm vector) index := by
  rfl

/-- Synthesizing one summand and analyzing again gives the exact dependent single. -/
theorem exact_decomposition_output_analysis
    {n summandCount : ℕ} (ρ : G →* Matrix (Fin n) (Fin n) ℂ)
    (summands : Fin summandCount →
      Submodule ℂ[G] (matrixRepresentation ρ).asModule)
    (decomposition : (matrixRepresentation ρ).asModule ≃ₗ[ℂ[G]]
      Π₀ index, summands index)
    (index : Fin summandCount) (vector : summands index) :
    decomposition ((matrixRepresentation ρ).asModuleEquiv.symm
      (finiteRepresentationDecompositionOutput ρ summands decomposition index vector)) =
      DFinsupp.lsingle (R := ℂ[G]) index vector := by
  simp [finiteRepresentationDecompositionOutput]

/-- Exact finite analysis/synthesis reconstruction. -/
theorem exact_vector_reconstruction
    {n summandCount : ℕ} (ρ : G →* Matrix (Fin n) (Fin n) ℂ)
    (summands : Fin summandCount →
      Submodule ℂ[G] (matrixRepresentation ρ).asModule)
    (decomposition : (matrixRepresentation ρ).asModule ≃ₗ[ℂ[G]]
      Π₀ index, summands index)
    (vector : Fin n → ℂ) :
    vector = ∑ index, finiteRepresentationDecompositionOutput ρ summands decomposition index
      (finiteRepresentationDecompositionInput ρ summands decomposition vector index) :=
  finiteRepresentationDecomposition_reconstruct ρ summands decomposition vector

/-- Exact equivariant reconstruction of the represented action. -/
theorem exact_action_reconstruction
    {n summandCount : ℕ} (ρ : G →* Matrix (Fin n) (Fin n) ℂ)
    (summands : Fin summandCount →
      Submodule ℂ[G] (matrixRepresentation ρ).asModule)
    (decomposition : (matrixRepresentation ρ).asModule ≃ₗ[ℂ[G]]
      Π₀ index, summands index)
    (g : G) (vector : Fin n → ℂ) :
    Matrix.mulVec (ρ g) vector =
      ∑ index, finiteRepresentationDecompositionOutput ρ summands decomposition index
        ((MonoidAlgebra.single g (1 : ℂ)) •
          finiteRepresentationDecompositionInput ρ summands decomposition vector index) :=
  finiteRepresentationDecomposition_reconstruct_action ρ summands decomposition g vector

/-- Exact coordinate coefficient reconstruction. -/
theorem exact_coefficient_reconstruction
    {n summandCount : ℕ} (ρ : G →* Matrix (Fin n) (Fin n) ℂ)
    (summands : Fin summandCount →
      Submodule ℂ[G] (matrixRepresentation ρ).asModule)
    (decomposition : (matrixRepresentation ρ).asModule ≃ₗ[ℂ[G]]
      Π₀ index, summands index)
    (g : G) (row column : Fin n) :
    ρ g row column =
      ∑ index, finiteRepresentationDecompositionOutput ρ summands decomposition index
        ((MonoidAlgebra.single g (1 : ℂ)) •
          finiteRepresentationDecompositionInput ρ summands decomposition
            (Pi.single column 1) index) row :=
  finiteRepresentationDecomposition_reconstruct_coefficient
    ρ summands decomposition g row column

/-- Hostile probe: changing the exact finite coefficient sum is contradictory. -/
theorem changed_coefficient_reconstruction_blocked
    {n summandCount : ℕ} (ρ : G →* Matrix (Fin n) (Fin n) ℂ)
    (summands : Fin summandCount →
      Submodule ℂ[G] (matrixRepresentation ρ).asModule)
    (decomposition : (matrixRepresentation ρ).asModule ≃ₗ[ℂ[G]]
      Π₀ index, summands index)
    (g : G) (row column : Fin n)
    (changed : ρ g row column ≠
      ∑ index, finiteRepresentationDecompositionOutput ρ summands decomposition index
        ((MonoidAlgebra.single g (1 : ℂ)) •
          finiteRepresentationDecompositionInput ρ summands decomposition
            (Pi.single column 1) index) row) : False :=
  changed (finiteRepresentationDecomposition_reconstruct_coefficient
    ρ summands decomposition g row column)

/-- An alleged empty decomposition of a nonzero coordinate carrier forces every vector to zero,
blocking an empty-summand surrogate. -/
theorem empty_decomposition_forces_zero_vector
    {n : ℕ} (ρ : G →* Matrix (Fin n) (Fin n) ℂ)
    (summands : Fin 0 → Submodule ℂ[G] (matrixRepresentation ρ).asModule)
    (decomposition : (matrixRepresentation ρ).asModule ≃ₗ[ℂ[G]]
      Π₀ index, summands index)
    (vector : Fin n → ℂ) : vector = 0 := by
  rw [finiteRepresentationDecomposition_reconstruct ρ summands decomposition vector]
  simp

/-- With positive coordinate dimension, an empty decomposition is directly contradictory. -/
theorem empty_decomposition_positive_dimension_blocked
    {n : ℕ} (dimension_pos : 0 < n)
    (ρ : G →* Matrix (Fin n) (Fin n) ℂ)
    (summands : Fin 0 → Submodule ℂ[G] (matrixRepresentation ρ).asModule)
    (decomposition : (matrixRepresentation ρ).asModule ≃ₗ[ℂ[G]]
      Π₀ index, summands index) : False := by
  let coordinate : Fin n := ⟨0, dimension_pos⟩
  have collapsed := empty_decomposition_forces_zero_vector
    ρ summands decomposition (Pi.single coordinate 1)
  have atCoordinate := congrFun collapsed coordinate
  simp [coordinate] at atCoordinate

variable [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
  [MeasurableSpace G] [BorelSpace G]

/-- Every product of two continuous compact-representation coefficients receives the selected exact
finite simple-summand reconstruction. -/
theorem exact_tensor_coefficient_product_finite_simple_reconstruction
    {n m : ℕ}
    (ρ : G →* Matrix (Fin n) (Fin n) ℂ) (hρ : Continuous ρ)
    (σ : G →* Matrix (Fin m) (Fin m) ℂ) (hσ : Continuous σ) :
    ∃ (summandCount : ℕ)
      (summands : Fin summandCount → Submodule ℂ[G]
        (matrixRepresentation (matrixRepresentationTensorProduct ρ σ)).asModule)
      (decomposition :
        (matrixRepresentation (matrixRepresentationTensorProduct ρ σ)).asModule ≃ₗ[ℂ[G]]
          Π₀ index, summands index),
      (∀ index, IsSimpleModule ℂ[G] (summands index)) ∧
      ∀ (g : G) (i j : Fin n) (k l : Fin m),
        ρ g i j * σ g k l =
          ∑ index, finiteRepresentationDecompositionOutput
            (matrixRepresentationTensorProduct ρ σ) summands decomposition index
            ((MonoidAlgebra.single g (1 : ℂ)) •
              finiteRepresentationDecompositionInput
                (matrixRepresentationTensorProduct ρ σ) summands decomposition
                (Pi.single (finProdEquivFinMul n m (j, l)) 1) index)
            (finProdEquivFinMul n m (i, k)) :=
  matrixCoefficient_product_exists_finite_simpleSummand_reconstruction ρ hρ σ hσ

end

end Probes
end FiniteRepresentationSimpleSummandReconstruction
end Mathematics
end YangMills
