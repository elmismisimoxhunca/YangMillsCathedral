/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Mathematics.CompactMatrixRepresentationTensorProduct

/-!
# Finite reconstruction from simple representation summands

A finite direct-sum decomposition of a representation's group-algebra module gives exact analysis
and synthesis maps for vectors. Equivariance of that decomposition reconstructs the represented
action as a finite sum of actions inside the selected summands. Applying this to coordinate basis
vectors gives a finite-sum formula for every matrix coefficient.

For a tensor-product representation, the formula expresses every product of two input matrix
coefficients as a finite sum through simple group-algebra summands. The summand actions are exact,
but this file does not yet expand each summand term into matrix coefficients of its selected
unitary-coordinate representative. That final coordinate transport remains separate, and no
Peter–Weyl density statement is used.
-/

namespace YangMills
namespace Mathematics

open Module
open scoped MonoidAlgebra

noncomputable section

universe uG

/-- Analysis of a vector into one selected summand of a finite group-algebra decomposition. -/
noncomputable def finiteRepresentationDecompositionInput
    {G : Type uG} [Group G] {n summandCount : ℕ}
    (ρ : G →* Matrix (Fin n) (Fin n) ℂ)
    (summands : Fin summandCount →
      Submodule ℂ[G] (matrixRepresentation ρ).asModule)
    (decomposition : (matrixRepresentation ρ).asModule ≃ₗ[ℂ[G]]
      Π₀ index, summands index)
    (vector : Fin n → ℂ) (index : Fin summandCount) : summands index :=
  decomposition ((matrixRepresentation ρ).asModuleEquiv.symm vector) index

/-- Synthesis of one selected summand vector back into the original coordinate carrier. -/
noncomputable def finiteRepresentationDecompositionOutput
    {G : Type uG} [Group G] {n summandCount : ℕ}
    (ρ : G →* Matrix (Fin n) (Fin n) ℂ)
    (summands : Fin summandCount →
      Submodule ℂ[G] (matrixRepresentation ρ).asModule)
    (decomposition : (matrixRepresentation ρ).asModule ≃ₗ[ℂ[G]]
      Π₀ index, summands index)
    (index : Fin summandCount) (vector : summands index) : Fin n → ℂ :=
  (matrixRepresentation ρ).asModuleEquiv
    (decomposition.symm (DFinsupp.lsingle (R := ℂ[G]) index vector))

/-- Analysis followed by finite summand synthesis reconstructs every original vector exactly. -/
theorem finiteRepresentationDecomposition_reconstruct
    {G : Type uG} [Group G] {n summandCount : ℕ}
    (ρ : G →* Matrix (Fin n) (Fin n) ℂ)
    (summands : Fin summandCount →
      Submodule ℂ[G] (matrixRepresentation ρ).asModule)
    (decomposition : (matrixRepresentation ρ).asModule ≃ₗ[ℂ[G]]
      Π₀ index, summands index)
    (vector : Fin n → ℂ) :
    vector = ∑ index, finiteRepresentationDecompositionOutput ρ summands decomposition index
      (finiteRepresentationDecompositionInput ρ summands decomposition vector index) := by
  apply (matrixRepresentation ρ).asModuleEquiv.symm.injective
  apply decomposition.injective
  ext index
  simp [finiteRepresentationDecompositionOutput,
    finiteRepresentationDecompositionInput]

/-- Equivariance reconstructs the action of every group element as the finite sum of the unchanged
group-ring actions inside the selected summands. -/
theorem finiteRepresentationDecomposition_reconstruct_action
    {G : Type uG} [Group G] {n summandCount : ℕ}
    (ρ : G →* Matrix (Fin n) (Fin n) ℂ)
    (summands : Fin summandCount →
      Submodule ℂ[G] (matrixRepresentation ρ).asModule)
    (decomposition : (matrixRepresentation ρ).asModule ≃ₗ[ℂ[G]]
      Π₀ index, summands index)
    (g : G) (vector : Fin n → ℂ) :
    Matrix.mulVec (ρ g) vector =
      ∑ index, finiteRepresentationDecompositionOutput ρ summands decomposition index
        ((MonoidAlgebra.single g (1 : ℂ)) •
          finiteRepresentationDecompositionInput ρ summands decomposition vector index) := by
  rw [finiteRepresentationDecomposition_reconstruct ρ summands decomposition
    (Matrix.mulVec (ρ g) vector)]
  apply Finset.sum_congr rfl
  intro index _
  congr 1
  unfold finiteRepresentationDecompositionInput
  change decomposition ((matrixRepresentation ρ).asModuleEquiv.symm
    ((matrixRepresentation ρ g) vector)) index = _
  rw [Representation.asModuleEquiv_symm_map_rho]
  exact DFunLike.congr_fun
    (decomposition.map_smul (MonoidAlgebra.single g (1 : ℂ))
      ((matrixRepresentation ρ).asModuleEquiv.symm vector)) index

/-- Every original matrix coefficient is an exact finite sum through the selected summand actions. -/
theorem finiteRepresentationDecomposition_reconstruct_coefficient
    {G : Type uG} [Group G] {n summandCount : ℕ}
    (ρ : G →* Matrix (Fin n) (Fin n) ℂ)
    (summands : Fin summandCount →
      Submodule ℂ[G] (matrixRepresentation ρ).asModule)
    (decomposition : (matrixRepresentation ρ).asModule ≃ₗ[ℂ[G]]
      Π₀ index, summands index)
    (g : G) (row column : Fin n) :
    ρ g row column =
      ∑ index, finiteRepresentationDecompositionOutput ρ summands decomposition index
        ((MonoidAlgebra.single g (1 : ℂ)) •
          finiteRepresentationDecompositionInput ρ summands decomposition
            (Pi.single column 1) index) row := by
  have action := congrFun
    (finiteRepresentationDecomposition_reconstruct_action ρ summands decomposition g
      (Pi.single column 1)) row
  rw [Matrix.mulVec_single_one] at action
  simpa [Matrix.col_apply] using action

/-- Products of coefficients of two continuous compact matrix representations have an exact finite
sum through simple summand actions of their tensor representation. This is the selected decomposition
constructed by compact complete reducibility. -/
theorem matrixCoefficient_product_exists_finite_simpleSummand_reconstruction
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
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
            (finProdEquivFinMul n m (i, k)) := by
  rcases compactRepresentation_exists_finite_simple_groupAlgebra_decomposition
      (matrixRepresentationTensorProduct ρ σ)
      (continuous_matrixRepresentationTensorProduct ρ hρ σ hσ) with
    ⟨summandCount, summands, decomposition, simple⟩
  refine ⟨summandCount, summands, decomposition, simple, ?_⟩
  intro g i j k l
  rw [← matrixRepresentationTensorProduct_apply ρ σ g i j k l]
  exact finiteRepresentationDecomposition_reconstruct_coefficient
    (matrixRepresentationTensorProduct ρ σ) summands decomposition g
    (finProdEquivFinMul n m (i, k)) (finProdEquivFinMul n m (j, l))

end

end Mathematics
end YangMills
