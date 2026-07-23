/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Mathematics.FiniteRepresentationUnitaryCoefficientExpansion

/-!
# Hostile probes for finite unitary-coefficient expansion
-/

namespace YangMills
namespace Mathematics
namespace FiniteRepresentationUnitaryCoefficientExpansion
namespace Probes

open Module
open scoped MonoidAlgebra

noncomputable section

universe uG uW

variable {G : Type uG} [Group G]

/-- Exact abstract-to-matrix expansion, retaining output weight, matrix coefficient, and input
coordinate in that order. -/
theorem exact_representation_equiv_expansion
    {W : Type uW} [AddCommGroup W] [Module ℂ W]
    (τ : Representation ℂ G W) {d : ℕ}
    (u : G →* Matrix (Fin d) (Fin d) ℂ)
    (equivalence : Representation.Equiv τ (matrixRepresentation u))
    (functional : W →ₗ[ℂ] ℂ) (g : G) (vector : W) :
    functional (τ g vector) =
      ∑ row, ∑ column,
        functional (equivalence.symm (Pi.single row 1)) *
          u g row column * equivalence vector column :=
  representationEquiv_matrixCoefficient_expansion
    τ u equivalence functional g vector

/-- Hostile probe: changing the exact matrix-element expansion is contradictory. -/
theorem changed_representation_equiv_expansion_blocked
    {W : Type uW} [AddCommGroup W] [Module ℂ W]
    (τ : Representation ℂ G W) {d : ℕ}
    (u : G →* Matrix (Fin d) (Fin d) ℂ)
    (equivalence : Representation.Equiv τ (matrixRepresentation u))
    (functional : W →ₗ[ℂ] ℂ) (g : G) (vector : W)
    (changed : functional (τ g vector) ≠
      ∑ row, ∑ column,
        functional (equivalence.symm (Pi.single row 1)) *
          u g row column * equivalence vector column) : False :=
  changed (representationEquiv_matrixCoefficient_expansion
    τ u equivalence functional g vector)

/-- Hostile RestrictScalars probe: changing the exact group-ring-action coordinate expansion is
contradictory. -/
theorem changed_groupAlgebraSubmodule_action_expansion_blocked
    {n d : ℕ} (ρ : G →* Matrix (Fin n) (Fin n) ℂ)
    (S : Submodule ℂ[G] (matrixRepresentation ρ).asModule)
    (u : G →* Matrix (Fin d) (Fin d) ℂ)
    (equivalence : Representation.Equiv
      (Representation.ofModule (k := ℂ) (G := G) S) (matrixRepresentation u))
    (functional : S →ₗ[ℂ] ℂ) (g : G) (vector : S)
    (changed : functional ((MonoidAlgebra.single g (1 : ℂ)) • vector) ≠
      ∑ row, ∑ column,
        functional (restrictedGroupAlgebraSubmoduleLinearEquiv ρ S
          (equivalence.symm (Pi.single row 1))) *
        u g row column *
        equivalence ((restrictedGroupAlgebraSubmoduleLinearEquiv ρ S).symm vector) column) : False :=
  changed (groupAlgebraSubmodule_action_matrixCoefficient_expansion
    ρ S u equivalence functional g vector)

/-- The bundled output-coordinate functional is exactly the earlier summand synthesis evaluated at
the selected output row. -/
theorem exact_output_coordinate_functional
    {n summandCount : ℕ} (ρ : G →* Matrix (Fin n) (Fin n) ℂ)
    (summands : Fin summandCount →
      Submodule ℂ[G] (matrixRepresentation ρ).asModule)
    (decomposition : (matrixRepresentation ρ).asModule ≃ₗ[ℂ[G]]
      Π₀ index, summands index)
    (index : Fin summandCount) (row : Fin n) (vector : summands index) :
    finiteRepresentationDecompositionOutputCoordinate ρ summands decomposition index row vector =
      finiteRepresentationDecompositionOutput ρ summands decomposition index vector row := by
  rfl

/-- Every finite decomposition equipped with explicit summand matrices has the exact triple-sum
coefficient formula. -/
theorem exact_matrix_summand_coefficient_expansion
    {n summandCount : ℕ} (ρ : G →* Matrix (Fin n) (Fin n) ℂ)
    (summands : Fin summandCount →
      Submodule ℂ[G] (matrixRepresentation ρ).asModule)
    (decomposition : (matrixRepresentation ρ).asModule ≃ₗ[ℂ[G]]
      Π₀ index, summands index)
    (dimension : Fin summandCount → ℕ)
    (u : ∀ index, G →* Matrix (Fin (dimension index)) (Fin (dimension index)) ℂ)
    (equivalence : ∀ index, Representation.Equiv
      (Representation.ofModule (k := ℂ) (G := G) (summands index))
      (matrixRepresentation (u index)))
    (g : G) (row column : Fin n) :
    ρ g row column = ∑ index, ∑ summandRow, ∑ summandColumn,
      finiteRepresentationDecompositionOutputCoordinate ρ summands decomposition index row
        (restrictedGroupAlgebraSubmoduleLinearEquiv ρ (summands index)
          ((equivalence index).symm (Pi.single summandRow 1))) *
      u index g summandRow summandColumn *
      equivalence index
        ((restrictedGroupAlgebraSubmoduleLinearEquiv ρ (summands index)).symm
          (finiteRepresentationDecompositionInput ρ summands decomposition
            (Pi.single column 1) index)) summandColumn :=
  finiteRepresentationDecomposition_reconstruct_coefficient_in_matrixSummands
    ρ summands decomposition dimension u equivalence g row column

variable [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
  [MeasurableSpace G] [BorelSpace G]

/-- A simple selected decomposition expands directly in its selected irreducible unitary matrix
coefficients. -/
theorem exact_selected_unitary_summand_coefficient_expansion
    {n summandCount : ℕ}
    (ρ : G →* Matrix (Fin n) (Fin n) ℂ) (hρ : Continuous ρ)
    (summands : Fin summandCount →
      Submodule ℂ[G] (matrixRepresentation ρ).asModule)
    (decomposition : (matrixRepresentation ρ).asModule ≃ₗ[ℂ[G]]
      Π₀ index, summands index)
    [∀ index, IsSimpleModule ℂ[G] (summands index)]
    (g : G) (row column : Fin n) :
    ρ g row column = ∑ index, ∑ summandRow, ∑ summandColumn,
      finiteRepresentationDecompositionOutputCoordinate ρ summands decomposition index row
        (restrictedGroupAlgebraSubmoduleLinearEquiv ρ (summands index)
          ((simpleGroupAlgebraSubmoduleSelectedUnitaryEquiv ρ hρ (summands index)).symm
            (Pi.single summandRow 1))) *
      (simpleGroupAlgebraSubmoduleUnitaryData ρ hρ (summands index)).representation g
        summandRow summandColumn *
      simpleGroupAlgebraSubmoduleSelectedUnitaryEquiv ρ hρ (summands index)
        ((restrictedGroupAlgebraSubmoduleLinearEquiv ρ (summands index)).symm
          (finiteRepresentationDecompositionInput ρ summands decomposition
            (Pi.single column 1) index)) summandColumn :=
  finiteRepresentationDecomposition_reconstruct_coefficient_in_selectedUnitarySummands
    ρ hρ summands decomposition g row column

/-- Every product of two continuous compact-representation coefficients has an exact finite
expansion in coefficients of positive-dimensional continuous irreducible unitary representatives. -/
theorem exact_tensor_product_selected_unitary_coefficient_expansion
    {n m : ℕ}
    (ρ : G →* Matrix (Fin n) (Fin n) ℂ) (hρ : Continuous ρ)
    (σ : G →* Matrix (Fin m) (Fin m) ℂ) (hσ : Continuous σ) :
    ∃ (summandCount : ℕ)
      (summands : Fin summandCount → Submodule ℂ[G]
        (matrixRepresentation (matrixRepresentationTensorProduct ρ σ)).asModule)
      (decomposition :
        (matrixRepresentation (matrixRepresentationTensorProduct ρ σ)).asModule ≃ₗ[ℂ[G]]
          Π₀ index, summands index)
      (dimension : Fin summandCount → ℕ)
      (u : ∀ index, G →* Matrix (Fin (dimension index)) (Fin (dimension index)) ℂ)
      (equivalence : ∀ index, Representation.Equiv
        (Representation.ofModule (k := ℂ) (G := G) (summands index))
        (matrixRepresentation (u index))),
      (∀ index, 0 < dimension index) ∧
      (∀ index, Continuous (u index)) ∧
      (∀ index g, star (u index g) * u index g = 1) ∧
      (∀ index, Representation.IsIrreducible (matrixRepresentation (u index))) ∧
      ∀ (g : G) (i j : Fin n) (k l : Fin m),
        ρ g i j * σ g k l = ∑ index, ∑ summandRow, ∑ summandColumn,
          finiteRepresentationDecompositionOutputCoordinate
            (matrixRepresentationTensorProduct ρ σ) summands decomposition index
            (finProdEquivFinMul n m (i, k))
            (restrictedGroupAlgebraSubmoduleLinearEquiv
              (matrixRepresentationTensorProduct ρ σ) (summands index)
              ((equivalence index).symm (Pi.single summandRow 1))) *
          u index g summandRow summandColumn *
          equivalence index
            ((restrictedGroupAlgebraSubmoduleLinearEquiv
              (matrixRepresentationTensorProduct ρ σ) (summands index)).symm
              (finiteRepresentationDecompositionInput
                (matrixRepresentationTensorProduct ρ σ) summands decomposition
                (Pi.single (finProdEquivFinMul n m (j, l)) 1) index)) summandColumn :=
  matrixCoefficient_product_exists_finite_selectedUnitarySummand_expansion ρ hρ σ hσ

end

end Probes
end FiniteRepresentationUnitaryCoefficientExpansion
end Mathematics
end YangMills
