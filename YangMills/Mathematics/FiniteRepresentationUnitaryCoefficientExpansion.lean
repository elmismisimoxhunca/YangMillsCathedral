/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Mathematics.FiniteRepresentationSimpleSummandReconstruction

/-!
# Finite expansion in selected irreducible unitary coefficients

An exact representation equivalence to matrix coordinates expands every abstract matrix element
`L(ρ(g)v)` as a finite double sum of coordinate matrix coefficients. Applying this to each simple
summand in the compact complete-reducibility decomposition upgrades the earlier group-algebra action
formula to an explicit finite sum of matrix coefficients of selected continuous irreducible unitary
representatives.

In particular, every product of two coordinate coefficients of continuous compact-group matrix
representations has such a finite expansion. This proves the multiplicative finite-span bridge
needed for the algebraic Peter–Weyl/Stone–Weierstrass track. It does not prove point separation,
uniform density, `L²` completeness, or any infinite-series theorem.
-/

namespace YangMills
namespace Mathematics

open Module
open scoped MonoidAlgebra

noncomputable section

universe uG uW

/-- An exact equivalence to finite matrix coordinates expands every abstract matrix element into a
finite double sum of coordinate matrix coefficients. -/
theorem representationEquiv_matrixCoefficient_expansion
    {G : Type uG} [Group G] {W : Type uW} [AddCommGroup W] [Module ℂ W]
    (τ : Representation ℂ G W) {d : ℕ}
    (u : G →* Matrix (Fin d) (Fin d) ℂ)
    (equivalence : Representation.Equiv τ (matrixRepresentation u))
    (functional : W →ₗ[ℂ] ℂ) (g : G) (vector : W) :
    functional (τ g vector) =
      ∑ row, ∑ column,
        functional (equivalence.symm (Pi.single row 1)) *
          u g row column * equivalence vector column := by
  have intertwining := Representation.IntertwiningMap.isIntertwining
    τ (matrixRepresentation u) equivalence.toIntertwiningMap g vector
  change equivalence (τ g vector) =
    Matrix.mulVec (u g) (equivalence vector) at intertwining
  have action := congrArg equivalence.symm intertwining
  simp only [equivalence.symm_apply_apply] at action
  rw [action]
  have expand (coordinateVector : Fin d → ℂ) :
      equivalence.symm coordinateVector =
        ∑ row, coordinateVector row • equivalence.symm (Pi.single row 1) := by
    apply equivalence.injective
    simp only [map_sum, map_smul]
    ext row
    simp [Pi.single_apply]
  rw [expand]
  simp only [map_sum, map_smul, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro row _
  rw [Matrix.mulVec, dotProduct]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro column _
  ring

/-- A group-ring action inside a submodule expands in the matrix coefficients of any explicitly
equivalent matrix representation. -/
theorem groupAlgebraSubmodule_action_matrixCoefficient_expansion
    {G : Type uG} [Group G] {n d : ℕ}
    (ρ : G →* Matrix (Fin n) (Fin n) ℂ)
    (S : Submodule ℂ[G] (matrixRepresentation ρ).asModule)
    (u : G →* Matrix (Fin d) (Fin d) ℂ)
    (equivalence : Representation.Equiv
      (Representation.ofModule (k := ℂ) (G := G) S) (matrixRepresentation u))
    (functional : S →ₗ[ℂ] ℂ) (g : G) (vector : S) :
    functional ((MonoidAlgebra.single g (1 : ℂ)) • vector) =
      ∑ row, ∑ column,
        functional (restrictedGroupAlgebraSubmoduleLinearEquiv ρ S
          (equivalence.symm (Pi.single row 1))) *
        u g row column *
        equivalence ((restrictedGroupAlgebraSubmoduleLinearEquiv ρ S).symm vector) column := by
  letI groupCarrier : AddCommGroup (RestrictScalars ℂ ℂ[G] S) :=
    instAddCommGroupRestrictScalars ℂ ℂ[G] S
  letI : AddCommMonoid (RestrictScalars ℂ ℂ[G] S) := groupCarrier.toAddCommMonoid
  letI : Module ℂ (RestrictScalars ℂ ℂ[G] S) := RestrictScalars.module ℂ ℂ[G] S
  let carrierEquiv := restrictedGroupAlgebraSubmoduleLinearEquiv ρ S
  let restrictedFunctional : RestrictScalars ℂ ℂ[G] S →ₗ[ℂ] ℂ :=
    functional.comp carrierEquiv.toLinearMap
  have expansion := representationEquiv_matrixCoefficient_expansion
    (Representation.ofModule (k := ℂ) (G := G) S) u equivalence
    restrictedFunctional g (carrierEquiv.symm vector)
  have action : carrierEquiv
      ((Representation.ofModule (k := ℂ) (G := G) S) g (carrierEquiv.symm vector)) =
      (MonoidAlgebra.single g (1 : ℂ)) • vector := by
    apply Subtype.ext
    change ((RestrictScalars.addEquiv ℂ ℂ[G] S)
      ((Representation.ofModule (k := ℂ) (G := G) S) g
        ((RestrictScalars.addEquiv ℂ ℂ[G] S).symm vector))).val = _
    have action' : (RestrictScalars.addEquiv ℂ ℂ[G] S)
        ((Representation.ofModule (k := ℂ) (G := G) S) g
          ((RestrictScalars.addEquiv ℂ ℂ[G] S).symm vector)) =
        (MonoidAlgebra.single g (1 : ℂ)) • vector := by
      rw [← one_smul ℂ
        ((Representation.ofModule (k := ℂ) (G := G) S) g
          ((RestrictScalars.addEquiv ℂ ℂ[G] S).symm vector)),
        ← LinearMap.smul_apply, ← Representation.asAlgebraHom_single]
      rw [Representation.ofModule_asAlgebraHom_apply_apply]
      simp
    rw [action']
  calc
    functional ((MonoidAlgebra.single g (1 : ℂ)) • vector) =
        restrictedFunctional
          ((Representation.ofModule (k := ℂ) (G := G) S) g
            (carrierEquiv.symm vector)) := by
      change functional ((MonoidAlgebra.single g (1 : ℂ)) • vector) =
        functional (carrierEquiv
          ((Representation.ofModule (k := ℂ) (G := G) S) g
            (carrierEquiv.symm vector)))
      rw [action]
    _ = ∑ row, ∑ column,
        restrictedFunctional (equivalence.symm (Pi.single row 1)) *
          u g row column * equivalence (carrierEquiv.symm vector) column := expansion
    _ = _ := rfl

/-- A selected exact equivalence from a simple group-algebra summand to its Haar-unitarized matrix
representative. -/
noncomputable def simpleGroupAlgebraSubmoduleSelectedUnitaryEquiv
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    {n : ℕ} (ρ : G →* Matrix (Fin n) (Fin n) ℂ) (hρ : Continuous ρ)
    (S : Submodule ℂ[G] (matrixRepresentation ρ).asModule)
    [IsSimpleModule ℂ[G] S] :
    Representation.Equiv (Representation.ofModule (k := ℂ) (G := G) S)
      (matrixRepresentation
        (simpleGroupAlgebraSubmoduleUnitaryData ρ hρ S).representation) :=
  Classical.choice (simpleGroupAlgebraSubmoduleUnitaryData_equivalent ρ hρ S)

/-- The output coordinate after synthesizing one summand is a complex-linear functional of that
summand vector. -/
noncomputable def finiteRepresentationDecompositionOutputCoordinate
    {G : Type uG} [Group G] {n summandCount : ℕ}
    (ρ : G →* Matrix (Fin n) (Fin n) ℂ)
    (summands : Fin summandCount →
      Submodule ℂ[G] (matrixRepresentation ρ).asModule)
    (decomposition : (matrixRepresentation ρ).asModule ≃ₗ[ℂ[G]]
      Π₀ index, summands index)
    (index : Fin summandCount) (row : Fin n) : summands index →ₗ[ℂ] ℂ :=
  (LinearMap.proj row).comp
    ((matrixRepresentation ρ).asModuleEquiv.toLinearMap.comp
      ((decomposition.symm.toLinearMap.restrictScalars ℂ).comp
        ((DFinsupp.lsingle (R := ℂ[G]) index).restrictScalars ℂ)))

/-- Any finite decomposition equipped with explicit matrix representatives for its summands gives a
finite triple-sum expansion of every original coefficient. -/
theorem finiteRepresentationDecomposition_reconstruct_coefficient_in_matrixSummands
    {G : Type uG} [Group G] {n summandCount : ℕ}
    (ρ : G →* Matrix (Fin n) (Fin n) ℂ)
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
            (Pi.single column 1) index)) summandColumn := by
  rw [finiteRepresentationDecomposition_reconstruct_coefficient
    ρ summands decomposition g row column]
  apply Finset.sum_congr rfl
  intro index _
  exact groupAlgebraSubmodule_action_matrixCoefficient_expansion ρ (summands index)
    (u index) (equivalence index)
    (finiteRepresentationDecompositionOutputCoordinate ρ summands decomposition index row) g
    (finiteRepresentationDecompositionInput ρ summands decomposition
      (Pi.single column 1) index)

/-- For a compact continuous representation with simple selected summands, every coefficient expands
in the selected irreducible unitary summand coefficients. -/
theorem finiteRepresentationDecomposition_reconstruct_coefficient_in_selectedUnitarySummands
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
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
  finiteRepresentationDecomposition_reconstruct_coefficient_in_matrixSummands
    ρ summands decomposition
    (fun index => (simpleGroupAlgebraSubmoduleUnitaryData ρ hρ (summands index)).dimension)
    (fun index => (simpleGroupAlgebraSubmoduleUnitaryData ρ hρ (summands index)).representation)
    (fun index => simpleGroupAlgebraSubmoduleSelectedUnitaryEquiv ρ hρ (summands index))
    g row column

/-- Every product of two continuous compact-representation coefficients has an exact finite expansion
in coefficients of selected positive-dimensional continuous irreducible unitary representations. -/
theorem matrixCoefficient_product_exists_finite_selectedUnitarySummand_expansion
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
                (Pi.single (finProdEquivFinMul n m (j, l)) 1) index)) summandColumn := by
  rcases compactRepresentation_exists_finite_simple_groupAlgebra_decomposition
      (matrixRepresentationTensorProduct ρ σ)
      (continuous_matrixRepresentationTensorProduct ρ hρ σ hσ) with
    ⟨summandCount, summands, decomposition, simple⟩
  let unitaryData (index : Fin summandCount) :
      ContinuousUnitaryIrreducibleMatrixRepresentation G := by
    letI : IsSimpleModule ℂ[G] (summands index) := simple index
    exact simpleGroupAlgebraSubmoduleUnitaryData
      (matrixRepresentationTensorProduct ρ σ)
      (continuous_matrixRepresentationTensorProduct ρ hρ σ hσ) (summands index)
  let dimension : Fin summandCount → ℕ := fun index => (unitaryData index).dimension
  let u : ∀ index, G →* Matrix (Fin (dimension index)) (Fin (dimension index)) ℂ :=
    fun index => (unitaryData index).representation
  let equivalence (index : Fin summandCount) : Representation.Equiv
      (Representation.ofModule (k := ℂ) (G := G) (summands index))
      (matrixRepresentation (u index)) := by
    letI : IsSimpleModule ℂ[G] (summands index) := simple index
    exact simpleGroupAlgebraSubmoduleSelectedUnitaryEquiv
      (matrixRepresentationTensorProduct ρ σ)
      (continuous_matrixRepresentationTensorProduct ρ hρ σ hσ) (summands index)
  refine ⟨summandCount, summands, decomposition, dimension, u, equivalence,
    fun index => (unitaryData index).dimension_pos,
    fun index => (unitaryData index).continuous_representation,
    fun index g => (unitaryData index).unitary_representation g,
    fun index => (unitaryData index).irreducible_representation, ?_⟩
  intro g i j k l
  rw [← matrixRepresentationTensorProduct_apply ρ σ g i j k l]
  exact finiteRepresentationDecomposition_reconstruct_coefficient_in_matrixSummands
    (matrixRepresentationTensorProduct ρ σ) summands decomposition dimension u equivalence g
    (finProdEquivFinMul n m (i, k)) (finProdEquivFinMul n m (j, l))

end

end Mathematics
end YangMills
