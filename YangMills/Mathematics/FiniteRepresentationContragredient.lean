/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Mathematics.FiniteRepresentationUnitaryCoefficientExpansion

/-!
# Contragredient coefficients and finite unitary expansion

For a finite matrix representation, the contragredient matrix is

`ρᵛ(g) = (ρ(g⁻¹))ᵀ`.

The transpose reverses the order introduced by inversion, so this is again a representation. For a
unitary representation its `(i,j)` coefficient is exactly the pointwise complex conjugate of
`ρ(g)ᵢⱼ`.

This file also packages one classically selected finite simple/unitary decomposition for every
continuous compact representation. Applying it to the contragredient proves that the pointwise star
of every unitary coefficient is a finite weighted sum of positive-dimensional continuous
irreducible unitary coefficients. This is finite star-closure data, not point separation or density.
-/

namespace YangMills
namespace Mathematics

open Module
open scoped MonoidAlgebra

noncomputable section

universe uG

/-- The contragredient finite matrix representation `g ↦ (ρ(g⁻¹))ᵀ`. -/
noncomputable def matrixRepresentationContragredient
    {G : Type uG} [Group G] {n : ℕ}
    (ρ : G →* Matrix (Fin n) (Fin n) ℂ) :
    G →* Matrix (Fin n) (Fin n) ℂ where
  toFun g := (ρ (g⁻¹)).transpose
  map_one' := by simp
  map_mul' g h := by
    simp only [mul_inv_rev, map_mul]
    rw [Matrix.transpose_mul]

/-- Exact contragredient coefficient convention. -/
@[simp]
theorem matrixRepresentationContragredient_apply
    {G : Type uG} [Group G] {n : ℕ}
    (ρ : G →* Matrix (Fin n) (Fin n) ℂ) (g : G) (i j : Fin n) :
    matrixRepresentationContragredient ρ g i j = ρ (g⁻¹) j i :=
  rfl

/-- Continuity of a representation implies continuity of its contragredient. -/
theorem continuous_matrixRepresentationContragredient
    {G : Type uG} [Group G] [TopologicalSpace G] [ContinuousInv G] {n : ℕ}
    (ρ : G →* Matrix (Fin n) (Fin n) ℂ) (hρ : Continuous ρ) :
    Continuous (matrixRepresentationContragredient ρ) := by
  change Continuous (fun g i j => ρ (g⁻¹) j i)
  fun_prop

/-- For a coordinate-unitary representation, each contragredient coefficient is exactly the
pointwise scalar star of the original coefficient. -/
theorem matrixRepresentationContragredient_apply_eq_star
    {G : Type uG} [Group G] {n : ℕ}
    (ρ : G →* Matrix (Fin n) (Fin n) ℂ)
    (unitaryρ : ∀ g, star (ρ g) * ρ g = 1)
    (g : G) (i j : Fin n) :
    matrixRepresentationContragredient ρ g i j = star (ρ g i j) :=
  unitaryMatrixRepresentation_inv_apply ρ unitaryρ g j i

/-- One selected finite decomposition of a continuous compact matrix representation into explicit
positive-dimensional continuous irreducible unitary matrix representatives. -/
structure CompactRepresentationSelectedUnitaryDecomposition
    {G : Type uG} [Group G] [TopologicalSpace G] (n : ℕ)
    (ρ : G →* Matrix (Fin n) (Fin n) ℂ) where
  count : ℕ
  summands : Fin count → Submodule ℂ[G] (matrixRepresentation ρ).asModule
  decomposition : (matrixRepresentation ρ).asModule ≃ₗ[ℂ[G]] Π₀ i, summands i
  dimension : Fin count → ℕ
  representation : ∀ i, G →* Matrix (Fin (dimension i)) (Fin (dimension i)) ℂ
  equivalence : ∀ i, Representation.Equiv
    (Representation.ofModule (k := ℂ) (G := G) (summands i))
    (matrixRepresentation (representation i))
  dimension_pos : ∀ i, 0 < dimension i
  continuous_representation : ∀ i, Continuous (representation i)
  unitary_representation : ∀ i g, star (representation i g) * representation i g = 1
  irreducible_representation : ∀ i,
    Representation.IsIrreducible (matrixRepresentation (representation i))

/-- Classical selection of the finite simple decomposition and the already constructed unitary
coordinates for all its summands. This selection does not enumerate the whole unitary dual. -/
noncomputable def compactRepresentationSelectedUnitaryDecomposition
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    {n : ℕ} (ρ : G →* Matrix (Fin n) (Fin n) ℂ) (hρ : Continuous ρ) :
    CompactRepresentationSelectedUnitaryDecomposition n ρ := by
  let existsCount := compactRepresentation_exists_finite_simple_groupAlgebra_decomposition ρ hρ
  let count := existsCount.choose
  let existsSummands := existsCount.choose_spec
  let summands := existsSummands.choose
  let existsDecomposition := existsSummands.choose_spec
  let decomposition := existsDecomposition.choose
  let simple := existsDecomposition.choose_spec
  let data (i : Fin count) : ContinuousUnitaryIrreducibleMatrixRepresentation G := by
    letI : IsSimpleModule ℂ[G] (summands i) := simple i
    exact simpleGroupAlgebraSubmoduleUnitaryData ρ hρ (summands i)
  let dimension := fun i => (data i).dimension
  let representation : ∀ i, G →* Matrix (Fin (dimension i)) (Fin (dimension i)) ℂ :=
    fun i => (data i).representation
  let equivalence (i : Fin count) : Representation.Equiv
      (Representation.ofModule (k := ℂ) (G := G) (summands i))
      (matrixRepresentation (representation i)) := by
    letI : IsSimpleModule ℂ[G] (summands i) := simple i
    exact simpleGroupAlgebraSubmoduleSelectedUnitaryEquiv ρ hρ (summands i)
  exact {
    count := count
    summands := summands
    decomposition := decomposition
    dimension := dimension
    representation := representation
    equivalence := equivalence
    dimension_pos := fun i => (data i).dimension_pos
    continuous_representation := fun i => (data i).continuous_representation
    unitary_representation := fun i => (data i).unitary_representation
    irreducible_representation := fun i => (data i).irreducible_representation }

/-- Every coefficient of the original representation has an exact finite expansion in the selected
irreducible unitary summand coefficients. -/
theorem compactRepresentationSelectedUnitaryDecomposition_coefficient_expansion
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    {n : ℕ} (ρ : G →* Matrix (Fin n) (Fin n) ℂ) (hρ : Continuous ρ)
    (g : G) (row column : Fin n) :
    ρ g row column = ∑ index, ∑ summandRow, ∑ summandColumn,
      finiteRepresentationDecompositionOutputCoordinate ρ
        (compactRepresentationSelectedUnitaryDecomposition ρ hρ).summands
        (compactRepresentationSelectedUnitaryDecomposition ρ hρ).decomposition index row
        (restrictedGroupAlgebraSubmoduleLinearEquiv ρ
          ((compactRepresentationSelectedUnitaryDecomposition ρ hρ).summands index)
          (((compactRepresentationSelectedUnitaryDecomposition ρ hρ).equivalence index).symm
            (Pi.single summandRow 1))) *
      (compactRepresentationSelectedUnitaryDecomposition ρ hρ).representation index g
        summandRow summandColumn *
      (compactRepresentationSelectedUnitaryDecomposition ρ hρ).equivalence index
        ((restrictedGroupAlgebraSubmoduleLinearEquiv ρ
          ((compactRepresentationSelectedUnitaryDecomposition ρ hρ).summands index)).symm
          (finiteRepresentationDecompositionInput ρ
            (compactRepresentationSelectedUnitaryDecomposition ρ hρ).summands
            (compactRepresentationSelectedUnitaryDecomposition ρ hρ).decomposition
            (Pi.single column 1) index)) summandColumn :=
  finiteRepresentationDecomposition_reconstruct_coefficient_in_matrixSummands
    ρ (compactRepresentationSelectedUnitaryDecomposition ρ hρ).summands
    (compactRepresentationSelectedUnitaryDecomposition ρ hρ).decomposition
    (compactRepresentationSelectedUnitaryDecomposition ρ hρ).dimension
    (compactRepresentationSelectedUnitaryDecomposition ρ hρ).representation
    (compactRepresentationSelectedUnitaryDecomposition ρ hρ).equivalence g row column

/-- The scalar star of every coefficient of a continuous unitary representation has an exact finite
expansion in selected positive-dimensional continuous irreducible unitary coefficients. -/
theorem matrixCoefficient_star_finite_selectedUnitary_expansion
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    {n : ℕ} (ρ : G →* Matrix (Fin n) (Fin n) ℂ) (hρ : Continuous ρ)
    (unitaryρ : ∀ g, star (ρ g) * ρ g = 1)
    (g : G) (row column : Fin n) :
    star (ρ g row column) = ∑ index, ∑ summandRow, ∑ summandColumn,
      finiteRepresentationDecompositionOutputCoordinate (matrixRepresentationContragredient ρ)
        (compactRepresentationSelectedUnitaryDecomposition
          (matrixRepresentationContragredient ρ)
          (continuous_matrixRepresentationContragredient ρ hρ)).summands
        (compactRepresentationSelectedUnitaryDecomposition
          (matrixRepresentationContragredient ρ)
          (continuous_matrixRepresentationContragredient ρ hρ)).decomposition index row
        (restrictedGroupAlgebraSubmoduleLinearEquiv (matrixRepresentationContragredient ρ)
          ((compactRepresentationSelectedUnitaryDecomposition
            (matrixRepresentationContragredient ρ)
            (continuous_matrixRepresentationContragredient ρ hρ)).summands index)
          (((compactRepresentationSelectedUnitaryDecomposition
            (matrixRepresentationContragredient ρ)
            (continuous_matrixRepresentationContragredient ρ hρ)).equivalence index).symm
            (Pi.single summandRow 1))) *
      (compactRepresentationSelectedUnitaryDecomposition
        (matrixRepresentationContragredient ρ)
        (continuous_matrixRepresentationContragredient ρ hρ)).representation index g
        summandRow summandColumn *
      (compactRepresentationSelectedUnitaryDecomposition
        (matrixRepresentationContragredient ρ)
        (continuous_matrixRepresentationContragredient ρ hρ)).equivalence index
        ((restrictedGroupAlgebraSubmoduleLinearEquiv (matrixRepresentationContragredient ρ)
          ((compactRepresentationSelectedUnitaryDecomposition
            (matrixRepresentationContragredient ρ)
            (continuous_matrixRepresentationContragredient ρ hρ)).summands index)).symm
          (finiteRepresentationDecompositionInput (matrixRepresentationContragredient ρ)
            (compactRepresentationSelectedUnitaryDecomposition
              (matrixRepresentationContragredient ρ)
              (continuous_matrixRepresentationContragredient ρ hρ)).summands
            (compactRepresentationSelectedUnitaryDecomposition
              (matrixRepresentationContragredient ρ)
              (continuous_matrixRepresentationContragredient ρ hρ)).decomposition
            (Pi.single column 1) index)) summandColumn := by
  rw [← matrixRepresentationContragredient_apply_eq_star ρ unitaryρ g row column]
  exact compactRepresentationSelectedUnitaryDecomposition_coefficient_expansion
    (matrixRepresentationContragredient ρ)
    (continuous_matrixRepresentationContragredient ρ hρ) g row column

end

end Mathematics
end YangMills
