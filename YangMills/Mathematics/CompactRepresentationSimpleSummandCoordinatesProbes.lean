/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Mathematics.CompactRepresentationSimpleSummandCoordinates

/-!
# Hostile probes for simple-summand matrix coordinates
-/

namespace YangMills
namespace Mathematics
namespace CompactRepresentationSimpleSummandCoordinates
namespace Probes

open Module
open scoped MonoidAlgebra

noncomputable section

universe uG

variable {G : Type uG} [Group G]

/-- The scalar-restriction equivalence retains the exact underlying submodule vector. -/
theorem exact_restricted_equivalence_carrier
    {n : ℕ} (ρ : G →* Matrix (Fin n) (Fin n) ℂ)
    (S : Submodule ℂ[G] (matrixRepresentation ρ).asModule)
    (vector : RestrictScalars ℂ ℂ[G] S) :
    letI : Module ℂ (RestrictScalars ℂ ℂ[G] S) := RestrictScalars.module ℂ ℂ[G] S
    (restrictedGroupAlgebraSubmoduleLinearEquiv ρ S vector).val =
      (RestrictScalars.addEquiv ℂ ℂ[G] S vector).val := by
  rfl

/-- The inverse scalar-restriction equivalence also retains the exact carrier. -/
theorem exact_restricted_equivalence_inverse
    {n : ℕ} (ρ : G →* Matrix (Fin n) (Fin n) ℂ)
    (S : Submodule ℂ[G] (matrixRepresentation ρ).asModule) (vector : S) :
    letI : Module ℂ (RestrictScalars ℂ ℂ[G] S) := RestrictScalars.module ℂ ℂ[G] S
    (RestrictScalars.addEquiv ℂ ℂ[G] S)
      ((restrictedGroupAlgebraSubmoduleLinearEquiv ρ S).symm vector) = vector := by
  rfl

/-- Basis-coordinate matrices act exactly by the represented linear map in coordinates. -/
theorem exact_finite_basis_action
    {V : Type*} [AddCommMonoid V] [Module ℂ V]
    (τ : Representation ℂ G V) {d : ℕ} (basis : Basis (Fin d) ℂ V)
    (g : G) (vector : V) :
    Matrix.mulVec (finiteRepresentationMatrixInBasis τ basis g) (basis.repr vector) =
      basis.repr (τ g vector) :=
  LinearMap.toMatrix_mulVec_repr basis basis (τ g) vector

/-- The coordinate representation equivalence uses the unchanged basis coordinate map. -/
theorem exact_finite_basis_equivalence_carrier
    {V : Type*} [AddCommMonoid V] [Module ℂ V]
    (τ : Representation ℂ G V) {d : ℕ} (basis : Basis (Fin d) ℂ V)
    (vector : V) :
    finiteRepresentationMatrixInBasisEquiv τ basis vector = basis.equivFun vector := by
  rfl

variable [TopologicalSpace G]

/-- Every simple summand gets the exact finite-rank matrix dimension. -/
theorem exact_simple_coordinate_dimension
    {n : ℕ} (ρ : G →* Matrix (Fin n) (Fin n) ℂ) (hρ : Continuous ρ)
    (S : Submodule ℂ[G] (matrixRepresentation ρ).asModule)
    [IsSimpleModule ℂ[G] S] :
    (simpleGroupAlgebraSubmoduleCoordinateData ρ hρ S).dimension =
      Module.finrank ℂ S := by
  rfl

/-- Every simple summand has strictly positive selected coordinate dimension. -/
theorem positive_simple_coordinate_dimension
    {n : ℕ} (ρ : G →* Matrix (Fin n) (Fin n) ℂ) (hρ : Continuous ρ)
    (S : Submodule ℂ[G] (matrixRepresentation ρ).asModule)
    [IsSimpleModule ℂ[G] S] :
    0 < (simpleGroupAlgebraSubmoduleCoordinateData ρ hρ S).dimension :=
  (simpleGroupAlgebraSubmoduleCoordinateData ρ hρ S).dimension_pos

/-- Hostile dimension probe: changing the selected dimension away from the summand finrank is
contradictory. -/
theorem changed_simple_coordinate_dimension_blocked
    {n : ℕ} (ρ : G →* Matrix (Fin n) (Fin n) ℂ) (hρ : Continuous ρ)
    (S : Submodule ℂ[G] (matrixRepresentation ρ).asModule)
    [IsSimpleModule ℂ[G] S]
    (changed : (simpleGroupAlgebraSubmoduleCoordinateData ρ hρ S).dimension ≠
      Module.finrank ℂ S) : False :=
  changed rfl

/-- The selected coordinate representative is continuous. -/
theorem exact_simple_coordinate_continuity
    {n : ℕ} (ρ : G →* Matrix (Fin n) (Fin n) ℂ) (hρ : Continuous ρ)
    (S : Submodule ℂ[G] (matrixRepresentation ρ).asModule)
    [IsSimpleModule ℂ[G] S] :
    Continuous (simpleGroupAlgebraSubmoduleCoordinateData ρ hρ S).representation :=
  (simpleGroupAlgebraSubmoduleCoordinateData ρ hρ S).continuous_representation

/-- Simplicity is transported to exact coordinate irreducibility. -/
theorem exact_simple_coordinate_irreducibility
    {n : ℕ} (ρ : G →* Matrix (Fin n) (Fin n) ℂ) (hρ : Continuous ρ)
    (S : Submodule ℂ[G] (matrixRepresentation ρ).asModule)
    [IsSimpleModule ℂ[G] S] :
    Representation.IsIrreducible
      (matrixRepresentation (simpleGroupAlgebraSubmoduleCoordinateData ρ hρ S).representation) :=
  (simpleGroupAlgebraSubmoduleCoordinateData ρ hρ S).irreducible_representation

/-- Hostile probe: the selected simple coordinate representation cannot be reducible. -/
theorem reducible_simple_coordinate_blocked
    {n : ℕ} (ρ : G →* Matrix (Fin n) (Fin n) ℂ) (hρ : Continuous ρ)
    (S : Submodule ℂ[G] (matrixRepresentation ρ).asModule)
    [IsSimpleModule ℂ[G] S]
    (reducible : ¬ Representation.IsIrreducible
      (matrixRepresentation (simpleGroupAlgebraSubmoduleCoordinateData ρ hρ S).representation)) :
    False :=
  reducible (simpleGroupAlgebraSubmoduleCoordinateData ρ hρ S).irreducible_representation

variable [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
  [MeasurableSpace G] [BorelSpace G]

/-- Haar unitarization gives every simple summand the literal coordinate unitary law. -/
theorem exact_simple_summand_unitary
    {n : ℕ} (ρ : G →* Matrix (Fin n) (Fin n) ℂ) (hρ : Continuous ρ)
    (S : Submodule ℂ[G] (matrixRepresentation ρ).asModule)
    [IsSimpleModule ℂ[G] S] (g : G) :
    star ((simpleGroupAlgebraSubmoduleUnitaryData ρ hρ S).representation g) *
        (simpleGroupAlgebraSubmoduleUnitaryData ρ hρ S).representation g = 1 :=
  (simpleGroupAlgebraSubmoduleUnitaryData ρ hρ S).unitary_representation g

/-- The final unitary representative is explicitly equivalent to the unchanged simple module. -/
theorem exact_simple_summand_equivalence
    {n : ℕ} (ρ : G →* Matrix (Fin n) (Fin n) ℂ) (hρ : Continuous ρ)
    (S : Submodule ℂ[G] (matrixRepresentation ρ).asModule)
    [IsSimpleModule ℂ[G] S] :
    Nonempty (Representation.Equiv
      (Representation.ofModule (k := ℂ) (G := G) S)
      (matrixRepresentation
        (simpleGroupAlgebraSubmoduleUnitaryData ρ hρ S).representation)) :=
  simpleGroupAlgebraSubmoduleUnitaryData_equivalent ρ hρ S

/-- Hostile probe: failure of the unitary law contradicts the selected realization. -/
theorem failed_simple_summand_unitary_blocked
    {n : ℕ} (ρ : G →* Matrix (Fin n) (Fin n) ℂ) (hρ : Continuous ρ)
    (S : Submodule ℂ[G] (matrixRepresentation ρ).asModule)
    [IsSimpleModule ℂ[G] S] (g : G)
    (failed : star ((simpleGroupAlgebraSubmoduleUnitaryData ρ hρ S).representation g) *
        (simpleGroupAlgebraSubmoduleUnitaryData ρ hρ S).representation g ≠ 1) : False :=
  failed ((simpleGroupAlgebraSubmoduleUnitaryData ρ hρ S).unitary_representation g)

/-- The complete-reducibility decomposition can now be equipped summand-by-summand with explicit
unitary matrix coordinates and exact equivalences. -/
theorem every_finite_simple_decomposition_summand_has_unitary_coordinates
    {n : ℕ} (ρ : G →* Matrix (Fin n) (Fin n) ℂ) (hρ : Continuous ρ) :
    ∃ (summandCount : ℕ)
      (summands : Fin summandCount →
        Submodule ℂ[G] (matrixRepresentation ρ).asModule)
      (_ : (matrixRepresentation ρ).asModule ≃ₗ[ℂ[G]]
        Π₀ index : Fin summandCount, summands index),
      ∀ index, ∃ unitaryRepresentative :
          ContinuousUnitaryIrreducibleMatrixRepresentation G,
        Nonempty (Representation.Equiv
          (Representation.ofModule (k := ℂ) (G := G) (summands index))
          (matrixRepresentation unitaryRepresentative.representation)) :=
  compactRepresentation_exists_finite_simple_unitaryCoordinate_decomposition ρ hρ

end

end Probes
end CompactRepresentationSimpleSummandCoordinates
end Mathematics
end YangMills
