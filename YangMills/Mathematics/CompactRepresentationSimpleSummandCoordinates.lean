/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Mathematics.CompactRepresentationCompleteReducibility
import YangMills.Mathematics.CompactRepresentationUnitaryCoordinateRealization

/-!
# Explicit unitary coordinates for simple compact-representation summands

Complete reducibility produces simple submodules of the group-algebra module associated to a
continuous compact matrix representation. This file gives each such simple summand finite matrix
coordinates. It carefully reconciles Mathlib's `RestrictScalars` carrier with the original
submodule, proves continuity of every coordinate, transports simplicity to irreducibility, and then
applies Haar unitarization.

Thus every simple summand has an explicitly equivalent continuous irreducible unitary matrix
representative. This is finite-dimensional realization infrastructure. It does not prove that all
irreducible classes occur in one original representation, that representations separate points, or
that matrix coefficients are dense.
-/

namespace YangMills
namespace Mathematics

open Module
open scoped MonoidAlgebra

noncomputable section

universe uG

/-- The scalar-restricted carrier of a group-algebra submodule is linearly equivalent to the
unchanged submodule. -/
noncomputable def restrictedGroupAlgebraSubmoduleLinearEquiv
    {G : Type uG} [Group G] {n : ℕ} (ρ : G →* Matrix (Fin n) (Fin n) ℂ)
    (S : Submodule ℂ[G] (matrixRepresentation ρ).asModule) :
    letI : Module ℂ (RestrictScalars ℂ ℂ[G] S) := RestrictScalars.module ℂ ℂ[G] S
    RestrictScalars ℂ ℂ[G] S ≃ₗ[ℂ] S := by
  letI : Module ℂ (RestrictScalars ℂ ℂ[G] S) := RestrictScalars.module ℂ ℂ[G] S
  exact
    { toFun := RestrictScalars.addEquiv ℂ ℂ[G] S
      invFun := (RestrictScalars.addEquiv ℂ ℂ[G] S).symm
      left_inv := (RestrictScalars.addEquiv ℂ ℂ[G] S).symm_apply_apply
      right_inv := (RestrictScalars.addEquiv ℂ ℂ[G] S).apply_symm_apply
      map_add' := (RestrictScalars.addEquiv ℂ ℂ[G] S).map_add
      map_smul' := by
        intro c x
        apply Subtype.ext
        change ((algebraMap ℂ ℂ[G] c) •
          (RestrictScalars.addEquiv ℂ ℂ[G] S x : S)).val =
          (c • (RestrictScalars.addEquiv ℂ ℂ[G] S x : S)).val
        change (matrixRepresentation ρ).asModuleEquiv
          ((algebraMap ℂ ℂ[G] c) •
            ((RestrictScalars.addEquiv ℂ ℂ[G] S x).val :
              (matrixRepresentation ρ).asModule)) = _
        rw [Representation.asModuleEquiv_map_smul]
        rw [(matrixRepresentation ρ).asAlgebraHom.commutes c]
        rfl }

/-- A `Fin (finrank ℂ S)` basis on the exact scalar-restricted carrier used by `ofModule`. -/
noncomputable def restrictedGroupAlgebraSubmoduleBasis
    {G : Type uG} [Group G] {n : ℕ} (ρ : G →* Matrix (Fin n) (Fin n) ℂ)
    (S : Submodule ℂ[G] (matrixRepresentation ρ).asModule) :
    letI : Module ℂ (RestrictScalars ℂ ℂ[G] S) := RestrictScalars.module ℂ ℂ[G] S
    Basis (Fin (Module.finrank ℂ S)) ℂ (RestrictScalars ℂ ℂ[G] S) := by
  letI : Module ℂ (RestrictScalars ℂ ℂ[G] S) := RestrictScalars.module ℂ ℂ[G] S
  letI : AddCommMonoid S := S.addCommGroup.toAddCommMonoid
  letI : Module ℂ S := S.module'
  letI : FiniteDimensional ℂ S := FiniteDimensional.of_injective
    (S.subtype.restrictScalars ℂ) S.injective_subtype
  exact (Module.finBasis ℂ S).map
    (restrictedGroupAlgebraSubmoduleLinearEquiv ρ S).symm

/-- Matrix coordinates of an arbitrary finite-basis representation. -/
noncomputable def finiteRepresentationMatrixInBasis
    {G : Type uG} [Group G] {V : Type*} [AddCommMonoid V] [Module ℂ V]
    (τ : Representation ℂ G V) {d : ℕ} (basis : Basis (Fin d) ℂ V) :
    G →* Matrix (Fin d) (Fin d) ℂ where
  toFun g := LinearMap.toMatrix basis basis (τ g)
  map_one' := by simp
  map_mul' g h := by
    rw [map_mul]
    exact LinearMap.toMatrix_comp basis basis basis _ _

/-- The basis-coordinate matrix representation is exactly equivalent to the original
representation. -/
noncomputable def finiteRepresentationMatrixInBasisEquiv
    {G : Type uG} [Group G] {V : Type*} [AddCommMonoid V] [Module ℂ V]
    (τ : Representation ℂ G V) {d : ℕ} (basis : Basis (Fin d) ℂ V) :
    Representation.Equiv τ
      (matrixRepresentation (finiteRepresentationMatrixInBasis τ basis)) :=
  Representation.Equiv.mk basis.equivFun (fun g => by
    apply LinearMap.ext
    intro vector
    change basis.repr (τ g vector) = Matrix.mulVec
      (LinearMap.toMatrix basis basis (τ g)) (basis.repr vector)
    rw [LinearMap.toMatrix_mulVec_repr])

/-- If every orbit map is continuous, then all entries of the finite-basis matrix representation
are continuous. -/
theorem continuous_finiteRepresentationMatrixInBasis
    {G : Type uG} [Group G] [TopologicalSpace G]
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
    (τ : Representation ℂ G V) (orbitContinuous : ∀ v, Continuous (fun g => τ g v))
    {d : ℕ} (basis : Basis (Fin d) ℂ V) :
    Continuous (finiteRepresentationMatrixInBasis τ basis) := by
  change Continuous (fun g row column =>
    LinearMap.toMatrix basis basis (τ g) row column)
  rw [continuous_pi_iff]
  intro row
  rw [continuous_pi_iff]
  intro column
  simp only [LinearMap.toMatrix_apply]
  change Continuous ((basis.coord row) ∘ fun g => τ g (basis column))
  exact (basis.coord row).continuous_of_finiteDimensional.comp
    (orbitContinuous (basis column))

/-- The coordinate matrix representation of one group-algebra submodule. -/
noncomputable def simpleGroupAlgebraSubmoduleCoordinateRepresentation
    {G : Type uG} [Group G] {n : ℕ} (ρ : G →* Matrix (Fin n) (Fin n) ℂ)
    (S : Submodule ℂ[G] (matrixRepresentation ρ).asModule) :
    G →* Matrix (Fin (Module.finrank ℂ S)) (Fin (Module.finrank ℂ S)) ℂ := by
  letI : Module ℂ (RestrictScalars ℂ ℂ[G] S) := RestrictScalars.module ℂ ℂ[G] S
  exact finiteRepresentationMatrixInBasis
    (Representation.ofModule (k := ℂ) (G := G) S)
    (restrictedGroupAlgebraSubmoduleBasis ρ S)

/-- The coordinate representation of every simple group-algebra submodule is irreducible. -/
theorem simpleGroupAlgebraSubmoduleCoordinateRepresentation_irreducible
    {G : Type uG} [Group G] {n : ℕ} (ρ : G →* Matrix (Fin n) (Fin n) ℂ)
    (S : Submodule ℂ[G] (matrixRepresentation ρ).asModule)
    [IsSimpleModule ℂ[G] S] :
    Representation.IsIrreducible
      (matrixRepresentation (simpleGroupAlgebraSubmoduleCoordinateRepresentation ρ S)) := by
  letI groupCarrier : AddCommGroup (RestrictScalars ℂ ℂ[G] S) :=
    instAddCommGroupRestrictScalars ℂ ℂ[G] S
  letI : AddCommMonoid (RestrictScalars ℂ ℂ[G] S) := groupCarrier.toAddCommMonoid
  letI : Module ℂ (RestrictScalars ℂ ℂ[G] S) := RestrictScalars.module ℂ ℂ[G] S
  exact (representation_isIrreducible_iff_of_equiv
    (finiteRepresentationMatrixInBasisEquiv
      (Representation.ofModule (k := ℂ) (G := G) S)
      (restrictedGroupAlgebraSubmoduleBasis ρ S))).mp
    ((Representation.isSimpleModule_iff_irreducible_ofModule
      (k := ℂ) (G := G) S).mp inferInstance)

/-- The scalar-restricted submodule includes linearly and injectively into the original coordinate
space. -/
def restrictedGroupAlgebraSubmoduleInclusion
    {G : Type uG} [Group G] {n : ℕ} (ρ : G →* Matrix (Fin n) (Fin n) ℂ)
    (S : Submodule ℂ[G] (matrixRepresentation ρ).asModule) :
    letI : Module ℂ (RestrictScalars ℂ ℂ[G] S) := RestrictScalars.module ℂ ℂ[G] S
    RestrictScalars ℂ ℂ[G] S →ₗ[ℂ] (Fin n → ℂ) := by
  letI : Module ℂ (RestrictScalars ℂ ℂ[G] S) := RestrictScalars.module ℂ ℂ[G] S
  exact
    { toFun := fun x => (RestrictScalars.addEquiv ℂ ℂ[G] S x).val
      map_add' := fun _ _ => rfl
      map_smul' := by
        intro c x
        change ((RestrictScalars.addEquiv ℂ ℂ[G] S) (c • x)).val =
          c • ((RestrictScalars.addEquiv ℂ ℂ[G] S x).val : Fin n → ℂ)
        rw [RestrictScalars.addEquiv_map_smul]
        change (matrixRepresentation ρ).asModuleEquiv
          ((algebraMap ℂ ℂ[G] c) •
            ((RestrictScalars.addEquiv ℂ ℂ[G] S x).val :
              (matrixRepresentation ρ).asModule)) = _
        rw [Representation.asModuleEquiv_map_smul]
        rw [(matrixRepresentation ρ).asAlgebraHom.commutes c]
        rfl }

/-- The scalar-restricted inclusion has no kernel. -/
theorem restrictedGroupAlgebraSubmoduleInclusion_injective
    {G : Type uG} [Group G] {n : ℕ} (ρ : G →* Matrix (Fin n) (Fin n) ℂ)
    (S : Submodule ℂ[G] (matrixRepresentation ρ).asModule) :
    letI : Module ℂ (RestrictScalars ℂ ℂ[G] S) := RestrictScalars.module ℂ ℂ[G] S
    Function.Injective (restrictedGroupAlgebraSubmoduleInclusion ρ S) := by
  letI : Module ℂ (RestrictScalars ℂ ℂ[G] S) := RestrictScalars.module ℂ ℂ[G] S
  intro x y equality
  apply (RestrictScalars.addEquiv ℂ ℂ[G] S).injective
  apply Subtype.ext
  exact equality

/-- The matrix-coordinate representative of every group-algebra submodule is continuous when the
original matrix representation is continuous. -/
theorem continuous_simpleGroupAlgebraSubmoduleCoordinateRepresentation
    {G : Type uG} [Group G] [TopologicalSpace G]
    {n : ℕ} (ρ : G →* Matrix (Fin n) (Fin n) ℂ) (hρ : Continuous ρ)
    (S : Submodule ℂ[G] (matrixRepresentation ρ).asModule) :
    Continuous (simpleGroupAlgebraSubmoduleCoordinateRepresentation ρ S) := by
  let additiveInclusion : RestrictScalars ℂ ℂ[G] S →+ (Fin n → ℂ) :=
    { toFun := fun x => (RestrictScalars.addEquiv ℂ ℂ[G] S x).val
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have additiveInclusion_injective : Function.Injective additiveInclusion := by
    intro x y equality
    apply (RestrictScalars.addEquiv ℂ ℂ[G] S).injective
    apply Subtype.ext
    exact equality
  letI normedCarrier : NormedAddCommGroup (RestrictScalars ℂ ℂ[G] S) :=
    NormedAddCommGroup.induced _ (Fin n → ℂ) additiveInclusion
      additiveInclusion_injective
  letI groupCarrier : AddCommGroup (RestrictScalars ℂ ℂ[G] S) :=
    normedCarrier.toAddCommGroup
  letI : AddCommMonoid (RestrictScalars ℂ ℂ[G] S) := groupCarrier.toAddCommMonoid
  letI : Module ℂ (RestrictScalars ℂ ℂ[G] S) := RestrictScalars.module ℂ ℂ[G] S
  let inclusion : RestrictScalars ℂ ℂ[G] S →ₗ[ℂ] (Fin n → ℂ) :=
    { toFun := additiveInclusion
      map_add' := additiveInclusion.map_add
      map_smul' := by
        intro c x
        change ((RestrictScalars.addEquiv ℂ ℂ[G] S) (c • x)).val =
          c • ((RestrictScalars.addEquiv ℂ ℂ[G] S x).val : Fin n → ℂ)
        rw [RestrictScalars.addEquiv_map_smul]
        change (matrixRepresentation ρ).asModuleEquiv
          ((algebraMap ℂ ℂ[G] c) •
            ((RestrictScalars.addEquiv ℂ ℂ[G] S x).val :
              (matrixRepresentation ρ).asModule)) = _
        rw [Representation.asModuleEquiv_map_smul]
        rw [(matrixRepresentation ρ).asAlgebraHom.commutes c]
        rfl }
  letI : @NormedSpace ℂ (RestrictScalars ℂ ℂ[G] S) _
      normedCarrier.toSeminormedAddCommGroup :=
    NormedSpace.induced ℂ _ (Fin n → ℂ) inclusion
  letI : FiniteDimensional ℂ (RestrictScalars ℂ ℂ[G] S) :=
    FiniteDimensional.of_injective inclusion additiveInclusion_injective
  apply continuous_finiteRepresentationMatrixInBasis
  intro vector
  rw [continuous_induced_rng]
  change Continuous (fun g => inclusion
    ((Representation.ofModule (k := ℂ) (G := G) S) g vector))
  have orbitEquality :
      (fun g => inclusion
        ((Representation.ofModule (k := ℂ) (G := G) S) g vector)) =
      fun g => Matrix.mulVec (ρ g) (inclusion vector) := by
    funext g
    change ((RestrictScalars.addEquiv ℂ ℂ[G] S)
      ((Representation.ofModule (k := ℂ) (G := G) S) g vector)).val = _
    have action : (RestrictScalars.addEquiv ℂ ℂ[G] S)
        ((Representation.ofModule (k := ℂ) (G := G) S) g vector) =
        (MonoidAlgebra.single g (1 : ℂ)) •
          (RestrictScalars.addEquiv ℂ ℂ[G] S vector : S) := by
      rw [← one_smul ℂ
        ((Representation.ofModule (k := ℂ) (G := G) S) g vector),
        ← LinearMap.smul_apply,
        ← Representation.asAlgebraHom_single]
      rw [Representation.ofModule_asAlgebraHom_apply_apply]
      simp
    rw [action]
    change (MonoidAlgebra.single g (1 : ℂ)) •
      ((RestrictScalars.addEquiv ℂ ℂ[G] S vector).val :
        (matrixRepresentation ρ).asModule) = _
    rw [Representation.single_smul]
    simp only [one_smul, matrixRepresentation_apply, Matrix.toLin'_apply]
    change Matrix.mulVec (ρ g)
      (RestrictScalars.addEquiv ℂ ℂ[G] S vector).val =
      Matrix.mulVec (ρ g) (RestrictScalars.addEquiv ℂ ℂ[G] S vector).val
    rfl
  rw [orbitEquality]
  fun_prop

/-- A simple summand, in explicit continuous irreducible matrix coordinates before unitary
selection. -/
noncomputable def simpleGroupAlgebraSubmoduleCoordinateData
    {G : Type uG} [Group G] [TopologicalSpace G]
    {n : ℕ} (ρ : G →* Matrix (Fin n) (Fin n) ℂ) (hρ : Continuous ρ)
    (S : Submodule ℂ[G] (matrixRepresentation ρ).asModule)
    [IsSimpleModule ℂ[G] S] : ContinuousIrreducibleMatrixRepresentation G := by
  letI : AddCommMonoid S := S.addCommGroup.toAddCommMonoid
  letI : Module ℂ S := S.module'
  letI : Nontrivial S := IsSimpleModule.nontrivial ℂ[G] S
  letI : FiniteDimensional ℂ S := FiniteDimensional.of_injective
    (S.subtype.restrictScalars ℂ) S.injective_subtype
  exact
    { dimension := Module.finrank ℂ S
      dimension_pos := Module.finrank_pos
      representation := simpleGroupAlgebraSubmoduleCoordinateRepresentation ρ S
      continuous_representation :=
        continuous_simpleGroupAlgebraSubmoduleCoordinateRepresentation ρ hρ S
      irreducible_representation :=
        simpleGroupAlgebraSubmoduleCoordinateRepresentation_irreducible ρ S }

/-- Haar unitarization of the explicit coordinates for a simple summand. -/
noncomputable def simpleGroupAlgebraSubmoduleUnitaryData
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    {n : ℕ} (ρ : G →* Matrix (Fin n) (Fin n) ℂ) (hρ : Continuous ρ)
    (S : Submodule ℂ[G] (matrixRepresentation ρ).asModule)
    [IsSimpleModule ℂ[G] S] : ContinuousUnitaryIrreducibleMatrixRepresentation G :=
  (simpleGroupAlgebraSubmoduleCoordinateData ρ hρ S).toUnitary

/-- The selected unitary matrix representative remains exactly equivalent to the original simple
`ofModule` summand representation. -/
theorem simpleGroupAlgebraSubmoduleUnitaryData_equivalent
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    {n : ℕ} (ρ : G →* Matrix (Fin n) (Fin n) ℂ) (hρ : Continuous ρ)
    (S : Submodule ℂ[G] (matrixRepresentation ρ).asModule)
    [IsSimpleModule ℂ[G] S] :
    Nonempty (Representation.Equiv
      (Representation.ofModule (k := ℂ) (G := G) S)
      (matrixRepresentation
        (simpleGroupAlgebraSubmoduleUnitaryData ρ hρ S).representation)) := by
  letI : Module ℂ (RestrictScalars ℂ ℂ[G] S) := RestrictScalars.module ℂ ℂ[G] S
  exact ⟨(finiteRepresentationMatrixInBasisEquiv
      (Representation.ofModule (k := ℂ) (G := G) S)
      (restrictedGroupAlgebraSubmoduleBasis ρ S)).trans
    (compactRepresentationUnitarizingRepresentationEquiv
      (simpleGroupAlgebraSubmoduleCoordinateRepresentation ρ S)
      (continuous_simpleGroupAlgebraSubmoduleCoordinateRepresentation ρ hρ S))⟩

/-- The selected complete-reducibility decomposition can be equipped summand-by-summand with
explicit continuous irreducible unitary matrix representatives and exact equivalences. This selects
the decomposition constructed by `compactRepresentation_exists_finite_simple_groupAlgebra_decomposition`;
it does not quantify over arbitrary caller-supplied decompositions. -/
theorem compactRepresentation_exists_finite_simple_unitaryCoordinate_decomposition
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
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
          (matrixRepresentation unitaryRepresentative.representation)) := by
  rcases compactRepresentation_exists_finite_simple_groupAlgebra_decomposition ρ hρ with
    ⟨summandCount, summands, decomposition, simple⟩
  refine ⟨summandCount, summands, decomposition, ?_⟩
  intro index
  letI : IsSimpleModule ℂ[G] (summands index) := simple index
  exact ⟨simpleGroupAlgebraSubmoduleUnitaryData ρ hρ (summands index),
    simpleGroupAlgebraSubmoduleUnitaryData_equivalent ρ hρ (summands index)⟩

end

end Mathematics
end YangMills
