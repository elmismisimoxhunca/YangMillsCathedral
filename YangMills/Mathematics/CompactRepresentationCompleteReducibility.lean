/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import Mathlib.RepresentationTheory.Semisimple
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import YangMills.Mathematics.CompactRepresentationAveragedNormedRealization

/-!
# Complete reducibility of compact finite-dimensional matrix representations

Haar averaging gives every continuous finite-dimensional complex matrix representation of a compact
group an invariant positive inner product. The orthogonal complement of any invariant subspace is
therefore invariant. In finite dimension the subspace and its orthogonal complement are algebraic
complements, proving semisimplicity and a finite decomposition into simple group-algebra modules.

This is the complete-reducibility consequence of Haar averaging. It is a prerequisite for proving
that products of irreducible matrix coefficients remain in the algebraic irreducible-coefficient
span. It does not prove that finite-dimensional representations separate group points, and it does
not prove Peter–Weyl density or completeness.
-/

namespace YangMills
namespace Mathematics

open scoped MonoidAlgebra

noncomputable section

universe uG

/-- The invariant orthogonal-complement subrepresentation formed using the exact Haar-averaged
inner product. -/
noncomputable def compactRepresentationOrthogonalComplement
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    {n : ℕ} (ρ : G →* Matrix (Fin n) (Fin n) ℂ) (hρ : Continuous ρ)
    (subrepresentation : Subrepresentation (matrixRepresentation ρ)) :
    Subrepresentation (matrixRepresentation ρ) := by
  letI := compactRepresentationAveragedNormedAddCommGroup ρ hρ
  letI := compactRepresentationAveragedNormedSpace ρ hρ
  letI := compactRepresentationAveragedInnerProductSpace ρ hρ
  exact
    { toSubmodule := subrepresentation.toSubmoduleᗮ
      apply_mem_toSubmodule := fun g vector vector_orthogonal => by
        rw [Submodule.mem_orthogonal'] at vector_orthogonal ⊢
        intro subspaceVector subspaceVector_mem
        let prior := Matrix.mulVec (ρ (g⁻¹)) subspaceVector
        have prior_mem : prior ∈ subrepresentation :=
          subrepresentation.apply_mem_toSubmodule (g⁻¹) subspaceVector_mem
        have recover : Matrix.mulVec (ρ g) prior = subspaceVector := by
          dsimp [prior]
          rw [Matrix.mulVec_mulVec, ← map_mul, mul_inv_cancel, map_one,
            Matrix.one_mulVec]
        rw [← recover]
        change compactRepresentationAveragedPairing ρ
          (Matrix.mulVec (ρ g) vector) (Matrix.mulVec (ρ g) prior) = 0
        rw [compactRepresentationAveragedPairing_invariant]
        change inner ℂ vector prior = 0
        exact vector_orthogonal prior prior_mem }

/-- Exact membership in the invariant complement is orthogonality, for the unchanged Haar-averaged
pairing, to every vector in the original subrepresentation. -/
theorem mem_compactRepresentationOrthogonalComplement_iff
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    {n : ℕ} (ρ : G →* Matrix (Fin n) (Fin n) ℂ) (hρ : Continuous ρ)
    (subrepresentation : Subrepresentation (matrixRepresentation ρ))
    (vector : Fin n → ℂ) :
    vector ∈ compactRepresentationOrthogonalComplement ρ hρ subrepresentation ↔
      ∀ subspaceVector ∈ subrepresentation,
        compactRepresentationAveragedPairing ρ vector subspaceVector = 0 := by
  letI := compactRepresentationAveragedNormedAddCommGroup ρ hρ
  letI := compactRepresentationAveragedNormedSpace ρ hρ
  letI := compactRepresentationAveragedInnerProductSpace ρ hρ
  change vector ∈ subrepresentation.toSubmoduleᗮ ↔ _
  rw [Submodule.mem_orthogonal']
  rfl

/-- A subrepresentation and its invariant Haar-orthogonal complement are exact algebraic
complements. Finite dimensionality is used only for the spanning half of this assertion. -/
theorem compactRepresentationOrthogonalComplement_isCompl
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    {n : ℕ} (ρ : G →* Matrix (Fin n) (Fin n) ℂ) (hρ : Continuous ρ)
    (subrepresentation : Subrepresentation (matrixRepresentation ρ)) :
    IsCompl subrepresentation
      (compactRepresentationOrthogonalComplement ρ hρ subrepresentation) := by
  letI := compactRepresentationAveragedNormedAddCommGroup ρ hρ
  letI := compactRepresentationAveragedNormedSpace ρ hρ
  letI := compactRepresentationAveragedInnerProductSpace ρ hρ
  have dimension_bound : Module.finrank ℂ (Fin n → ℂ) ≤
      Module.finrank ℂ subrepresentation.toSubmodule +
        Module.finrank ℂ subrepresentation.toSubmoduleᗮ := by
    rw [Submodule.finrank_add_finrank_orthogonal]
  have module_complement :
      IsCompl subrepresentation.toSubmodule subrepresentation.toSubmoduleᗮ :=
    (Submodule.isCompl_iff_disjoint _ _ dimension_bound).mpr
      subrepresentation.toSubmodule.orthogonal_disjoint
  constructor
  · rw [disjoint_iff]
    apply Subrepresentation.toSubmodule_injective
    change subrepresentation.toSubmodule ⊓ subrepresentation.toSubmoduleᗮ = ⊥
    exact module_complement.disjoint.eq_bot
  · rw [codisjoint_iff]
    apply Subrepresentation.toSubmodule_injective
    change subrepresentation.toSubmodule ⊔ subrepresentation.toSubmoduleᗮ = ⊤
    exact module_complement.codisjoint.eq_top

/-- Every continuous finite-dimensional complex matrix representation of a compact group is
semisimple. No irreducibility, unitarity, or positive-dimension premise is needed. -/
theorem compactRepresentation_isSemisimple
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    {n : ℕ} (ρ : G →* Matrix (Fin n) (Fin n) ℂ) (hρ : Continuous ρ) :
    Representation.IsSemisimpleRepresentation (matrixRepresentation ρ) := by
  change ComplementedLattice (Subrepresentation (matrixRepresentation ρ))
  rw [complementedLattice_iff]
  intro subrepresentation
  exact ⟨compactRepresentationOrthogonalComplement ρ hρ subrepresentation,
    compactRepresentationOrthogonalComplement_isCompl ρ hρ subrepresentation⟩

/-- The associated group-algebra module admits a finite direct-sum decomposition into simple
submodules. This is an algebraic decomposition theorem; packaging each summand in explicit unitary
matrix coordinates is a later bridge. -/
theorem compactRepresentation_exists_finite_simple_groupAlgebra_decomposition
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    {n : ℕ} (ρ : G →* Matrix (Fin n) (Fin n) ℂ) (hρ : Continuous ρ) :
    ∃ (summandCount : ℕ)
      (summands : Fin summandCount →
        Submodule ℂ[G] (matrixRepresentation ρ).asModule)
      (_ : (matrixRepresentation ρ).asModule ≃ₗ[ℂ[G]]
        Π₀ index : Fin summandCount, summands index),
      ∀ index, IsSimpleModule ℂ[G] (summands index) := by
  letI : Representation.IsSemisimpleRepresentation (matrixRepresentation ρ) :=
    compactRepresentation_isSemisimple ρ hρ
  haveI : IsSemisimpleModule ℂ[G] (matrixRepresentation ρ).asModule :=
    (Representation.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule _).mp
      inferInstance
  letI : Module.Finite ℂ[G] (matrixRepresentation ρ).asModule :=
    Module.Finite.of_restrictScalars_finite ℂ ℂ[G] _
  exact IsSemisimpleModule.exists_linearEquiv_fin_dfinsupp ℂ[G]
    (matrixRepresentation ρ).asModule

end

end Mathematics
end YangMills
