/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Mathematics.UnitaryMatrixDualCharacters

/-!
# Character transport across representation equivalence

Trace characters do not depend on the chosen coordinate presentation of a finite-dimensional
representation. This file proves that statement directly from Mathlib's representation equivalence
and linear-trace conjugation theorem, then applies it to the selected representative of each
`UnitaryMatrixDual` quotient class.

Raw matrix coefficients are basis-dependent and are deliberately not identified here. No Haar
orthogonality, density, Peter–Weyl completeness, or infinite character expansion is asserted.
-/

namespace YangMills
namespace Mathematics

noncomputable section

universe uG

/-- Equivalent finite coordinate representations have pointwise equal matrix-trace characters,
even when their coordinate dimensions are presented differently. -/
theorem matrixRepresentation_trace_eq_of_equiv
    {G : Type uG} [Monoid G] {m n : ℕ}
    (ρ : G →* Matrix (Fin m) (Fin m) ℂ)
    (σ : G →* Matrix (Fin n) (Fin n) ℂ)
    (equivalence : Representation.Equiv (matrixRepresentation ρ)
      (matrixRepresentation σ)) (g : G) :
    Matrix.trace (ρ g) = Matrix.trace (σ g) := by
  rw [← matrixRepresentation_character, ← matrixRepresentation_character]
  unfold Representation.character
  have traceConjugation := LinearMap.trace_conj'
    (matrixRepresentation ρ g) equivalence.toLinearEquiv
  rw [equivalence.conj_apply_self g] at traceConjugation
  exact traceConjugation.symm

/-- A supplied equivalence between bundled continuous irreducible unitary matrix representations
forces their trace characters to agree pointwise. -/
theorem ContinuousUnitaryIrreducibleMatrixRepresentation.trace_eq_of_isEquivalent
    {G : Type uG} [Group G] [TopologicalSpace G]
    {ρ σ : ContinuousUnitaryIrreducibleMatrixRepresentation G}
    (equivalent : ρ.IsEquivalent σ) (g : G) :
    Matrix.trace (ρ.representation g) = Matrix.trace (σ.representation g) := by
  rcases equivalent with ⟨equivalence⟩
  exact matrixRepresentation_trace_eq_of_equiv
    ρ.representation σ.representation equivalence g

/-- The character selected by a coordinate-unitary-dual class agrees pointwise with the character
of every bundled presentation defining that class. -/
theorem unitaryMatrixDualCharacter_class_eq
    {G : Type uG} [Group G] [TopologicalSpace G]
    (ρ : ContinuousUnitaryIrreducibleMatrixRepresentation G) (g : G) :
    unitaryMatrixDualCharacter (unitaryMatrixDualClass ρ) g =
      Matrix.trace (ρ.representation g) := by
  exact (ContinuousUnitaryIrreducibleMatrixRepresentation.trace_eq_of_isEquivalent
    (unitaryMatrixDual_equivalent_representative ρ) g).symm

/-- Function-level form of quotient representative independence for trace characters. -/
theorem unitaryMatrixDualCharacter_class_eq_fun
    {G : Type uG} [Group G] [TopologicalSpace G]
    (ρ : ContinuousUnitaryIrreducibleMatrixRepresentation G) :
    unitaryMatrixDualCharacter (unitaryMatrixDualClass ρ) =
      fun g => Matrix.trace (ρ.representation g) := by
  funext g
  exact unitaryMatrixDualCharacter_class_eq ρ g

end

end Mathematics
end YangMills
