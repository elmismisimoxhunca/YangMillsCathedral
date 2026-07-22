/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Mathematics.MatrixRepresentationCharacter

/-!
# Hostile probes for matrix representation characters
-/

namespace YangMills
namespace Mathematics
namespace MatrixRepresentationCharacter
namespace Probes

noncomputable section

universe uG un

/-- The induced action is the exact original matrix action, not an unrelated representation. -/
theorem exact_matrix_action
    {G : Type uG} [Monoid G] {n : Type un} [Fintype n] [DecidableEq n]
    (ρ : G →* Matrix n n ℂ) (g : G) :
    matrixRepresentation ρ g = Matrix.toLin' (ρ g) :=
  rfl

/-- The abstract representation-theoretic character cannot diverge from the original matrix trace. -/
theorem exact_character_bridge
    {G : Type uG} [Monoid G] {n : Type un} [Fintype n] [DecidableEq n]
    (ρ : G →* Matrix n n ℂ) (g : G) :
    (matrixRepresentation ρ).character g = Matrix.trace (ρ g) :=
  matrixRepresentation_character ρ g

/-- Every exact coefficient remains tied to its designated row and column. -/
theorem exact_coefficient
    {G : Type uG} {n : Type un}
    (ρ : G → Matrix n n ℂ) (row column : n) (g : G) :
    matrixRepresentationCoefficient ρ row column g = ρ g row column :=
  rfl

/-- Continuity of the representation matrix forces continuity of its actual trace character. -/
theorem exact_continuous_trace
    {G : Type uG} [TopologicalSpace G] {n : Type un} [Fintype n]
    (ρ : G → Matrix n n ℂ) (hρ : Continuous ρ) :
    Continuous (fun g => Matrix.trace (ρ g)) :=
  continuous_matrixRepresentation_trace ρ hρ

/-- Cyclic trace invariance is derived from the same matrix representation. -/
theorem exact_conjugacy_invariance
    {G : Type uG} [Group G] {n : Type un} [Fintype n] [DecidableEq n]
    (ρ : G →* Matrix n n ℂ) (g h : G) :
    Matrix.trace (ρ (h * g * h⁻¹)) = Matrix.trace (ρ g) :=
  matrixRepresentation_trace_conj ρ g h

/-- The trace is the sum of the diagonal coefficients, not all matrix entries. -/
theorem exact_diagonal_trace
    {G : Type uG} {n : Type un} [Fintype n]
    (ρ : G → Matrix n n ℂ) (g : G) :
    Matrix.trace (ρ g) = ∑ i, matrixRepresentationCoefficient ρ i i g :=
  matrix_trace_eq_sum_coefficients ρ g

end

end Probes
end MatrixRepresentationCharacter
end Mathematics
end YangMills
