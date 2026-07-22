/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.Trace
import YangMills.Mathematics.MatrixRepresentationCharacter

/-!
# Inverse matrices in unitary representations

For a square matrix representation satisfying `star(ρ(g))ρ(g)=1`, this file derives that the exact
group inverse matrix is the conjugate transpose. The proof does not assume uniqueness of arbitrary
left inverses: it also uses the representation matrix at `g⁻¹` as the exact right inverse.

Entrywise conjugation and inverse-character conjugation follow. These are the missing coordinate
bridges needed to turn Haar–Schur averaging formulas into conventional matrix-coefficient
orthogonality statements.
-/

namespace YangMills
namespace Mathematics

noncomputable section

universe uG

/-- The exact inverse representation matrix is its conjugate transpose. -/
theorem unitaryMatrixRepresentation_inv_eq_conjTranspose
    {G : Type uG} [Group G] {n : ℕ}
    (ρ : G →* Matrix (Fin n) (Fin n) ℂ)
    (unitary : ∀ g, star (ρ g) * ρ g = 1) (g : G) :
    ρ (g⁻¹) = Matrix.conjTranspose (ρ g) := by
  rw [← Matrix.star_eq_conjTranspose]
  calc
    ρ (g⁻¹) = 1 * ρ (g⁻¹) := (Matrix.one_mul _).symm
    _ = (star (ρ g) * ρ g) * ρ (g⁻¹) := by rw [unitary]
    _ = star (ρ g) * (ρ g * ρ (g⁻¹)) := Matrix.mul_assoc _ _ _
    _ = star (ρ g) * ρ (g * g⁻¹) := by rw [map_mul]
    _ = star (ρ g) := by simp

/-- Entrywise inverse matrices are transposed complex conjugates. -/
theorem unitaryMatrixRepresentation_inv_apply
    {G : Type uG} [Group G] {n : ℕ}
    (ρ : G →* Matrix (Fin n) (Fin n) ℂ)
    (unitary : ∀ g, star (ρ g) * ρ g = 1)
    (g : G) (row column : Fin n) :
    ρ (g⁻¹) row column = star (ρ g column row) := by
  rw [unitaryMatrixRepresentation_inv_eq_conjTranspose ρ unitary g]
  rfl

/-- The trace character at the inverse is the complex conjugate of the original trace character. -/
theorem unitaryMatrixRepresentation_trace_inv
    {G : Type uG} [Group G] {n : ℕ}
    (ρ : G →* Matrix (Fin n) (Fin n) ℂ)
    (unitary : ∀ g, star (ρ g) * ρ g = 1) (g : G) :
    Matrix.trace (ρ (g⁻¹)) = star (Matrix.trace (ρ g)) := by
  rw [unitaryMatrixRepresentation_inv_eq_conjTranspose ρ unitary g]
  exact Matrix.trace_conjTranspose (ρ g)

/-- In particular, the real part of the trace character is inversion invariant. -/
theorem unitaryMatrixRepresentation_trace_inv_re
    {G : Type uG} [Group G] {n : ℕ}
    (ρ : G →* Matrix (Fin n) (Fin n) ℂ)
    (unitary : ∀ g, star (ρ g) * ρ g = 1) (g : G) :
    (Matrix.trace (ρ (g⁻¹))).re = (Matrix.trace (ρ g)).re := by
  rw [unitaryMatrixRepresentation_trace_inv ρ unitary g]
  rfl

end

end Mathematics
end YangMills
