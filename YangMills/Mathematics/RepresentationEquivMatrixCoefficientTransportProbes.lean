/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Mathematics.RepresentationEquivMatrixCoefficientTransport

/-!
# Hostile probes for basis-aware matrix-coefficient transport
-/

namespace YangMills
namespace Mathematics
namespace RepresentationEquivMatrixCoefficientTransport
namespace Probes

noncomputable section

universe uG

/-- Both explicitly constructed rectangular coordinate matrices retain the exact left inverse law. -/
theorem exact_coordinate_left_inverse
    {G : Type uG} [Monoid G] {m n : ℕ}
    {ρ : G →* Matrix (Fin m) (Fin m) ℂ}
    {σ : G →* Matrix (Fin n) (Fin n) ℂ}
    (equivalence : Representation.Equiv (matrixRepresentation ρ)
      (matrixRepresentation σ)) :
    representationEquivInverseMatrix equivalence *
      representationEquivMatrix equivalence = 1 :=
  representationEquivInverseMatrix_mul equivalence

/-- Both explicitly constructed rectangular coordinate matrices retain the exact right inverse law. -/
theorem exact_coordinate_right_inverse
    {G : Type uG} [Monoid G] {m n : ℕ}
    {ρ : G →* Matrix (Fin m) (Fin m) ℂ}
    {σ : G →* Matrix (Fin n) (Fin n) ℂ}
    (equivalence : Representation.Equiv (matrixRepresentation ρ)
      (matrixRepresentation σ)) :
    representationEquivMatrix equivalence *
      representationEquivInverseMatrix equivalence = 1 :=
  representationEquivMatrix_mul_inverse equivalence

/-- Exact conjugation probe: representation transport uses the same supplied equivalence and its
actual inverse coordinate matrix. -/
theorem exact_basis_aware_conjugation
    {G : Type uG} [Monoid G] {m n : ℕ}
    (ρ : G →* Matrix (Fin m) (Fin m) ℂ)
    (σ : G →* Matrix (Fin n) (Fin n) ℂ)
    (equivalence : Representation.Equiv (matrixRepresentation ρ)
      (matrixRepresentation σ)) (g : G) :
    representationEquivMatrix equivalence * ρ g *
      representationEquivInverseMatrix equivalence = σ g :=
  representationEquivMatrix_conjugates ρ σ equivalence g

/-- Hostile conjugation probe: replacing the exact transported representation matrix is
contradictory. -/
theorem changed_conjugation_blocked
    {G : Type uG} [Monoid G] {m n : ℕ}
    (ρ : G →* Matrix (Fin m) (Fin m) ℂ)
    (σ : G →* Matrix (Fin n) (Fin n) ℂ)
    (equivalence : Representation.Equiv (matrixRepresentation ρ)
      (matrixRepresentation σ)) (g : G)
    (changed : representationEquivMatrix equivalence * ρ g *
      representationEquivInverseMatrix equivalence ≠ σ g) : False :=
  changed (representationEquivMatrix_conjugates ρ σ equivalence g)

/-- Exact coefficient probe: raw target coefficients retain both change-of-basis factors and both
finite source-coordinate sums. -/
theorem exact_basis_aware_coefficient
    {G : Type uG} [Monoid G] {m n : ℕ}
    (ρ : G →* Matrix (Fin m) (Fin m) ℂ)
    (σ : G →* Matrix (Fin n) (Fin n) ℂ)
    (equivalence : Representation.Equiv (matrixRepresentation ρ)
      (matrixRepresentation σ))
    (g : G) (row column : Fin n) :
    σ g row column = ∑ sourceRow, ∑ sourceColumn,
      representationEquivMatrix equivalence row sourceRow *
        ρ g sourceRow sourceColumn *
          representationEquivInverseMatrix equivalence sourceColumn column :=
  representationEquiv_matrixCoefficient ρ σ equivalence g row column

/-- Hostile coefficient probe: a changed basis-aware coefficient formula is impossible. This does
not falsely assert equality of raw coefficients from two different presentations. -/
theorem changed_basis_aware_coefficient_blocked
    {G : Type uG} [Monoid G] {m n : ℕ}
    (ρ : G →* Matrix (Fin m) (Fin m) ℂ)
    (σ : G →* Matrix (Fin n) (Fin n) ℂ)
    (equivalence : Representation.Equiv (matrixRepresentation ρ)
      (matrixRepresentation σ))
    (g : G) (row column : Fin n)
    (changed : σ g row column ≠ ∑ sourceRow, ∑ sourceColumn,
      representationEquivMatrix equivalence row sourceRow *
        ρ g sourceRow sourceColumn *
          representationEquivInverseMatrix equivalence sourceColumn column) : False :=
  changed (representationEquiv_matrixCoefficient ρ σ equivalence g row column)

/-- Anti-collapse probe: in positive source dimension the forward change-of-basis matrix cannot be
zero, because its exact left inverse would make the identity matrix zero. -/
theorem positive_dimension_change_matrix_ne_zero
    {G : Type uG} [Monoid G] {m n : ℕ}
    {ρ : G →* Matrix (Fin m) (Fin m) ℂ}
    {σ : G →* Matrix (Fin n) (Fin n) ℂ}
    (equivalence : Representation.Equiv (matrixRepresentation ρ)
      (matrixRepresentation σ)) (dimension_pos : 0 < m) :
    representationEquivMatrix equivalence ≠ 0 := by
  intro collapsed
  have inverseLaw := representationEquivInverseMatrix_mul equivalence
  rw [collapsed] at inverseLaw
  let coordinate : Fin m := ⟨0, dimension_pos⟩
  have diagonal := congrFun (congrFun inverseLaw coordinate) coordinate
  simp [Matrix.mul_apply] at diagonal

end

end Probes
end RepresentationEquivMatrixCoefficientTransport
end Mathematics
end YangMills
