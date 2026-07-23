/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Mathematics.UnitaryMatrixDualCharacterTransport

/-!
# Matrix-coefficient transport across representation equivalence

A representation equivalence between two finite coordinate presentations determines an exact
rectangular change-of-basis matrix and an exact rectangular inverse matrix. This file proves their
two inverse laws, the matrix conjugation formula

`σ(g) = E ρ(g) E⁻¹`,

and the resulting double-sum formula for every coordinate coefficient of `σ`.

Unlike trace characters, raw matrix coefficients are basis-dependent. They are therefore transported
through the explicit change-of-basis matrices rather than identified. No Haar orthogonality,
Peter–Weyl density, or infinite expansion is asserted here.
-/

namespace YangMills
namespace Mathematics

noncomputable section

universe uG

/-- The rectangular coordinate matrix of an equivalence from an `m`-dimensional presentation to an
`n`-dimensional presentation. -/
def representationEquivMatrix
    {G : Type uG} [Monoid G] {m n : ℕ}
    {ρ : G →* Matrix (Fin m) (Fin m) ℂ}
    {σ : G →* Matrix (Fin n) (Fin n) ℂ}
    (equivalence : Representation.Equiv (matrixRepresentation ρ)
      (matrixRepresentation σ)) :
    Matrix (Fin n) (Fin m) ℂ :=
  LinearMap.toMatrix' equivalence.toLinearMap

/-- The rectangular coordinate matrix of the inverse representation equivalence. -/
def representationEquivInverseMatrix
    {G : Type uG} [Monoid G] {m n : ℕ}
    {ρ : G →* Matrix (Fin m) (Fin m) ℂ}
    {σ : G →* Matrix (Fin n) (Fin n) ℂ}
    (equivalence : Representation.Equiv (matrixRepresentation ρ)
      (matrixRepresentation σ)) :
    Matrix (Fin m) (Fin n) ℂ :=
  LinearMap.toMatrix' equivalence.toLinearEquiv.symm.toLinearMap

/-- The inverse coordinate matrix is a left inverse of the forward coordinate matrix. -/
theorem representationEquivInverseMatrix_mul
    {G : Type uG} [Monoid G] {m n : ℕ}
    {ρ : G →* Matrix (Fin m) (Fin m) ℂ}
    {σ : G →* Matrix (Fin n) (Fin n) ℂ}
    (equivalence : Representation.Equiv (matrixRepresentation ρ)
      (matrixRepresentation σ)) :
    representationEquivInverseMatrix equivalence *
      representationEquivMatrix equivalence = 1 := by
  apply Matrix.toLin'.injective
  simp [representationEquivMatrix, representationEquivInverseMatrix,
    Matrix.toLin'_mul]
  ext basisIndex coordinate
  exact congrFun
    (equivalence.left_inv (Pi.single basisIndex 1)) coordinate

/-- The forward coordinate matrix is a right inverse of the inverse coordinate matrix. -/
theorem representationEquivMatrix_mul_inverse
    {G : Type uG} [Monoid G] {m n : ℕ}
    {ρ : G →* Matrix (Fin m) (Fin m) ℂ}
    {σ : G →* Matrix (Fin n) (Fin n) ℂ}
    (equivalence : Representation.Equiv (matrixRepresentation ρ)
      (matrixRepresentation σ)) :
    representationEquivMatrix equivalence *
      representationEquivInverseMatrix equivalence = 1 := by
  apply Matrix.toLin'.injective
  simp [representationEquivMatrix, representationEquivInverseMatrix,
    Matrix.toLin'_mul]
  ext basisIndex coordinate
  exact congrFun
    (equivalence.right_inv (Pi.single basisIndex 1)) coordinate

/-- The exact matrix form of representation intertwining is conjugation by the supplied coordinate
change and its actual inverse. -/
theorem representationEquivMatrix_conjugates
    {G : Type uG} [Monoid G] {m n : ℕ}
    (ρ : G →* Matrix (Fin m) (Fin m) ℂ)
    (σ : G →* Matrix (Fin n) (Fin n) ℂ)
    (equivalence : Representation.Equiv (matrixRepresentation ρ)
      (matrixRepresentation σ)) (g : G) :
    representationEquivMatrix equivalence * ρ g *
      representationEquivInverseMatrix equivalence = σ g := by
  have intertwining := equivalence.conj_apply_self g
  rw [LinearEquiv.conj_apply] at intertwining
  have coordinateIntertwining := congrArg LinearMap.toMatrix' intertwining
  simpa [representationEquivMatrix, representationEquivInverseMatrix,
    LinearMap.toMatrix'_comp] using coordinateIntertwining

/-- Every coefficient in the target presentation is the exact basis-aware double sum of source
coefficients. The two rectangular coordinate matrices cannot be omitted in general. -/
theorem representationEquiv_matrixCoefficient
    {G : Type uG} [Monoid G] {m n : ℕ}
    (ρ : G →* Matrix (Fin m) (Fin m) ℂ)
    (σ : G →* Matrix (Fin n) (Fin n) ℂ)
    (equivalence : Representation.Equiv (matrixRepresentation ρ)
      (matrixRepresentation σ))
    (g : G) (row column : Fin n) :
    σ g row column = ∑ sourceRow, ∑ sourceColumn,
      representationEquivMatrix equivalence row sourceRow *
        ρ g sourceRow sourceColumn *
          representationEquivInverseMatrix equivalence sourceColumn column := by
  rw [← representationEquivMatrix_conjugates ρ σ equivalence g]
  simp only [Matrix.mul_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

end

end Mathematics
end YangMills
