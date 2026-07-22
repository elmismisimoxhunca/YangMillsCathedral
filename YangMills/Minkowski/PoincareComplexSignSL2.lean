/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import YangMills.Minkowski.PoincareComplexSignKernel

/-!
# Concrete complex signs inside `SL(2, ℂ)`

Streater–Wightman printed p. 12, equations (1-14)–(1-15), identifies the homogeneous covering
kernel with the two scalar matrices `±I`. This module constructs the exact injective homomorphism
from the project's literal complex-sign group into Mathlib's matrix special linear group.

This closes only the scalar-kernel carrier step. It does not construct the homogeneous Lorentz map,
the inhomogeneous Poincare cover, a topology or Lie structure on `SL(2, ℂ)`, or any representation.
-/

namespace YangMills.Minkowski

noncomputable section

/-- Mathlib's concrete two-by-two complex special linear group. -/
abbrev ComplexSpecialLinearTwo := Matrix.SpecialLinearGroup (Fin 2) ℂ

/-- A literal complex sign as the scalar matrix `±I`, whose determinant is one in dimension two. -/
def complexSignScalarMatrix (sign : ComplexSign) : ComplexSpecialLinearTwo := by
  refine ⟨Matrix.scalar (Fin 2) (((sign : ℂˣ) : ℂ)), ?_⟩
  rw [Matrix.scalar_apply, Matrix.det_diagonal]
  rcases sign.property with positive | negative
  · rw [positive]
    norm_num
  · rw [negative]
    norm_num

@[simp]
theorem complexSignScalarMatrix_coe (sign : ComplexSign) :
    (complexSignScalarMatrix sign : Matrix (Fin 2) (Fin 2) ℂ) =
      Matrix.scalar (Fin 2) (((sign : ℂˣ) : ℂ)) :=
  rfl

/-- Scalar-sign matrices preserve multiplication exactly. -/
theorem complexSignScalarMatrix_mul (first second : ComplexSign) :
    complexSignScalarMatrix (first * second) =
      complexSignScalarMatrix first * complexSignScalarMatrix second := by
  apply Subtype.ext
  change Matrix.scalar (Fin 2) (((first * second : ComplexSign) : ℂˣ) : ℂ) =
    Matrix.scalar (Fin 2) (((first : ℂˣ) : ℂ)) *
      Matrix.scalar (Fin 2) (((second : ℂˣ) : ℂ))
  exact map_mul (Matrix.scalar (Fin 2))
    (((first : ℂˣ) : ℂ)) (((second : ℂˣ) : ℂ))

/-- Exact scalar-matrix homomorphism from literal complex signs into concrete `SL(2, ℂ)`. -/
def complexSignToSL2 : ComplexSign →* ComplexSpecialLinearTwo where
  toFun := complexSignScalarMatrix
  map_one' := by
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    simp [complexSignScalarMatrix_coe]
  map_mul' := complexSignScalarMatrix_mul

/-- The two literal signs remain distinct as scalar matrices. -/
theorem complexSignToSL2_injective : Function.Injective complexSignToSL2 := by
  intro first second equality
  have diagonalEquality := congrArg
    (fun matrix : ComplexSpecialLinearTwo =>
      (matrix : Matrix (Fin 2) (Fin 2) ℂ) 0 0) equality
  simp [complexSignToSL2, complexSignScalarMatrix_coe, Matrix.scalar_apply]
    at diagonalEquality
  apply Subtype.ext
  apply Units.ext
  exact diagonalEquality

/-- The negative literal sign is exactly the scalar matrix `-I`. -/
@[simp]
theorem complexSignToSL2_negative_coe :
    (complexSignToSL2 negativeComplexSign : Matrix (Fin 2) (Fin 2) ℂ) =
      Matrix.scalar (Fin 2) (-1 : ℂ) := by
  rfl

/-- The negative scalar matrix is not the identity in concrete `SL(2, ℂ)`. -/
theorem complexSignToSL2_negative_ne_one :
    complexSignToSL2 negativeComplexSign ≠ 1 := by
  intro equality
  apply negativeComplexSign_ne_one
  apply complexSignToSL2_injective
  simpa using equality

/-- Scalar-sign matrices are central in concrete `SL(2, ℂ)`. -/
theorem complexSignToSL2_central
    (sign : ComplexSign) (matrix : ComplexSpecialLinearTwo) :
    complexSignToSL2 sign * matrix = matrix * complexSignToSL2 sign := by
  apply Subtype.ext
  change Matrix.scalar (Fin 2) (((sign : ℂˣ) : ℂ)) *
      (matrix : Matrix (Fin 2) (Fin 2) ℂ) =
    (matrix : Matrix (Fin 2) (Fin 2) ℂ) *
      Matrix.scalar (Fin 2) (((sign : ℂˣ) : ℂ))
  exact (Matrix.scalar_commute (((sign : ℂˣ) : ℂ))
    (fun scalar => mul_comm _ scalar) (matrix : Matrix (Fin 2) (Fin 2) ℂ)).eq

end

end YangMills.Minkowski
