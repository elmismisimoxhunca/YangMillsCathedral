/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.RepresentationTheory.Character
import Mathlib.Topology.Instances.Matrix

/-!
# Matrix representations and Mathlib representation characters

This file supplies the first algebraic bridge for compact nonabelian Fourier analysis. A square
matrix-valued monoid representation acts on coordinate vectors by matrix multiplication and hence
defines Mathlib's `Representation`. Its abstract linear trace character is proved to be literally the
matrix trace of the original representation.

The construction is independent of Yang–Mills, topology, Haar measure, irreducibility, and
Peter–Weyl completeness. Those layers must be added separately rather than assumed here.
-/

namespace YangMills
namespace Mathematics

noncomputable section

universe uG un

/-- Convert a square matrix-valued monoid homomorphism into Mathlib's representation on coordinate
vectors using the standard basis. -/
def matrixRepresentation
    {G : Type uG} [Monoid G] {n : Type un} [Fintype n] [DecidableEq n]
    (ρ : G →* Matrix n n ℂ) : Representation ℂ G (n → ℂ) :=
  (Matrix.toLinAlgEquiv (Pi.basisFun ℂ n)).toMonoidHom.comp ρ

@[simp]
theorem matrixRepresentation_apply
    {G : Type uG} [Monoid G] {n : Type un} [Fintype n] [DecidableEq n]
    (ρ : G →* Matrix n n ℂ) (g : G) :
    matrixRepresentation ρ g = Matrix.toLin' (ρ g) :=
  rfl

/-- The abstract Mathlib character of the induced coordinate representation is exactly the matrix
trace of the original matrix representation. -/
@[simp]
theorem matrixRepresentation_character
    {G : Type uG} [Monoid G] {n : Type un} [Fintype n] [DecidableEq n]
    (ρ : G →* Matrix n n ℂ) (g : G) :
    (matrixRepresentation ρ).character g = Matrix.trace (ρ g) := by
  rw [Representation.character,
    LinearMap.trace_eq_matrix_trace ℂ (Pi.basisFun ℂ n)]
  change (LinearMap.toMatrix' (Matrix.toLin' (ρ g))).trace = _
  rw [LinearMap.toMatrix'_toLin']

/-- A matrix coefficient in the fixed coordinate basis. -/
def matrixRepresentationCoefficient
    {G : Type uG} {n : Type un}
    (ρ : G → Matrix n n ℂ) (row column : n) : G → ℂ :=
  fun g => ρ g row column

/-- Continuity of a matrix-valued representation gives continuity of each exact coordinate matrix
coefficient. -/
theorem continuous_matrixRepresentationCoefficient
    {G : Type uG} [TopologicalSpace G] {n : Type un}
    (ρ : G → Matrix n n ℂ) (hρ : Continuous ρ) (row column : n) :
    Continuous (matrixRepresentationCoefficient ρ row column) := by
  exact (continuous_apply column).comp ((continuous_apply row).comp hρ)

/-- The matrix trace character of a continuous finite matrix family is continuous, derived from its
exact diagonal coefficients. -/
theorem continuous_matrixRepresentation_trace
    {G : Type uG} [TopologicalSpace G] {n : Type un} [Fintype n]
    (ρ : G → Matrix n n ℂ) (hρ : Continuous ρ) :
    Continuous (fun g => Matrix.trace (ρ g)) := by
  unfold Matrix.trace
  fun_prop

/-- Conjugacy invariance of the matrix trace is inherited from Mathlib's abstract representation
character theorem. -/
theorem matrixRepresentation_trace_conj
    {G : Type uG} [Group G] {n : Type un} [Fintype n] [DecidableEq n]
    (ρ : G →* Matrix n n ℂ) (g h : G) :
    Matrix.trace (ρ (h * g * h⁻¹)) = Matrix.trace (ρ g) := by
  simpa only [matrixRepresentation_character] using
    Representation.char_conj (matrixRepresentation ρ) g h

/-- The matrix trace character is the finite sum of exact diagonal matrix coefficients. -/
theorem matrix_trace_eq_sum_coefficients
    {G : Type uG} {n : Type un} [Fintype n]
    (ρ : G → Matrix n n ℂ) (g : G) :
    Matrix.trace (ρ g) = ∑ i, matrixRepresentationCoefficient ρ i i g :=
  rfl

end

end Mathematics
end YangMills
