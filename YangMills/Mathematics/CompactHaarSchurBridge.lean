/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import Mathlib.RepresentationTheory.Irreducible
import YangMills.Mathematics.CompactHaarIntertwinerAverage

/-!
# From Haar averaging to algebraic Schur lemmas

This file converts the coordinatewise compact Haar average into Mathlib's exact
`Representation.IntertwiningMap`. It then applies Mathlib's algebraic irreducibility API: between
irreducible inequivalent representations, every such averaged rectangular matrix is zero.

This is the first analytic Schur consequence in the nonabelian Fourier track. It does not yet derive
the scalar normalization in the equivalent/self case or the full matrix-coefficient orthogonality
formula.
-/

namespace YangMills
namespace Mathematics

open Representation

noncomputable section

universe uG

/-- The Haar-averaged rectangular matrix as Mathlib's exact intertwining map between the coordinate
representations. -/
def compactHaarIntertwiningMap
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    {m n : ℕ}
    (σ : G →* Matrix (Fin m) (Fin m) ℂ)
    (ρ : G →* Matrix (Fin n) (Fin n) ℂ)
    (hσ : Continuous σ) (hρ : Continuous ρ)
    (A : Matrix (Fin m) (Fin n) ℂ) :
    IntertwiningMap (matrixRepresentation ρ) (matrixRepresentation σ) where
  toLinearMap := Matrix.toLin' (compactHaarIntertwinerAverage σ ρ A)
  isIntertwining' := by
    intro h
    rw [matrixRepresentation_apply, matrixRepresentation_apply,
      ← Matrix.toLin'_mul, ← Matrix.toLin'_mul]
    exact congrArg Matrix.toLin'
      (compactHaarIntertwinerAverage_intertwines σ ρ hσ hρ A h).symm

/-- Under irreducibility of both representations, the averaged intertwiner is either bijective or
zero. This is a direct application of Mathlib's algebraic Schur dichotomy. -/
theorem compactHaarIntertwiningMap_bijective_or_eq_zero
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    {m n : ℕ}
    (σ : G →* Matrix (Fin m) (Fin m) ℂ)
    (ρ : G →* Matrix (Fin n) (Fin n) ℂ)
    (hσ : Continuous σ) (hρ : Continuous ρ)
    (A : Matrix (Fin m) (Fin n) ℂ)
    [Representation.IsIrreducible (matrixRepresentation ρ)]
    [Representation.IsIrreducible (matrixRepresentation σ)] :
    Function.Bijective (compactHaarIntertwiningMap σ ρ hσ hρ A) ∨
      compactHaarIntertwiningMap σ ρ hσ hρ A = 0 :=
  Representation.IsIrreducible.bijective_or_eq_zero _

/-- If the two irreducible coordinate representations are inequivalent, every rectangular Haar
average `∫σ(g⁻¹)Aρ(g)` vanishes exactly. -/
theorem compactHaarIntertwinerAverage_eq_zero_of_irreducible_inequivalent
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    {m n : ℕ}
    (σ : G →* Matrix (Fin m) (Fin m) ℂ)
    (ρ : G →* Matrix (Fin n) (Fin n) ℂ)
    (hσ : Continuous σ) (hρ : Continuous ρ)
    (A : Matrix (Fin m) (Fin n) ℂ)
    [Representation.IsIrreducible (matrixRepresentation ρ)]
    [Representation.IsIrreducible (matrixRepresentation σ)]
    [IsEmpty (Representation.Equiv
      (matrixRepresentation ρ) (matrixRepresentation σ))] :
    compactHaarIntertwinerAverage σ ρ A = 0 := by
  have mapZero : compactHaarIntertwiningMap σ ρ hσ hρ A = 0 :=
    Subsingleton.elim _ _
  have linearZero := congrArg
    (fun value : IntertwiningMap
      (matrixRepresentation ρ) (matrixRepresentation σ) => value.toLinearMap)
    mapZero
  change Matrix.toLin' (compactHaarIntertwinerAverage σ ρ A) = 0 at linearZero
  apply Matrix.toLin'.injective
  simpa using linearZero

end

end Mathematics
end YangMills
