/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import Mathlib.Analysis.Complex.Polynomial.Basic
import YangMills.Mathematics.CompactHaarSchurBridge

/-!
# The irreducible self-case of compact Haar–Schur averaging

For an irreducible continuous complex matrix representation, this file combines the constructed
Haar intertwiner average with Mathlib's algebraically-closed Schur theorem. It proves that every
self-average `∫ρ(g⁻¹)Aρ(g)dμ_H` is a complex scalar multiple of the identity matrix and names that
scalar by choice.

The scalar's exact trace/dimension formula and matrix-coefficient orthogonality are deliberately left
to the next layer; no normalization is guessed here.
-/

namespace YangMills
namespace Mathematics

open Representation

noncomputable section

universe uG

/-- Every Haar-conjugation average for an irreducible complex matrix representation is a scalar
matrix. -/
theorem exists_compactHaarIntertwinerAverage_eq_smul_one
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    {n : ℕ} (ρ : G →* Matrix (Fin n) (Fin n) ℂ)
    (hρ : Continuous ρ) (A : Matrix (Fin n) (Fin n) ℂ)
    [Representation.IsIrreducible (matrixRepresentation ρ)] :
    ∃ scalar : ℂ,
      compactHaarIntertwinerAverage ρ ρ A =
        scalar • (1 : Matrix (Fin n) (Fin n) ℂ) := by
  let averagedMap := compactHaarIntertwiningMap ρ ρ hρ hρ A
  obtain ⟨scalar, scalarMap⟩ :=
    (Representation.IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed
      (ρ := matrixRepresentation ρ)).2 averagedMap
  refine ⟨scalar, ?_⟩
  have linearEquality := congrArg
    (fun value : IntertwiningMap
      (matrixRepresentation ρ) (matrixRepresentation ρ) => value.toLinearMap)
    scalarMap
  apply Matrix.toLin'.injective
  change Matrix.toLin' (compactHaarIntertwinerAverage ρ ρ A) =
    Matrix.toLin' (scalar • (1 : Matrix (Fin n) (Fin n) ℂ))
  rw [← show (compactHaarIntertwiningMap ρ ρ hρ hρ A).toLinearMap =
    Matrix.toLin' (compactHaarIntertwinerAverage ρ ρ A) from rfl]
  have oneLinear :
      (1 : IntertwiningMap
        (matrixRepresentation ρ) (matrixRepresentation ρ)).toLinearMap =
        LinearMap.id := rfl
  simpa [averagedMap, oneLinear] using linearEquality.symm

/-- The selected scalar multiplying the identity in the irreducible self-average. -/
def compactHaarSchurScalar
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    {n : ℕ} (ρ : G →* Matrix (Fin n) (Fin n) ℂ)
    (hρ : Continuous ρ) (A : Matrix (Fin n) (Fin n) ℂ)
    [Representation.IsIrreducible (matrixRepresentation ρ)] : ℂ :=
  Classical.choose (exists_compactHaarIntertwinerAverage_eq_smul_one ρ hρ A)

/-- The exact self-average equals the selected scalar times the identity matrix. -/
theorem compactHaarIntertwinerAverage_eq_schurScalar_smul_one
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    {n : ℕ} (ρ : G →* Matrix (Fin n) (Fin n) ℂ)
    (hρ : Continuous ρ) (A : Matrix (Fin n) (Fin n) ℂ)
    [Representation.IsIrreducible (matrixRepresentation ρ)] :
    compactHaarIntertwinerAverage ρ ρ A =
      compactHaarSchurScalar ρ hρ A •
        (1 : Matrix (Fin n) (Fin n) ℂ) :=
  Classical.choose_spec
    (exists_compactHaarIntertwinerAverage_eq_smul_one ρ hρ A)

end

end Mathematics
end YangMills
