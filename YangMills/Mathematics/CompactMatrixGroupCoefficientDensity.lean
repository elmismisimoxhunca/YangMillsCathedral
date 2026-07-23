/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Mathematics.CompactUnitaryCoefficientStarSubalgebra

/-!
# Coefficient density for compact groups with a faithful finite matrix representation

Hall's compact matrix-group Stone–Weierstrass argument uses a faithful finite-dimensional
representation to separate points. The preceding finite complete-reducibility results place every
coefficient of that representation in the irreducible-unitary coefficient star subalgebra. Thus the
faithful representation supplies point separation, and Mathlib's complex Stone–Weierstrass theorem
supplies uniform density.

The faithful finite matrix representation is an explicit hypothesis here. This file does not prove
that an arbitrary compact Hausdorff group has such a representation, nor the more general
Peter–Weyl point-separation theorem by a family of finite representations.
-/

namespace YangMills
namespace Mathematics

noncomputable section

universe uG

/-- A continuous faithful finite complex matrix representation. This is the exact finite-coordinate
hypothesis used in the compact matrix-group Stone–Weierstrass argument. -/
structure ContinuousFaithfulFiniteMatrixRepresentation
    (G : Type uG) [Group G] [TopologicalSpace G] where
  dimension : ℕ
  representation : G →* Matrix (Fin dimension) (Fin dimension) ℂ
  continuous_representation : Continuous representation
  faithful_representation : Function.Injective representation

/-- Distinct group elements are distinguished by at least one entry of a faithful finite matrix
representation. -/
theorem ContinuousFaithfulFiniteMatrixRepresentation.exists_entry_ne
    {G : Type uG} [Group G] [TopologicalSpace G]
    (faithful : ContinuousFaithfulFiniteMatrixRepresentation G)
    {x y : G} (hxy : x ≠ y) :
    ∃ i j, faithful.representation x i j ≠ faithful.representation y i j := by
  have matrix_ne : faithful.representation x ≠ faithful.representation y :=
    faithful.faithful_representation.ne hxy
  by_contra no_entry
  push Not at no_entry
  exact matrix_ne (Matrix.ext no_entry)

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]

/-- A faithful finite matrix representation makes the irreducible-unitary coefficient star
subalgebra separate points. -/
theorem compactUnitaryCoefficientStarSubalgebra_separatesPoints_of_faithful
    (faithful : ContinuousFaithfulFiniteMatrixRepresentation G) :
    (compactUnitaryCoefficientStarSubalgebra (G := G)).SeparatesPoints := by
  intro x y hxy
  rcases faithful.exists_entry_ne hxy with ⟨i, j, hij⟩
  let f := continuousMatrixRepresentationCoefficient faithful.representation
    faithful.continuous_representation i j
  refine ⟨f, ⟨f, ?_, rfl⟩, hij⟩
  exact continuousMatrixRepresentationCoefficient_mem_span
    faithful.representation faithful.continuous_representation i j

/-- Conditional compact matrix-group Stone–Weierstrass theorem: under an explicit continuous
faithful finite matrix representation, the topological closure of the finite irreducible-unitary
coefficient star subalgebra is all of `C(G, ℂ)`. -/
theorem compactUnitaryCoefficientStarSubalgebra_topologicalClosure_eq_top_of_faithful
    (faithful : ContinuousFaithfulFiniteMatrixRepresentation G) :
    (compactUnitaryCoefficientStarSubalgebra (G := G)).topologicalClosure = ⊤ :=
  ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints _
    (compactUnitaryCoefficientStarSubalgebra_separatesPoints_of_faithful faithful)

end

end Mathematics
end YangMills
