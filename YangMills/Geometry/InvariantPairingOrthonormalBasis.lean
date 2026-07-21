/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Geometry.InvariantInnerProduct
import Mathlib.LinearAlgebra.Basis.Basic

/-!
# Finite orthonormal bases for an explicit invariant pairing

The project deliberately keeps `InvariantInnerProductData` out of global typeclass inference so
multiple normalizations can coexist. This module therefore packages a finite basis and its exact
orthonormality relative to one unchanged explicit pairing, rather than installing a competing
`InnerProductSpace` instance.

The basis is supplied acceptance data. No compact-group averaging or Gram--Schmidt construction is
claimed here.
-/

namespace YangMills.Geometry

open scoped Manifold ContDiff

universe uE uG

noncomputable section

variable
    {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {G : Type uG} [Group G] [TopologicalSpace G] [ChartedSpace E G]
    [LieGroup (modelWithCornersSelf ℝ E) ∞ G]

/-- A nonempty finite basis orthonormal for the exact selected invariant pairing. -/
structure InvariantPairingOrthonormalBasisData
    (inner : InvariantInnerProductData
      (I := modelWithCornersSelf ℝ E) (G := G)) where
  /-- Explicit source-indexed basis rank. -/
  rank : ℕ
  /-- Anti-vacuity: the orthonormal family is nonempty. -/
  rank_pos : 0 < rank
  /-- Basis of the exact tangent Lie algebra. -/
  basis : Module.Basis (Fin rank) ℝ
    (GroupLieAlgebra (modelWithCornersSelf ℝ E) G)
  /-- Orthonormality relative to the same explicit invariant pairing. -/
  basis_orthonormal : ∀ a b,
    inner.pairing (basis a) (basis b) = if a = b then 1 else 0

namespace InvariantPairingOrthonormalBasisData

/-- Canonical first index supplied by nonempty rank. -/
def firstIndex
    {inner : InvariantInnerProductData
      (I := modelWithCornersSelf ℝ E) (G := G)}
    (data : InvariantPairingOrthonormalBasisData inner) : Fin data.rank :=
  ⟨0, data.rank_pos⟩

/-- The first selected basis vector has exact squared norm one. -/
theorem firstBasis_pairing_self
    {inner : InvariantInnerProductData
      (I := modelWithCornersSelf ℝ E) (G := G)}
    (data : InvariantPairingOrthonormalBasisData inner) :
    inner.pairing (data.basis data.firstIndex) (data.basis data.firstIndex) = 1 := by
  rw [data.basis_orthonormal]
  simp

/-- The selected basis contains an actual nonzero tangent vector. -/
theorem firstBasis_ne_zero
    {inner : InvariantInnerProductData
      (I := modelWithCornersSelf ℝ E) (G := G)}
    (data : InvariantPairingOrthonormalBasisData inner) :
    data.basis data.firstIndex ≠ 0 := by
  intro zero_vector
  have h := data.firstBasis_pairing_self
  rw [zero_vector] at h
  simp at h

end InvariantPairingOrthonormalBasisData

end

end YangMills.Geometry
