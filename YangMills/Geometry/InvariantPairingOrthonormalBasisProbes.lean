/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Geometry.InvariantPairingOrthonormalBasis

/-!
# Hostile probes for explicit invariant-pairing orthonormal bases

The probes expose nonempty rank, exact diagonal normalization, and a genuinely nonzero basis vector.
No basis or invariant pairing is constructed.
-/

namespace YangMills.Geometry.InvariantPairingOrthonormalBasis.Probes

open scoped Manifold ContDiff

noncomputable section

variable
    {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [Group G] [TopologicalSpace G] [ChartedSpace E G]
    [LieGroup (modelWithCornersSelf ℝ E) ∞ G]
    {inner : InvariantInnerProductData
      (I := modelWithCornersSelf ℝ E) (G := G)}

/-- Positive rank gives an actual source index. -/
theorem exact_nonempty_basis_index
    (data : InvariantPairingOrthonormalBasisData inner) : Nonempty (Fin data.rank) :=
  ⟨data.firstIndex⟩

/-- The first basis vector has exact pairing norm one. -/
theorem exact_first_basis_normalization
    (data : InvariantPairingOrthonormalBasisData inner) :
    inner.pairing (data.basis data.firstIndex) (data.basis data.firstIndex) = 1 :=
  data.firstBasis_pairing_self

/-- Replacing the selected first basis vector by zero is contradictory. -/
theorem zero_first_basis_vector_blocked
    (data : InvariantPairingOrthonormalBasisData inner)
    (claimed : data.basis data.firstIndex = 0) : False :=
  data.firstBasis_ne_zero claimed

/-- A changed diagonal pairing value cannot replace exact orthonormality. -/
theorem wrong_diagonal_pairing_blocked
    (data : InvariantPairingOrthonormalBasisData inner)
    (wrong : ℝ) (different : wrong ≠ 1)
    (claimed : inner.pairing (data.basis data.firstIndex)
      (data.basis data.firstIndex) = wrong) : False := by
  apply different
  rw [← claimed]
  exact data.firstBasis_pairing_self

end

end YangMills.Geometry.InvariantPairingOrthonormalBasis.Probes
