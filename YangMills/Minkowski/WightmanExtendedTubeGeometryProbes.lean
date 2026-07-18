/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Minkowski.WightmanExtendedTubeGeometry

/-!
# Hostile probes for Wightman extended-tube geometry

The probes expose the exact orbit quantifiers, openness, invariance, strict nonzero semantics, and a
four-dimensional point proving that replacing the extended orbit by the original tube is invalid.
-/

namespace YangMills.Minkowski.WightmanExtendedTubeGeometry.Probes

/-- Membership is exactly one proper-complex-Lorentz image of one ordinary-tube point. -/
theorem exact_extended_tube_orbit
    {d : EuclideanDimension} {n : ℕ} (z : Fin n → ComplexifiedSpacetime d) :
    z ∈ wightmanExtendedTube d n ↔
      ∃ (transformation : ProperComplexLorentzTransformation d)
        (w : Fin n → ComplexifiedSpacetime d),
        w ∈ wightmanBackwardTube d n ∧
          z = ProperComplexLorentzTransformation.actConfiguration transformation w :=
  mem_wightmanExtendedTube_iff z

/-- The extended domain is an actual open nonempty set. -/
theorem exact_extended_tube_open_nonempty
    (d : EuclideanDimension) (n : ℕ) :
    IsOpen (wightmanExtendedTube d n) ∧
      (wightmanExtendedTube d n).Nonempty :=
  ⟨isOpen_wightmanExtendedTube d n, wightmanExtendedTube_nonempty d n⟩

/-- The ordinary tube embeds through the exact identity transformation. -/
theorem exact_ordinary_tube_inclusion
    (d : EuclideanDimension) (n : ℕ) :
    wightmanBackwardTube d n ⊆ wightmanExtendedTube d n :=
  wightmanBackwardTube_subset_extendedTube d n

/-- The orbit is closed under the same proper complex Lorentz group action. -/
theorem exact_extended_tube_invariance
    {d : EuclideanDimension} {n : ℕ}
    (transformation : ProperComplexLorentzTransformation d)
    {z : Fin n → ComplexifiedSpacetime d}
    (hz : z ∈ wightmanExtendedTube d n) :
    ProperComplexLorentzTransformation.actConfiguration transformation z ∈
      wightmanExtendedTube d n :=
  wightmanExtendedTube_invariant transformation hz

/-- Positive-arity zero remains excluded after taking all invertible orbit images. -/
theorem strict_extended_tube_rejects_zero
    (d : EuclideanDimension) {n : ℕ} (hn : 0 < n) :
    (0 : Fin n → ComplexifiedSpacetime d) ∉ wightmanExtendedTube d n :=
  zero_not_mem_wightmanExtendedTube d hn

/-- The explicit negated standard point proves strict four-dimensional enlargement. -/
theorem four_dimensional_extended_tube_strict
    {n : ℕ} (hn : 0 < n) :
    fourDimensionalExtendedTubeWitness n ∈
        wightmanExtendedTube EuclideanDimension.four n ∧
      fourDimensionalExtendedTubeWitness n ∉
        wightmanBackwardTube EuclideanDimension.four n :=
  ⟨fourDimensionalExtendedTubeWitness_mem n,
    fourDimensionalExtendedTubeWitness_not_mem_backwardTube hn⟩

/-- Identifying the extended domain with the original tube is directly contradicted at every
positive arity in four dimensions. -/
theorem fixed_tube_replacement_blocked
    {n : ℕ} (hn : 0 < n)
    (wrong : wightmanExtendedTube EuclideanDimension.four n =
      wightmanBackwardTube EuclideanDimension.four n) : False := by
  have extended := fourDimensionalExtendedTubeWitness_mem n
  rw [wrong] at extended
  exact fourDimensionalExtendedTubeWitness_not_mem_backwardTube hn extended

end YangMills.Minkowski.WightmanExtendedTubeGeometry.Probes
