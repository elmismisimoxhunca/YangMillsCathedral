/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Minkowski.ComplexLorentzKinematics

/-!
# Wightman extended-tube geometry

Streater–Wightman printed p. 63 defines the extended tube as the union of all images of the ordinary
tube under proper complex Lorentz transformations. This module constructs that orbit exactly and
proves it open, nonempty, invariant, and strictly larger than the ordinary four-dimensional tube at
positive arity.

Only domain geometry is constructed. No group analytic structure, holomorphic continuation,
single-valuedness theorem, correlator transformation law, or quantum theory is supplied.
-/

namespace YangMills.Minkowski

open Set

noncomputable section

/-- Orbit union of the ordinary backward tube under simultaneous proper complex Lorentz action. -/
def wightmanExtendedTube (d : EuclideanDimension) (n : ℕ) :
    Set (Fin n → ComplexifiedSpacetime d) :=
  ⋃ transformation : ProperComplexLorentzTransformation d,
    ProperComplexLorentzTransformation.actConfiguration transformation ''
      wightmanBackwardTube d n

/-- Exact existential orbit characterization of extended-tube membership. -/
theorem mem_wightmanExtendedTube_iff
    {d : EuclideanDimension} {n : ℕ} (z : Fin n → ComplexifiedSpacetime d) :
    z ∈ wightmanExtendedTube d n ↔
      ∃ (transformation : ProperComplexLorentzTransformation d)
        (w : Fin n → ComplexifiedSpacetime d),
        w ∈ wightmanBackwardTube d n ∧
          z = ProperComplexLorentzTransformation.actConfiguration transformation w := by
  simp only [wightmanExtendedTube, Set.mem_iUnion, Set.mem_image]
  constructor
  · rintro ⟨transformation, w, hw, equality⟩
    exact ⟨transformation, w, hw, equality.symm⟩
  · rintro ⟨transformation, w, hw, rfl⟩
    exact ⟨transformation, w, hw, rfl⟩

/-- The image of the ordinary tube under one invertible action is the inverse-action preimage. -/
theorem properComplexLorentz_image_wightmanBackwardTube
    {d : EuclideanDimension} (n : ℕ)
    (transformation : ProperComplexLorentzTransformation d) :
    ProperComplexLorentzTransformation.actConfiguration transformation ''
        wightmanBackwardTube d n =
      ProperComplexLorentzTransformation.actConfiguration transformation⁻¹ ⁻¹'
        wightmanBackwardTube d n := by
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    simpa using hw
  · intro hz
    refine ⟨ProperComplexLorentzTransformation.actConfiguration transformation⁻¹ z,
      hz, ?_⟩
    simpa using
      (ProperComplexLorentzTransformation.actConfiguration_inv transformation⁻¹ z)

/-- Every fixed proper-complex-Lorentz image of the ordinary tube is open. -/
theorem isOpen_properComplexLorentz_image_wightmanBackwardTube
    {d : EuclideanDimension} (n : ℕ)
    (transformation : ProperComplexLorentzTransformation d) :
    IsOpen (ProperComplexLorentzTransformation.actConfiguration transformation ''
      wightmanBackwardTube d n) := by
  rw [properComplexLorentz_image_wightmanBackwardTube]
  exact (isOpen_wightmanBackwardTube d n).preimage
    (ProperComplexLorentzTransformation.continuous_actConfiguration transformation⁻¹ n)

/-- The exact extended tube is open as a union of open complex-Lorentz images. -/
theorem isOpen_wightmanExtendedTube (d : EuclideanDimension) (n : ℕ) :
    IsOpen (wightmanExtendedTube d n) := by
  apply isOpen_iUnion
  intro transformation
  exact isOpen_properComplexLorentz_image_wightmanBackwardTube n transformation

/-- The ordinary tube embeds through the identity transformation. -/
theorem wightmanBackwardTube_subset_extendedTube
    (d : EuclideanDimension) (n : ℕ) :
    wightmanBackwardTube d n ⊆ wightmanExtendedTube d n := by
  intro z hz
  rw [mem_wightmanExtendedTube_iff]
  exact ⟨1, z, hz, by rw [ProperComplexLorentzTransformation.actConfiguration_one]⟩

/-- Every finite-arity extended tube is nonempty. -/
theorem wightmanExtendedTube_nonempty (d : EuclideanDimension) (n : ℕ) :
    (wightmanExtendedTube d n).Nonempty :=
  (wightmanBackwardTube_nonempty d n).mono
    (wightmanBackwardTube_subset_extendedTube d n)

/-- The extended tube is invariant under every proper complex Lorentz transformation. -/
theorem wightmanExtendedTube_invariant
    {d : EuclideanDimension} {n : ℕ}
    (transformation : ProperComplexLorentzTransformation d)
    {z : Fin n → ComplexifiedSpacetime d}
    (hz : z ∈ wightmanExtendedTube d n) :
    ProperComplexLorentzTransformation.actConfiguration transformation z ∈
      wightmanExtendedTube d n := by
  rw [mem_wightmanExtendedTube_iff] at hz ⊢
  rcases hz with ⟨sourceTransformation, w, hw, rfl⟩
  exact ⟨transformation * sourceTransformation, w, hw,
    (ProperComplexLorentzTransformation.actConfiguration_mul
      transformation sourceTransformation w).symm⟩

/-- At positive arity the zero configuration is excluded even after taking the full invertible
complex-Lorentz orbit. -/
theorem zero_not_mem_wightmanExtendedTube
    (d : EuclideanDimension) {n : ℕ} (hn : 0 < n) :
    (0 : Fin n → ComplexifiedSpacetime d) ∉ wightmanExtendedTube d n := by
  rw [mem_wightmanExtendedTube_iff]
  rintro ⟨transformation, w, hw, equality⟩
  have wzero : w = 0 := by
    calc
      w = ProperComplexLorentzTransformation.actConfiguration transformation⁻¹
          (ProperComplexLorentzTransformation.actConfiguration transformation w) :=
        (ProperComplexLorentzTransformation.actConfiguration_inv transformation w).symm
      _ = ProperComplexLorentzTransformation.actConfiguration transformation⁻¹ 0 := by
        rw [← equality]
      _ = 0 := by
        funext j
        simp [ProperComplexLorentzTransformation.actConfiguration]
  subst w
  exact zero_not_mem_wightmanBackwardTube d hn hw

/-- Acting on the standard four-dimensional tube point by complex negation gives an explicit point
of the extended orbit. -/
def fourDimensionalExtendedTubeWitness (n : ℕ) :
    Fin n → ComplexifiedSpacetime EuclideanDimension.four :=
  ProperComplexLorentzTransformation.actConfiguration
    ProperComplexLorentzTransformation.fourDimensionalComplexNegation
    (standardWightmanBackwardTubePoint EuclideanDimension.four n)

/-- The explicit negated standard point lies in the extended tube. -/
theorem fourDimensionalExtendedTubeWitness_mem (n : ℕ) :
    fourDimensionalExtendedTubeWitness n ∈
      wightmanExtendedTube EuclideanDimension.four n := by
  rw [mem_wightmanExtendedTube_iff]
  exact ⟨ProperComplexLorentzTransformation.fourDimensionalComplexNegation,
    standardWightmanBackwardTubePoint EuclideanDimension.four n,
    standardWightmanBackwardTubePoint_mem EuclideanDimension.four n, rfl⟩

/-- At positive arity the explicit negated point is outside the original backward tube, proving
that the four-dimensional extended tube is strictly larger. -/
theorem fourDimensionalExtendedTubeWitness_not_mem_backwardTube
    {n : ℕ} (hn : 0 < n) :
    fourDimensionalExtendedTubeWitness n ∉
      wightmanBackwardTube EuclideanDimension.four n := by
  intro membership
  let j : Fin n := ⟨0, hn⟩
  have timePositive := (membership j).1
  simp [fourDimensionalExtendedTubeWitness,
    ProperComplexLorentzTransformation.actConfiguration,
    ProperComplexLorentzTransformation.fourDimensionalComplexNegation,
    standardWightmanBackwardTubePoint,
    complexifiedSpacetimeImaginaryPart,
    EuclideanDimension.timeIndex] at timePositive
  norm_num at timePositive

end

end YangMills.Minkowski
