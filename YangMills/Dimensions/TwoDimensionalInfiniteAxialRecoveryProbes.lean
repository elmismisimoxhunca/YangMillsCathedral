/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Dimensions.TwoDimensionalInfiniteAxialRecovery

/-!
# Hostile probes for exact infinite axial recovery
-/

namespace YangMills.Dimensions.TwoDimensionalInfiniteAxialRecovery.Probes

noncomputable section

universe uG

variable {G : Type uG} [Group G] (spacing : PositiveLatticeSpacing)

/-- The first upper/lower rooted values retain opposite noncommutative orientations. -/
theorem exact_first_rooted_values
    (plaquettes : EpsilonSquareLatticePlaquette spacing → G) (horizontal : ℤ) :
    infiniteAxialUpperHorizontalRecover spacing plaquettes horizontal 1 =
        (plaquettes ⟨(horizontal, 0)⟩)⁻¹ ∧
      infiniteAxialLowerHorizontalRecover spacing plaquettes horizontal 1 =
        plaquettes ⟨(horizontal, -1)⟩ := by
  simp [infiniteAxialUpperHorizontalRecover, infiniteAxialLowerHorizontalRecover]

/-- Recovered configurations satisfy exact reverse inversion and fix every axial-tree bond. -/
theorem exact_reverse_and_tree
    (plaquettes : EpsilonSquareLatticePlaquette spacing → G)
    (bond : EpsilonSquareLatticeDirectedBond spacing)
    (tree : epsilonSquareLatticeIsAxialTreeBond bond) :
    infiniteAxialRecover spacing plaquettes bond.reverse =
        (infiniteAxialRecover spacing plaquettes bond)⁻¹ ∧
      infiniteAxialRecover spacing plaquettes bond = 1 :=
  ⟨(infiniteAxialRecover spacing plaquettes).configuration.reverse_value bond,
    (infiniteAxialRecover spacing plaquettes).axialTree_fixed bond tree⟩

/-- Every global input plaquette is recovered as the holonomy of the same output configuration. -/
theorem exact_global_plaquette_right_inverse
    (plaquettes : EpsilonSquareLatticePlaquette spacing → G)
    (plaquette : EpsilonSquareLatticePlaquette spacing) :
    epsilonSquareLatticeAxialPlaquetteHolonomy plaquette
        (infiniteAxialRecover spacing plaquettes) = plaquettes plaquette :=
  infiniteAxialRecover_plaquetteHolonomy spacing plaquettes plaquette

/-- Finite box coordinates are exactly the existing recursive recovery of the literal finite
plaquette restriction. -/
theorem exact_finite_recovery_coherence
    (radius : PositiveSquareLatticeBoxRadius)
    (plaquettes : EpsilonSquareLatticePlaquette spacing → G) :
    (fun coordinate : EpsilonSquareLatticeBoxCoordinate spacing radius =>
      infiniteAxialRecover spacing plaquettes coordinate.1) =
      boxPlaquetteDifferenceRecover spacing radius
        (infinitePlaquetteBoxRestriction spacing radius plaquettes) :=
  infiniteAxialRecover_boxCoordinateRestriction spacing radius plaquettes

section Measurable

variable [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]

/-- Global recovery and every finite plaquette restriction are measurable. -/
theorem exact_recovery_measurable (radius : PositiveSquareLatticeBoxRadius) :
    Measurable (infiniteAxialRecover (G := G) spacing) ∧
      Measurable (infinitePlaquetteBoxRestriction (G := G) spacing radius) :=
  ⟨infiniteAxialRecover_measurable spacing,
    infinitePlaquetteBoxRestriction_measurable spacing radius⟩

end Measurable

/-- Any proposed axial recovery whose holonomy misses even one input plaquette is provably
 different from the exact recovery. -/
theorem mismatched_plaquette_recovery_blocked
    (plaquettes : EpsilonSquareLatticePlaquette spacing → G)
    (wrong : EpsilonSquareLatticeAxialConfiguration G spacing)
    (plaquette : EpsilonSquareLatticePlaquette spacing)
    (mismatch : epsilonSquareLatticeAxialPlaquetteHolonomy plaquette wrong ≠
      plaquettes plaquette) :
    wrong ≠ infiniteAxialRecover spacing plaquettes := by
  intro equality
  subst wrong
  exact mismatch (infiniteAxialRecover_plaquetteHolonomy spacing plaquettes plaquette)

/-- Replacing the upper root step by a non-inverted plaquette value is rejected whenever inversion
is genuinely nontrivial. -/
theorem uninverted_upper_root_blocked
    (plaquettes : EpsilonSquareLatticePlaquette spacing → G) (horizontal : ℤ)
    (nonselfInverse : (plaquettes ⟨(horizontal, 0)⟩)⁻¹ ≠
      plaquettes ⟨(horizontal, 0)⟩)
    (claimed : infiniteAxialUpperHorizontalRecover spacing plaquettes horizontal 1 =
      plaquettes ⟨(horizontal, 0)⟩) : False := by
  have exactStep : infiniteAxialUpperHorizontalRecover spacing plaquettes horizontal 1 =
      (plaquettes ⟨(horizontal, 0)⟩)⁻¹ := by
    simp [infiniteAxialUpperHorizontalRecover]
  exact nonselfInverse (exactStep.symm.trans claimed)

/-- Infinite axial recovery remains two-dimensional evidence only. -/
theorem infinite_recovery_not_four_dimensional :
    EuclideanDimension.two ≠ EuclideanDimension.four :=
  EuclideanDimension.two_ne_four

end

end YangMills.Dimensions.TwoDimensionalInfiniteAxialRecovery.Probes
