/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Dimensions.TwoDimensionalSquareLatticeConditionedAxialMeasure

/-!
# Probes for Driver's finite conditioned axial measure
-/

namespace YangMills.Dimensions.TwoDimensionalSquareLatticeConditionedAxialMeasure.Probes

open MeasureTheory Set
open YangMills.Mathematics

noncomputable section

universe uG

variable
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    [MeasurableMul₂ G] [MeasurableInv G]
    (spacing : PositiveLatticeSpacing) (radius : PositiveSquareLatticeBoxRadius)
    (action : TwoDimensionalLatticeActionData G)
    (boundary : EpsilonSquareLatticeAxialConfiguration G spacing)

/-- Every density factor is indexed by an actual interacting plaquette `J(Bₙ)`. -/
theorem every_weight_plaquette_interacting
    (plaquette : EpsilonSquareLatticeBoxPlaquette spacing radius) :
    epsilonSquareLatticeFiniteVolumeInteractingPlaquette spacing radius plaquette.1 :=
  (epsilonSquareLatticeFiniteVolumeInteractingPlaquette.iff_box
    spacing radius plaquette.1).mpr plaquette.2

omit [T2Space G] in
/-- The conditioned partition function is both nonzero and finite. -/
theorem exact_normalizer_contract :
    twoDimensionalSquareLatticeConditionedAxialNormalizer
        spacing radius action boundary ≠ 0 ∧
      twoDimensionalSquareLatticeConditionedAxialNormalizer
        spacing radius action boundary ≠ ⊤ :=
  ⟨twoDimensionalSquareLatticeConditionedAxialNormalizer.ne_zero
      spacing radius action boundary,
    twoDimensionalSquareLatticeConditionedAxialNormalizer.ne_top
      spacing radius action boundary⟩

omit [T2Space G] in
/-- The finite-coordinate law is normalized and nonzero. -/
theorem exact_finite_measure_contract :
    twoDimensionalSquareLatticeConditionedAxialFiniteMeasure
        spacing radius action boundary univ = 1 ∧
      twoDimensionalSquareLatticeConditionedAxialFiniteMeasure
        spacing radius action boundary ≠ 0 :=
  ⟨twoDimensionalSquareLatticeConditionedAxialFiniteMeasure.apply_univ
      spacing radius action boundary,
    twoDimensionalSquareLatticeConditionedAxialFiniteMeasure.ne_zero
      spacing radius action boundary⟩

omit [T2Space G] in
/-- The pushed law on the infinite axial carrier is normalized and nonzero. -/
theorem exact_pushforward_measure_contract :
    twoDimensionalSquareLatticeConditionedAxialMeasure
        spacing radius action boundary univ = 1 ∧
      twoDimensionalSquareLatticeConditionedAxialMeasure
        spacing radius action boundary ≠ 0 :=
  ⟨twoDimensionalSquareLatticeConditionedAxialMeasure.apply_univ
      spacing radius action boundary,
    twoDimensionalSquareLatticeConditionedAxialMeasure.ne_zero
      spacing radius action boundary⟩

omit [MeasurableMul₂ G] in
/-- Every frozen bond equals the designated boundary value almost surely. -/
theorem exact_boundary_support
    (bond : EpsilonSquareLatticeDirectedBond spacing)
    (outside : epsilonSquareLatticeBoundaryConditionBond spacing radius bond) :
    (fun configuration : EpsilonSquareLatticeAxialConfiguration G spacing => configuration bond) =ᵐ[
      twoDimensionalSquareLatticeConditionedAxialMeasure spacing radius action boundary]
      fun _ => boundary bond :=
  twoDimensionalSquareLatticeConditionedAxialMeasure.boundary_ae
    spacing radius action boundary bond outside

omit [T2Space G] in
/-- A zero conditioned partition function is hostilely rejected. -/
theorem zero_normalizer_blocked
    (claimed : twoDimensionalSquareLatticeConditionedAxialNormalizer
      spacing radius action boundary = 0) : False :=
  (twoDimensionalSquareLatticeConditionedAxialNormalizer.ne_zero
    spacing radius action boundary) claimed

omit [T2Space G] [MeasurableMul₂ G] [MeasurableInv G] in
/-- An infinite conditioned partition function is hostilely rejected. -/
theorem infinite_normalizer_blocked
    (claimed : twoDimensionalSquareLatticeConditionedAxialNormalizer
      spacing radius action boundary = ⊤) : False :=
  (twoDimensionalSquareLatticeConditionedAxialNormalizer.ne_top
    spacing radius action boundary) claimed

omit [T2Space G] in
/-- A zero conditioned probability law is hostilely rejected. -/
theorem zero_conditioned_measure_blocked
    (claimed : twoDimensionalSquareLatticeConditionedAxialMeasure
      spacing radius action boundary = 0) : False :=
  (twoDimensionalSquareLatticeConditionedAxialMeasure.ne_zero
    spacing radius action boundary) claimed

/-- These finite two-dimensional laws cannot satisfy a four-dimensional endpoint. -/
theorem conditioned_measure_not_four_dimensional :
    EuclideanDimension.two ≠ EuclideanDimension.four :=
  EuclideanDimension.two_ne_four

end

end YangMills.Dimensions.TwoDimensionalSquareLatticeConditionedAxialMeasure.Probes
