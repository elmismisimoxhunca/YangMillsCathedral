/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Dimensions.TwoDimensionalSquareLatticeFiniteVolumePlaquettes

/-!
# Driver's finite boundary-conditioned axial measure

This module constructs the gauge-fixed finite-volume law in Driver (7.2). For one axial boundary
configuration, its finite Haar coordinates are the exact off-tree variables of `Bₙ`; its density is
the product of one unchanged Definition 7.1 action over the exact interacting set `J(Bₙ)`. The
partition function is finite and nonzero, so the resulting finite-coordinate law and its pushforward
to the infinite axial carrier are normalized and nonzero.

This is a finite boundary-conditioned law. It proves neither boundary independence nor a weak
infinite-volume limit.
-/

namespace YangMills.Dimensions

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

/-- Exact Driver (7.2) density numerator on finite axial `Bₙ` coordinates. -/
def twoDimensionalSquareLatticeConditionedAxialWeight
    (configuration : EpsilonSquareLatticeConditionedAxialCoordinate spacing radius → G) : ENNReal :=
  ∏ plaquette : EpsilonSquareLatticeBoxPlaquette spacing radius,
    ENNReal.ofReal (action.action
      (epsilonSquareLatticeAxialPlaquetteHolonomy plaquette.1
        (epsilonSquareLatticeConditionedAxialExtension
          spacing radius boundary configuration)))

/-- Exact boundary-dependent partition function in Driver (7.2). -/
def twoDimensionalSquareLatticeConditionedAxialNormalizer : ENNReal :=
  ∫⁻ configuration,
    twoDimensionalSquareLatticeConditionedAxialWeight spacing radius action boundary configuration
      ∂normalizedCompactHaarFiniteProductMeasure
        (EpsilonSquareLatticeConditionedAxialCoordinate spacing radius) G

/-- Normalized finite-coordinate boundary-conditioned axial law. -/
def twoDimensionalSquareLatticeConditionedAxialFiniteMeasure :
    Measure (EpsilonSquareLatticeConditionedAxialCoordinate spacing radius → G) :=
  (twoDimensionalSquareLatticeConditionedAxialNormalizer spacing radius action boundary)⁻¹ •
    (normalizedCompactHaarFiniteProductMeasure
      (EpsilonSquareLatticeConditionedAxialCoordinate spacing radius) G).withDensity
      (twoDimensionalSquareLatticeConditionedAxialWeight spacing radius action boundary)

/-- Push the same finite-coordinate conditioned law through the exact boundary-retaining extension. -/
def twoDimensionalSquareLatticeConditionedAxialMeasure :
    Measure (EpsilonSquareLatticeAxialConfiguration G spacing) :=
  Measure.map (epsilonSquareLatticeConditionedAxialExtension spacing radius boundary)
    (twoDimensionalSquareLatticeConditionedAxialFiniteMeasure
      spacing radius action boundary)

namespace twoDimensionalSquareLatticeConditionedAxialWeight

omit [T2Space G] in
/-- The exact conditioned action weight is measurable. -/
theorem measurable : Measurable
    (twoDimensionalSquareLatticeConditionedAxialWeight spacing radius action boundary) := by
  apply Finset.measurable_prod
  intro plaquette _
  exact ENNReal.measurable_ofReal.comp
    (action.action_continuous.measurable.comp
      ((epsilonSquareLatticeAxialPlaquetteHolonomy.measurable plaquette.1).comp
        (epsilonSquareLatticeConditionedAxialExtension.measurable spacing radius boundary)))

omit [T2Space G] [MeasurableMul₂ G] [MeasurableInv G] in
/-- Strict positivity of the action makes the conditioned weight nonzero everywhere. -/
theorem ne_zero
    (configuration : EpsilonSquareLatticeConditionedAxialCoordinate spacing radius → G) :
    twoDimensionalSquareLatticeConditionedAxialWeight
      spacing radius action boundary configuration ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro plaquette _
  exact ne_of_gt (ENNReal.ofReal_pos.mpr (action.action_pos _))

end twoDimensionalSquareLatticeConditionedAxialWeight

namespace twoDimensionalSquareLatticeConditionedAxialNormalizer

omit [T2Space G] in
/-- The exact conditioned partition function is nonzero. -/
theorem ne_zero :
    twoDimensionalSquareLatticeConditionedAxialNormalizer
      spacing radius action boundary ≠ 0 := by
  apply ne_of_gt
  apply (lintegral_pos_iff_support
    (twoDimensionalSquareLatticeConditionedAxialWeight.measurable
      spacing radius action boundary)).mpr
  have support_eq : Function.support
      (twoDimensionalSquareLatticeConditionedAxialWeight
        spacing radius action boundary) = univ := by
    apply Set.eq_univ_of_forall
    intro configuration
    exact twoDimensionalSquareLatticeConditionedAxialWeight.ne_zero
      spacing radius action boundary configuration
  rw [support_eq, normalizedCompactHaarFiniteProductMeasure_univ]
  exact zero_lt_one

omit [T2Space G] [MeasurableMul₂ G] [MeasurableInv G] in
/-- Compactness uniformly bounds the action, so the exact conditioned partition function is finite. -/
theorem ne_top :
    twoDimensionalSquareLatticeConditionedAxialNormalizer
      spacing radius action boundary ≠ ⊤ := by
  obtain ⟨bound, boundProperty⟩ :=
    isCompact_univ.bddAbove_image action.action_continuous.continuousOn
  have action_le_bound : ∀ g, action.action g ≤ bound := by
    intro g
    exact boundProperty ⟨g, Set.mem_univ g, rfl⟩
  have weight_bound : ∀ configuration,
      twoDimensionalSquareLatticeConditionedAxialWeight
          spacing radius action boundary configuration ≤
        (ENNReal.ofReal bound) ^
          (Finset.univ : Finset (EpsilonSquareLatticeBoxPlaquette spacing radius)).card := by
    intro configuration
    change (∏ plaquette : EpsilonSquareLatticeBoxPlaquette spacing radius,
      ENNReal.ofReal (action.action
        (epsilonSquareLatticeAxialPlaquetteHolonomy plaquette.1
          (epsilonSquareLatticeConditionedAxialExtension
            spacing radius boundary configuration)))) ≤ _
    rw [← Finset.prod_const]
    apply Finset.prod_le_prod
    · intro plaquette _
      exact bot_le
    · intro plaquette _
      exact ENNReal.ofReal_le_ofReal (action_le_bound _)
  have integral_bound :
      twoDimensionalSquareLatticeConditionedAxialNormalizer
          spacing radius action boundary ≤
        (ENNReal.ofReal bound) ^
          (Finset.univ : Finset (EpsilonSquareLatticeBoxPlaquette spacing radius)).card := by
    apply le_trans (lintegral_mono weight_bound)
    simp [normalizedCompactHaarFiniteProductMeasure_univ]
  exact ne_top_of_le_ne_top
    (ENNReal.pow_ne_top ENNReal.ofReal_ne_top) integral_bound

end twoDimensionalSquareLatticeConditionedAxialNormalizer

namespace twoDimensionalSquareLatticeConditionedAxialFiniteMeasure

omit [T2Space G] in
/-- The finite-coordinate conditioned law has total mass one. -/
theorem apply_univ :
    twoDimensionalSquareLatticeConditionedAxialFiniteMeasure
      spacing radius action boundary univ = 1 := by
  rw [twoDimensionalSquareLatticeConditionedAxialFiniteMeasure,
    Measure.smul_apply, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  simp only [smul_eq_mul]
  change (twoDimensionalSquareLatticeConditionedAxialNormalizer
      spacing radius action boundary)⁻¹ *
    twoDimensionalSquareLatticeConditionedAxialNormalizer
      spacing radius action boundary = 1
  exact ENNReal.inv_mul_cancel
    (twoDimensionalSquareLatticeConditionedAxialNormalizer.ne_zero
      spacing radius action boundary)
    (twoDimensionalSquareLatticeConditionedAxialNormalizer.ne_top
      spacing radius action boundary)

omit [T2Space G] in
/-- The finite-coordinate conditioned law is nonzero. -/
theorem ne_zero :
    twoDimensionalSquareLatticeConditionedAxialFiniteMeasure
      spacing radius action boundary ≠ 0 := by
  intro zeroMeasure
  have normalized := apply_univ spacing radius action boundary
  rw [zeroMeasure] at normalized
  simp at normalized

end twoDimensionalSquareLatticeConditionedAxialFiniteMeasure

namespace twoDimensionalSquareLatticeConditionedAxialMeasure

omit [T2Space G] in
/-- The pushed conditioned law has total mass one on the infinite axial carrier. -/
theorem apply_univ :
    twoDimensionalSquareLatticeConditionedAxialMeasure
      spacing radius action boundary univ = 1 := by
  rw [twoDimensionalSquareLatticeConditionedAxialMeasure,
    Measure.map_apply
      (epsilonSquareLatticeConditionedAxialExtension.measurable spacing radius boundary)
      MeasurableSet.univ, preimage_univ]
  exact twoDimensionalSquareLatticeConditionedAxialFiniteMeasure.apply_univ
    spacing radius action boundary

omit [T2Space G] in
/-- The pushed conditioned law is nonzero. -/
theorem ne_zero :
    twoDimensionalSquareLatticeConditionedAxialMeasure
      spacing radius action boundary ≠ 0 := by
  intro zeroMeasure
  have normalized := apply_univ spacing radius action boundary
  rw [zeroMeasure] at normalized
  simp at normalized

omit [MeasurableMul₂ G] in
/-- Every frozen bond equals the supplied boundary value almost surely under the exact conditioned
law. -/
theorem boundary_ae
    (bond : EpsilonSquareLatticeDirectedBond spacing)
    (outside : epsilonSquareLatticeBoundaryConditionBond spacing radius bond) :
    (fun configuration : EpsilonSquareLatticeAxialConfiguration G spacing => configuration bond) =ᵐ[
      twoDimensionalSquareLatticeConditionedAxialMeasure spacing radius action boundary]
      fun _ => boundary bond := by
  rw [twoDimensionalSquareLatticeConditionedAxialMeasure]
  apply (ae_map_iff
    (epsilonSquareLatticeConditionedAxialExtension.measurable
      spacing radius boundary).aemeasurable (by
        change MeasurableSet ((fun configuration :
          EpsilonSquareLatticeAxialConfiguration G spacing => configuration bond) ⁻¹'
            {boundary bond})
        exact isClosed_singleton.measurableSet.preimage
          (EpsilonSquareLatticeAxialConfiguration.measurable_apply bond))).mpr
  filter_upwards [] with configuration
  exact epsilonSquareLatticeConditionedAxialExtension.boundary
    spacing radius boundary configuration bond outside

end twoDimensionalSquareLatticeConditionedAxialMeasure

end

end YangMills.Dimensions
