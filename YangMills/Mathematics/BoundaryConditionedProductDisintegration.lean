/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import Mathlib.Probability.Kernel.Disintegration.StandardBorel
import Mathlib.Probability.Kernel.Composition.MeasureComp

/-!
# Exact boundary-conditioned product disintegrations

This file packages a genuine kernel disintegration in which every boundary-conditioned restriction
law is an exact product. The interface deliberately distinguishes:

* an unconditional measure from its boundary marginal;
* a measurable Markov kernel from an arbitrary pointwise family of measures;
* disintegration from an all-boundary-value product identity; and
* reversal of the second boundary orientation from the unchanged first boundary value.

The all-value product identity is stronger than generic regular conditional probability, whose
versions are determined only almost everywhere. Source-facing applications must justify that
stronger field separately. No surface or Yang--Mills measure is constructed here.
-/

namespace YangMills.Mathematics

open MeasureTheory ProbabilityTheory Set

noncomputable section

universe uBoundary uLeft uRight uWhole

/-- A genuine disintegration over a boundary marginal, with exact product restrictions at every
boundary value and explicit reversal on the second factor. -/
structure BoundaryConditionedProductDisintegrationData
    (Boundary : Type uBoundary) (Left : Type uLeft) (Right : Type uRight)
    (Whole : Type uWhole)
    [MeasurableSpace Boundary] [MeasurableSpace Left] [MeasurableSpace Right]
    [MeasurableSpace Whole] where
  boundaryReverse : Boundary → Boundary
  boundaryReverse_measurable : Measurable boundaryReverse
  boundaryReverse_involutive : Function.Involutive boundaryReverse
  wholeMeasure : Measure Whole
  boundaryMarginal : Measure Boundary
  boundaryMarginal_probability : IsProbabilityMeasure boundaryMarginal
  conditionedWhole : Kernel Boundary Whole
  conditionedWhole_markov : IsMarkovKernel conditionedWhole
  conditionedLeft : Kernel Boundary Left
  conditionedLeft_markov : IsMarkovKernel conditionedLeft
  conditionedRight : Kernel Boundary Right
  conditionedRight_markov : IsMarkovKernel conditionedRight
  boundaryValue : Whole → Boundary
  boundaryValue_measurable : Measurable boundaryValue
  restriction : Whole → Left × Right
  restriction_measurable : Measurable restriction
  boundaryMarginal_eq_map : boundaryMarginal = Measure.map boundaryValue wholeMeasure
  /-- Mathlib's genuine conditional-kernel disintegration of the joint boundary/whole law. -/
  conditionedWhole_disintegration : Measure.IsCondKernel
    (Measure.map (fun whole => (boundaryValue whole, whole)) wholeMeasure) conditionedWhole
  /-- Every selected all-value version gives zero mass to the complement of its exact boundary
  fiber. This formulation remains genuine without assuming measurable singletons; unlike assigning
  outer measure one to a possibly nonmeasurable fiber, it really excludes mass outside the fiber.
  It is stronger than generic almost-everywhere uniqueness and must be justified by a source-facing
  application. -/
  conditionedWhole_outside_boundary_fiber : ∀ boundary,
    conditionedWhole boundary {whole | boundaryValue whole ≠ boundary} = 0
  /-- Exact all-boundary-value product law. The right side uses the inverse/reversed boundary
  orientation. -/
  conditioned_restriction_product : ∀ boundary,
    Measure.map restriction (conditionedWhole boundary) =
      (conditionedLeft boundary).prod (conditionedRight (boundaryReverse boundary))

namespace BoundaryConditionedProductDisintegrationData

variable
    {Boundary : Type uBoundary} {Left : Type uLeft} {Right : Type uRight}
    {Whole : Type uWhole}
    [MeasurableSpace Boundary] [MeasurableSpace Left] [MeasurableSpace Right]
    [MeasurableSpace Whole]

/-- The stored boundary reversal is bijective; inverse orientation cannot collapse boundary values. -/
theorem boundaryReverse_bijective
    (data : BoundaryConditionedProductDisintegrationData Boundary Left Right Whole) :
    Function.Bijective data.boundaryReverse :=
  data.boundaryReverse_involutive.bijective

/-- Mathlib's joint conditional-kernel disintegration derives the corresponding bind reconstruction
of the whole-space law. -/
theorem disintegration
    (data : BoundaryConditionedProductDisintegrationData Boundary Left Right Whole) :
    Measure.bind data.boundaryMarginal data.conditionedWhole = data.wholeMeasure := by
  let joint : Measure (Boundary × Whole) :=
    Measure.map (fun whole => (data.boundaryValue whole, whole)) data.wholeMeasure
  letI : IsProbabilityMeasure data.boundaryMarginal := data.boundaryMarginal_probability
  letI : IsMarkovKernel data.conditionedWhole := data.conditionedWhole_markov
  letI : Measure.IsCondKernel joint data.conditionedWhole :=
    data.conditionedWhole_disintegration
  have firstMap : joint.fst = Measure.map data.boundaryValue data.wholeMeasure := by
    simpa [joint] using
      (Measure.fst_map_prodMk (μ := data.wholeMeasure)
        (X := data.boundaryValue) (Y := id) measurable_id)
  have first : joint.fst = data.boundaryMarginal := by
    rw [firstMap]
    exact data.boundaryMarginal_eq_map.symm
  have second : joint.snd = data.wholeMeasure := by
    have secondMap : joint.snd = Measure.map id data.wholeMeasure := by
      simpa [joint] using
        (Measure.snd_map_prodMk (μ := data.wholeMeasure)
          (X := data.boundaryValue) (Y := id) data.boundaryValue_measurable)
    rw [secondMap]
    simp
  have jointEquality := Measure.disintegrate joint data.conditionedWhole
  rw [first] at jointEquality
  have marginalEquality := congrArg Measure.snd jointEquality
  rw [Measure.snd_compProd, second] at marginalEquality
  exact marginalEquality

/-- The unconditional whole-space measure is probability normalized by genuine disintegration of a
probability boundary marginal through a Markov kernel. -/
theorem wholeMeasure_univ
    (data : BoundaryConditionedProductDisintegrationData Boundary Left Right Whole) :
    data.wholeMeasure univ = 1 := by
  letI : IsProbabilityMeasure data.boundaryMarginal := data.boundaryMarginal_probability
  letI : IsMarkovKernel data.conditionedWhole := data.conditionedWhole_markov
  rw [← data.disintegration, Measure.bind_apply MeasurableSet.univ data.conditionedWhole.aemeasurable]
  simp

/-- The unconditional whole-space measure cannot be zero. -/
theorem wholeMeasure_ne_zero
    (data : BoundaryConditionedProductDisintegrationData Boundary Left Right Whole) :
    data.wholeMeasure ≠ 0 := by
  intro zero
  have normalized := data.wholeMeasure_univ
  rw [zero] at normalized
  simp at normalized

/-- Exact left marginal of every boundary-conditioned whole-space restriction. -/
theorem conditioned_left_marginal
    (data : BoundaryConditionedProductDisintegrationData Boundary Left Right Whole)
    (boundary : Boundary) :
    Measure.map (fun whole => (data.restriction whole).1) (data.conditionedWhole boundary) =
      data.conditionedLeft boundary := by
  letI : IsMarkovKernel data.conditionedLeft := data.conditionedLeft_markov
  letI : IsMarkovKernel data.conditionedRight := data.conditionedRight_markov
  change Measure.map (Prod.fst ∘ data.restriction) (data.conditionedWhole boundary) = _
  rw [← Measure.map_map measurable_fst data.restriction_measurable]
  rw [data.conditioned_restriction_product boundary, Measure.map_fst_prod]
  simp

/-- Exact right marginal of every boundary-conditioned whole-space restriction, retaining the
reversed boundary value. -/
theorem conditioned_right_marginal
    (data : BoundaryConditionedProductDisintegrationData Boundary Left Right Whole)
    (boundary : Boundary) :
    Measure.map (fun whole => (data.restriction whole).2) (data.conditionedWhole boundary) =
      data.conditionedRight (data.boundaryReverse boundary) := by
  letI : IsMarkovKernel data.conditionedLeft := data.conditionedLeft_markov
  letI : IsMarkovKernel data.conditionedRight := data.conditionedRight_markov
  change Measure.map (Prod.snd ∘ data.restriction) (data.conditionedWhole boundary) = _
  rw [← Measure.map_map measurable_snd data.restriction_measurable]
  rw [data.conditioned_restriction_product boundary, Measure.map_snd_prod]
  simp

/-- The boundary marginal is exactly the pushforward of the reconstructed whole-space probability
law, rather than an unrelated parameter measure. -/
theorem exact_boundary_pushforward
    (data : BoundaryConditionedProductDisintegrationData Boundary Left Right Whole) :
    Measure.map data.boundaryValue data.wholeMeasure = data.boundaryMarginal :=
  data.boundaryMarginal_eq_map.symm

end BoundaryConditionedProductDisintegrationData

end

end YangMills.Mathematics
