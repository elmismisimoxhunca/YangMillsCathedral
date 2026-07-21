/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Dimensions.TwoDimensionalFiniteAxialPlaquetteMeasure

/-!
# Finite axial measure on the exact infinite configuration carrier

The normalized finite-coordinate measure is pushed through the same measurable finite-support axial
extension stored by its presentation. This produces an actual measure on the exact infinite axial
carrier and proves its represented-coordinate cylinder marginals. It remains a finite-support
pushforward, not Driver's infinite-volume limit.
-/

namespace YangMills.Dimensions

open MeasureTheory Set

noncomputable section

universe uG uCoordinate uPlaquette

variable
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [MeasurableSpace G] [BorelSpace G] [MeasurableMul₂ G]
    {spacing : PositiveLatticeSpacing}

/-- Push the normalized finite-coordinate law to the exact infinite axial configuration carrier. -/
def twoDimensionalFiniteAxialPushforwardMeasure
    (action : TwoDimensionalLatticeActionData G)
    (presentation : TwoDimensionalFiniteAxialPlaquettePresentationData.{uG, uCoordinate, uPlaquette}
      G spacing) : Measure (EpsilonSquareLatticeAxialConfiguration G spacing) := by
  letI := presentation.coordinateFintype
  exact Measure.map presentation.extension
    (twoDimensionalFiniteAxialMeasure action presentation)

namespace twoDimensionalFiniteAxialPushforwardMeasure

omit [MeasurableMul₂ G] in
/-- The pushforward has total mass one because the source measure does. -/
theorem apply_univ
    (action : TwoDimensionalLatticeActionData G)
    (presentation : TwoDimensionalFiniteAxialPlaquettePresentationData.{uG, uCoordinate, uPlaquette}
      G spacing)
    (normalizer : TwoDimensionalFiniteAxialNormalizerData action presentation) :
    twoDimensionalFiniteAxialPushforwardMeasure action presentation univ = 1 := by
  letI := presentation.coordinateFintype
  rw [twoDimensionalFiniteAxialPushforwardMeasure,
    Measure.map_apply presentation.extension_measurable MeasurableSet.univ, preimage_univ]
  exact twoDimensionalFiniteAxialMeasure.apply_univ action presentation normalizer

omit [MeasurableMul₂ G] in
/-- The normalized pushforward measure is nonzero. -/
theorem ne_zero
    (action : TwoDimensionalLatticeActionData G)
    (presentation : TwoDimensionalFiniteAxialPlaquettePresentationData.{uG, uCoordinate, uPlaquette}
      G spacing)
    (normalizer : TwoDimensionalFiniteAxialNormalizerData action presentation) :
    twoDimensionalFiniteAxialPushforwardMeasure action presentation ≠ 0 := by
  intro zeroMeasure
  have normalized := apply_univ action presentation normalizer
  rw [zeroMeasure] at normalized
  simp at normalized

omit [MeasurableMul₂ G] in
/-- Every represented infinite-bond coordinate has exactly the corresponding finite-coordinate
marginal; this is a measure-level anti-disconnection bridge. -/
theorem coordinate_marginal
    (action : TwoDimensionalLatticeActionData G)
    (presentation : TwoDimensionalFiniteAxialPlaquettePresentationData.{uG, uCoordinate, uPlaquette}
      G spacing)
    (coordinate : presentation.Coordinate) :
    Measure.map
        (fun configuration : EpsilonSquareLatticeAxialConfiguration G spacing =>
          configuration (presentation.coordinateBond coordinate))
        (twoDimensionalFiniteAxialPushforwardMeasure action presentation) =
      Measure.map (fun configuration : presentation.Coordinate → G => configuration coordinate)
        (twoDimensionalFiniteAxialMeasure action presentation) := by
  letI := presentation.coordinateFintype
  rw [twoDimensionalFiniteAxialPushforwardMeasure]
  rw [Measure.map_map
    (EpsilonSquareLatticeAxialConfiguration.measurable_apply
      (presentation.coordinateBond coordinate))
    presentation.extension_measurable]
  apply Measure.map_congr
  filter_upwards [] with configuration
  exact presentation.extension_coordinate configuration coordinate

end twoDimensionalFiniteAxialPushforwardMeasure

end

end YangMills.Dimensions
