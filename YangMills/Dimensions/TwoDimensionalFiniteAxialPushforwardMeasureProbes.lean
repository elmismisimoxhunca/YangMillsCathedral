/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Dimensions.TwoDimensionalFiniteAxialPushforwardMeasure
import YangMills.Dimensions.TwoDimensionalFiniteAxialPlaquetteMeasureProbes

/-!
# Probes for finite axial pushforward measures
-/

namespace YangMills.Dimensions.TwoDimensionalFiniteAxialPushforwardMeasure.Probes

open MeasureTheory Set

noncomputable section

universe uG uCoordinate uPlaquette

variable
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [MeasurableSpace G] [BorelSpace G] [MeasurableMul₂ G]
    {spacing : PositiveLatticeSpacing}

omit [MeasurableMul₂ G] in
/-- The infinite-carrier law is literally the map of the normalized finite-coordinate law through
the same stored extension. -/
theorem exact_pushforward_formula
    (action : TwoDimensionalLatticeActionData G)
    (presentation : TwoDimensionalFiniteAxialPlaquettePresentationData.{uG, uCoordinate, uPlaquette}
      G spacing) :
    twoDimensionalFiniteAxialPushforwardMeasure action presentation =
      Measure.map presentation.extension
        (twoDimensionalFiniteAxialMeasure action presentation) :=
  rfl

omit [MeasurableMul₂ G] in
/-- Normalization and nonzeroness survive on the exact infinite axial carrier. -/
theorem exact_pushforward_contract
    (action : TwoDimensionalLatticeActionData G)
    (presentation : TwoDimensionalFiniteAxialPlaquettePresentationData.{uG, uCoordinate, uPlaquette}
      G spacing)
    (normalizer : TwoDimensionalFiniteAxialNormalizerData action presentation) :
    twoDimensionalFiniteAxialPushforwardMeasure action presentation univ = 1 ∧
      twoDimensionalFiniteAxialPushforwardMeasure action presentation ≠ 0 :=
  ⟨twoDimensionalFiniteAxialPushforwardMeasure.apply_univ action presentation normalizer,
    twoDimensionalFiniteAxialPushforwardMeasure.ne_zero action presentation normalizer⟩

omit [MeasurableMul₂ G] in
/-- Every represented infinite-bond marginal is exactly its finite-coordinate marginal. -/
theorem exact_coordinate_marginal
    (action : TwoDimensionalLatticeActionData G)
    (presentation : TwoDimensionalFiniteAxialPlaquettePresentationData.{uG, uCoordinate, uPlaquette}
      G spacing)
    (coordinate : presentation.Coordinate) :
    Measure.map
        (fun configuration : EpsilonSquareLatticeAxialConfiguration G spacing =>
          configuration (presentation.coordinateBond coordinate))
        (twoDimensionalFiniteAxialPushforwardMeasure action presentation) =
      Measure.map (fun configuration : presentation.Coordinate → G => configuration coordinate)
        (twoDimensionalFiniteAxialMeasure action presentation) :=
  twoDimensionalFiniteAxialPushforwardMeasure.coordinate_marginal
    action presentation coordinate

omit [MeasurableMul₂ G] in
/-- A zero pushforward is incompatible with its exact partition-function certificate. -/
theorem zero_pushforward_blocked
    (action : TwoDimensionalLatticeActionData G)
    (presentation : TwoDimensionalFiniteAxialPlaquettePresentationData.{uG, uCoordinate, uPlaquette}
      G spacing)
    (normalizer : TwoDimensionalFiniteAxialNormalizerData action presentation)
    (claimed : twoDimensionalFiniteAxialPushforwardMeasure action presentation = 0) : False :=
  (twoDimensionalFiniteAxialPushforwardMeasure.ne_zero action presentation normalizer) claimed

/-- The positive unit presentation yields an actual normalized measure on the exact infinite axial
carrier; this is finite-support anti-vacuity only. -/
theorem unit_pushforward_normalized :
    twoDimensionalFiniteAxialPushforwardMeasure
        (TwoDimensionalLatticeActionData.constantOne (G := Unit))
        (TwoDimensionalFiniteAxialPlaquetteMeasure.Probes.unitPresentation
          (spacing := spacing)) univ = 1 :=
  twoDimensionalFiniteAxialPushforwardMeasure.apply_univ _ _
    (TwoDimensionalFiniteAxialPlaquetteMeasure.Probes.unitNormalizerData
      (spacing := spacing))

end

end YangMills.Dimensions.TwoDimensionalFiniteAxialPushforwardMeasure.Probes
