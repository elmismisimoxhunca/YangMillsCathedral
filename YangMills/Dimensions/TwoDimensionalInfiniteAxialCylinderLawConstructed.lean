/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Dimensions.TwoDimensionalInfiniteAxialRecovery
import Mathlib.Probability.ProductMeasure

/-!
# Constructed infinite axial cylinder law

The infinite product of the normalized one-plaquette action law is pushed through exact measurable
axial recovery. Product-measure finite marginals and finite recovery coherence identify every exact
box cylinder with the previously constructed box law, yielding the infinite-cylinder contract for
the exhaustive square-box projective sequence.

This is the free infinite axial cylinder law. It is not Driver's boundary-conditioned Theorem 7.2
weak-convergence theorem or a lattice-continuum limit.
-/

namespace YangMills.Dimensions

open MeasureTheory Set
open YangMills.Mathematics

noncomputable section

universe uG

variable {G : Type uG} [Group G]
    (spacing : PositiveLatticeSpacing)

section InfiniteMeasure

variable [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [MeasurableSpace G] [BorelSpace G] [MeasurableMul₂ G] [MeasurableInv G]
    (action : TwoDimensionalLatticeActionData G)

/-- IID global plaquette action product measure. -/
def infinitePlaquetteActionProductMeasure :
    Measure (EpsilonSquareLatticePlaquette spacing → G) :=
  Measure.infinitePi fun _ : EpsilonSquareLatticePlaquette spacing =>
    twoDimensionalPlaquetteActionMeasure action

/-- Push the IID global plaquette law through exact infinite axial recovery. -/
def infiniteAxialRecoveredMeasure :
    Measure (EpsilonSquareLatticeAxialConfiguration G spacing) :=
  Measure.map (infiniteAxialRecover spacing)
    (infinitePlaquetteActionProductMeasure spacing action)

/-- Restr an infinite axial configuration to exact box coordinates. -/
def infiniteAxialBoxCoordinateRestriction (radius : PositiveSquareLatticeBoxRadius) :
    EpsilonSquareLatticeAxialConfiguration G spacing →
      (EpsilonSquareLatticeBoxCoordinate spacing radius → G) :=
  fun configuration coordinate => configuration coordinate.1

omit [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [BorelSpace G] [MeasurableMul₂ G] [MeasurableInv G] in
/-- The infinite axial coordinate restriction is measurable. -/
theorem infiniteAxialBoxCoordinateRestriction_measurable
    (radius : PositiveSquareLatticeBoxRadius) :
    Measurable (infiniteAxialBoxCoordinateRestriction (G := G) spacing radius) := by
  apply measurable_pi_iff.mpr
  intro coordinate
  exact EpsilonSquareLatticeAxialConfiguration.measurable_apply coordinate.1

omit [MeasurableMul₂ G] [MeasurableInv G] in
/-- The global IID plaquette product has the expected exact finite-box plaquette marginal. -/
theorem infinitePlaquetteActionProductMeasure_box_marginal
    (radius : PositiveSquareLatticeBoxRadius) :
    Measure.map (infinitePlaquetteBoxRestriction (G := G) spacing radius)
        (infinitePlaquetteActionProductMeasure spacing action) =
      twoDimensionalPlaquetteActionFiniteProduct
        (EpsilonSquareLatticeBoxPlaquette spacing radius) action := by
  let μ := twoDimensionalPlaquetteActionMeasure action
  letI : ∀ _ : EpsilonSquareLatticePlaquette spacing, IsProbabilityMeasure μ :=
    fun _ => twoDimensionalPlaquetteActionMeasure.instIsProbabilityMeasure action
  change Measure.map (epsilonSquareLatticeBoxPlaquettes spacing radius).restrict
      (Measure.infinitePi fun _ : EpsilonSquareLatticePlaquette spacing => μ) =
    Measure.pi fun _ : EpsilonSquareLatticeBoxPlaquette spacing radius => μ
  exact Measure.infinitePi_map_restrict
    (fun _ : EpsilonSquareLatticePlaquette spacing => μ)
    (I := epsilonSquareLatticeBoxPlaquettes spacing radius)

/-- Finite recursive recovery sends the finite plaquette action product back to the existing box
coordinate law. -/
theorem map_boxPlaquetteDifferenceRecover_actionProduct
    (radius : PositiveSquareLatticeBoxRadius) :
    Measure.map (boxPlaquetteDifferenceRecover (G := G) spacing radius)
        (twoDimensionalPlaquetteActionFiniteProduct
          (EpsilonSquareLatticeBoxPlaquette spacing radius) action) =
      twoDimensionalSquareLatticeBoxMeasure spacing radius action := by
  let equiv := boxPlaquetteDifferenceMeasurableEquiv (G := G) spacing radius
  have factor :=
    map_twoDimensionalSquareLatticeBoxMeasure_eq_plaquetteActionFiniteProduct
      spacing radius action
  change Measure.map equiv
      (twoDimensionalSquareLatticeBoxMeasure spacing radius action) = _ at factor
  have mappedBack := congrArg (Measure.map equiv.symm) factor
  change Measure.map equiv.symm
      (twoDimensionalPlaquetteActionFiniteProduct
        (EpsilonSquareLatticeBoxPlaquette spacing radius) action) =
    twoDimensionalSquareLatticeBoxMeasure spacing radius action
  simpa only [equiv.map_symm_map] using mappedBack.symm

omit [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [MeasurableSpace G] [BorelSpace G] [MeasurableMul₂ G] [MeasurableInv G] in
/-- The global recovery/finite restriction square is pointwise exact. -/
theorem infiniteAxialRecover_boxRestriction_commutes
    (radius : PositiveSquareLatticeBoxRadius) :
    infiniteAxialBoxCoordinateRestriction (G := G) spacing radius ∘
        infiniteAxialRecover spacing =
      boxPlaquetteDifferenceRecover spacing radius ∘
        infinitePlaquetteBoxRestriction spacing radius := by
  funext plaquettes
  exact infiniteAxialRecover_boxCoordinateRestriction spacing radius plaquettes

/-- Every exact finite box restriction of the recovered infinite measure is the existing box law. -/
theorem infiniteAxialRecoveredMeasure_box_marginal
    (radius : PositiveSquareLatticeBoxRadius) :
    Measure.map (infiniteAxialBoxCoordinateRestriction (G := G) spacing radius)
        (infiniteAxialRecoveredMeasure spacing action) =
      twoDimensionalSquareLatticeBoxMeasure spacing radius action := by
  let coordinateRestriction :=
    infiniteAxialBoxCoordinateRestriction (G := G) spacing radius
  let plaquetteRestriction :=
    infinitePlaquetteBoxRestriction (G := G) spacing radius
  let recover := infiniteAxialRecover (G := G) spacing
  let finiteRecover := boxPlaquetteDifferenceRecover (G := G) spacing radius
  let infiniteMeasure := infinitePlaquetteActionProductMeasure spacing action
  have coordinateMeasurable : Measurable coordinateRestriction :=
    infiniteAxialBoxCoordinateRestriction_measurable spacing radius
  have recoverMeasurable : Measurable recover := infiniteAxialRecover_measurable spacing
  have plaquetteMeasurable : Measurable plaquetteRestriction :=
    infinitePlaquetteBoxRestriction_measurable spacing radius
  have finiteRecoverMeasurable : Measurable finiteRecover :=
    boxPlaquetteDifferenceRecover_measurable spacing radius
  have commuting : coordinateRestriction ∘ recover = finiteRecover ∘ plaquetteRestriction :=
    infiniteAxialRecover_boxRestriction_commutes spacing radius
  change Measure.map coordinateRestriction (Measure.map recover infiniteMeasure) = _
  calc
    Measure.map coordinateRestriction (Measure.map recover infiniteMeasure) =
        Measure.map (coordinateRestriction ∘ recover) infiniteMeasure :=
      Measure.map_map coordinateMeasurable recoverMeasurable
    _ = Measure.map (finiteRecover ∘ plaquetteRestriction) infiniteMeasure := by rw [commuting]
    _ = Measure.map finiteRecover (Measure.map plaquetteRestriction infiniteMeasure) :=
      (Measure.map_map finiteRecoverMeasurable plaquetteMeasurable).symm
    _ = Measure.map finiteRecover
        (twoDimensionalPlaquetteActionFiniteProduct
          (EpsilonSquareLatticeBoxPlaquette spacing radius) action) := by
      rw [infinitePlaquetteActionProductMeasure_box_marginal]
    _ = twoDimensionalSquareLatticeBoxMeasure spacing radius action :=
      map_boxPlaquetteDifferenceRecover_actionProduct spacing action radius

/-- Exact infinite axial cylinder law for the constructed exhaustive square-box projective
sequence. -/
def twoDimensionalSquareLatticeInfiniteAxialCylinderLawData :
    TwoDimensionalAxialInfiniteVolumeCylinderLawData (spacing := spacing) action
      (twoDimensionalSquareLatticeBoxProjectiveSequenceData spacing action) where
  probabilityMeasure := infiniteAxialRecoveredMeasure spacing action
  finiteCylinderLaw stage := by
    change Measure.map
      (infiniteAxialBoxCoordinateRestriction (G := G) spacing
        (squareLatticeBoxProjectiveRadius stage))
      (infiniteAxialRecoveredMeasure spacing action) =
      twoDimensionalSquareLatticeBoxMeasure spacing
        (squareLatticeBoxProjectiveRadius stage) action
    exact infiniteAxialRecoveredMeasure_box_marginal spacing action
      (squareLatticeBoxProjectiveRadius stage)

end InfiniteMeasure

end

end YangMills.Dimensions
