/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Dimensions.FourDimensionalCurrentStrengthUniversalAcceptance
import YangMills.Dimensions.FourDimensionalContractSeparation

/-!
# Hostile probes for the current-strength universal four-dimensional target

These probes verify the outer gauge quantifier, exact certificate indexing, fixed dimension, and
same-core physical gap projection. They do not inhabit the universal proposition.
-/

namespace YangMills.Dimensions.FourDimensionalCurrentStrengthUniversalAcceptance.Probes

open scoped Manifold ContDiff

universe uEG uGauge uEP uHP uP uLift uH uLabel

noncomputable section

variable
    {EG : Type uEG} {GaugeGroup : Type uGauge}
    [NormedAddCommGroup EG] [NormedSpace ℝ EG] [FiniteDimensional ℝ EG]
    [Group GaugeGroup] [TopologicalSpace GaugeGroup] [T2Space GaugeGroup]
    [SecondCountableTopology GaugeGroup] [ChartedSpace EG GaugeGroup]
    [LieGroup (modelWithCornersSelf ℝ EG) ∞ GaugeGroup]
    {gauge : Geometry.CompactSimpleGaugeGroupData GaugeGroup EG}

/-- The universal target specializes to every caller-selected exact compact-simple input. This
checks that the gauge group is universally quantified rather than existentially hidden. -/
theorem exact_universal_specialization
    (acceptance : FourDimensionalCurrentStrengthUniversalAcceptance.{
      uEG, uGauge, uEP, uHP, uP, uLift, uH, uLabel}) :
    Nonempty
      (FourDimensionalCurrentStrengthTheoryWitness.{
        uEG, uGauge, uEP, uHP, uP, uLift, uH, uLabel} EG GaugeGroup gauge) :=
  acceptance EG GaugeGroup gauge

/-- A packaged witness's core uses exactly the caller-supplied gauge certificate and remains
hard-wired to four spacetime dimensions. -/
theorem exact_witness_gauge_and_dimension
    (witness : FourDimensionalCurrentStrengthTheoryWitness.{
      uEG, uGauge, uEP, uHP, uP, uLift, uH, uLabel} EG GaugeGroup gauge) :
    letI : IsTopologicalGroup GaugeGroup := witness.gaugeTopologicalGroup
    letI : NormedAddCommGroup witness.EP := witness.epNormedAddCommGroup
    letI : NormedSpace ℝ witness.EP := witness.epNormedSpace
    letI : TopologicalSpace witness.HP := witness.hpTopologicalSpace
    letI : TopologicalSpace witness.P := witness.pTopologicalSpace
    letI : ChartedSpace witness.HP witness.P := witness.pChartedSpace
    letI : IsManifold witness.IP ∞ witness.P := witness.pIsManifold
    letI : Group witness.PoincareLiftGroup := witness.liftGroup
    letI : TopologicalSpace witness.PoincareLiftGroup := witness.liftTopology
    letI : IsTopologicalGroup witness.PoincareLiftGroup := witness.liftTopologicalGroup
    letI : NormedAddCommGroup witness.H := witness.hNormedAddCommGroup
    letI : InnerProductSpace ℂ witness.H := witness.hInnerProductSpace
    letI : CompleteSpace witness.H := witness.hCompleteSpace
    letI : TopologicalSpace.SeparableSpace witness.H := witness.hSeparableSpace
    witness.core.compactSimpleGaugeGroup = gauge ∧
      EuclideanDimension.four.value = 4 ∧
      EuclideanDimension.four.spatialDimension = 3 := by
  letI : IsTopologicalGroup GaugeGroup := witness.gaugeTopologicalGroup
  letI : NormedAddCommGroup witness.EP := witness.epNormedAddCommGroup
  letI : NormedSpace ℝ witness.EP := witness.epNormedSpace
  letI : TopologicalSpace witness.HP := witness.hpTopologicalSpace
  letI : TopologicalSpace witness.P := witness.pTopologicalSpace
  letI : ChartedSpace witness.HP witness.P := witness.pChartedSpace
  letI : IsManifold witness.IP ∞ witness.P := witness.pIsManifold
  letI : Group witness.PoincareLiftGroup := witness.liftGroup
  letI : TopologicalSpace witness.PoincareLiftGroup := witness.liftTopology
  letI : IsTopologicalGroup witness.PoincareLiftGroup := witness.liftTopologicalGroup
  letI : NormedAddCommGroup witness.H := witness.hNormedAddCommGroup
  letI : InnerProductSpace ℂ witness.H := witness.hInnerProductSpace
  letI : CompleteSpace witness.H := witness.hCompleteSpace
  letI : TopologicalSpace.SeparableSpace witness.H := witness.hSeparableSpace
  exact ⟨witness.core_gauge_eq, witness.core.exact_dimension⟩

/-- The projected gap remains the exact physical gap on the same joint spectrum selected inside the
unchanged core. -/
theorem exact_witness_same_spectrum_gap
    (witness : FourDimensionalCurrentStrengthTheoryWitness.{
      uEG, uGauge, uEP, uHP, uP, uLift, uH, uLabel} EG GaugeGroup gauge) :
    letI : IsTopologicalGroup GaugeGroup := witness.gaugeTopologicalGroup
    letI : NormedAddCommGroup witness.EP := witness.epNormedAddCommGroup
    letI : NormedSpace ℝ witness.EP := witness.epNormedSpace
    letI : TopologicalSpace witness.HP := witness.hpTopologicalSpace
    letI : TopologicalSpace witness.P := witness.pTopologicalSpace
    letI : ChartedSpace witness.HP witness.P := witness.pChartedSpace
    letI : IsManifold witness.IP ∞ witness.P := witness.pIsManifold
    letI : Group witness.PoincareLiftGroup := witness.liftGroup
    letI : TopologicalSpace witness.PoincareLiftGroup := witness.liftTopology
    letI : IsTopologicalGroup witness.PoincareLiftGroup := witness.liftTopologicalGroup
    letI : NormedAddCommGroup witness.H := witness.hNormedAddCommGroup
    letI : InnerProductSpace ℂ witness.H := witness.hInnerProductSpace
    letI : CompleteSpace witness.H := witness.hCompleteSpace
    letI : TopologicalSpace.SeparableSpace witness.H := witness.hSeparableSpace
    witness.core.wightmanSurface.HasPhysicalMassGap witness.core.gapThreshold := by
  letI : IsTopologicalGroup GaugeGroup := witness.gaugeTopologicalGroup
  letI : NormedAddCommGroup witness.EP := witness.epNormedAddCommGroup
  letI : NormedSpace ℝ witness.EP := witness.epNormedSpace
  letI : TopologicalSpace witness.HP := witness.hpTopologicalSpace
  letI : TopologicalSpace witness.P := witness.pTopologicalSpace
  letI : ChartedSpace witness.HP witness.P := witness.pChartedSpace
  letI : IsManifold witness.IP ∞ witness.P := witness.pIsManifold
  letI : Group witness.PoincareLiftGroup := witness.liftGroup
  letI : TopologicalSpace witness.PoincareLiftGroup := witness.liftTopology
  letI : IsTopologicalGroup witness.PoincareLiftGroup := witness.liftTopologicalGroup
  letI : NormedAddCommGroup witness.H := witness.hNormedAddCommGroup
  letI : InnerProductSpace ℂ witness.H := witness.hInnerProductSpace
  letI : CompleteSpace witness.H := witness.hCompleteSpace
  letI : TopologicalSpace.SeparableSpace witness.H := witness.hSeparableSpace
  exact witness.core.physicalMassGap

/-- Lower-dimensional coordinate carriers still cannot replace the witness's exact four-dimensional
base. -/
theorem lower_dimensional_carrier_blocked
    (d : EuclideanDimension)
    (lower : d = EuclideanDimension.one ∨ d = EuclideanDimension.two ∨
      d = EuclideanDimension.three) :
    ¬ Nonempty (d.Spacetime ≃ₗ[ℝ] FourDimensionalEuclideanBase) :=
  lowerDimensionalSpacetime_not_linearEquiv_four d lower

end

end YangMills.Dimensions.FourDimensionalCurrentStrengthUniversalAcceptance.Probes
