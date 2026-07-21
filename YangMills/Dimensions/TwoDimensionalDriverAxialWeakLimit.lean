/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Dimensions.TwoDimensionalSquareLatticeConditionedAxialMeasure
import YangMills.Mathematics.WeakMeasureConvergence

/-!
# Driver Theorem 7.2: gauge-fixed weak-limit acceptance surface

This module gives the infinite axial configuration carriers their natural induced product topologies
and states the full bounded-continuous weak-convergence and boundary-independence obligations from
Driver Theorem 7.2. It also requires the limit expectation of every bounded continuous observable
depending on `Bₙ` to equal the corresponding free finite-box expectation, as in (7.6).

The structure is intentionally uninhabited: no weak limit or boundary-independence theorem is proved.
-/

namespace YangMills.Dimensions

open Filter MeasureTheory Set
open YangMills.Mathematics

noncomputable section

universe uG

/-- Natural topology induced from all directed-bond coordinates. -/
instance epsilonSquareLatticeConfigurationTopologicalSpace
    {G : Type uG} [Group G] [TopologicalSpace G]
    {spacing : PositiveLatticeSpacing} :
    TopologicalSpace (EpsilonSquareLatticeConfiguration G spacing) :=
  TopologicalSpace.induced EpsilonSquareLatticeConfiguration.value inferInstance

/-- Natural topology on the axial subcarrier, induced from the full configuration carrier. -/
instance epsilonSquareLatticeAxialConfigurationTopologicalSpace
    {G : Type uG} [Group G] [TopologicalSpace G]
    {spacing : PositiveLatticeSpacing} :
    TopologicalSpace (EpsilonSquareLatticeAxialConfiguration G spacing) :=
  TopologicalSpace.induced EpsilonSquareLatticeAxialConfiguration.configuration inferInstance

namespace EpsilonSquareLatticeConfiguration

/-- Every directed-bond evaluation is continuous in the induced product topology. -/
theorem continuous_apply
    {G : Type uG} [Group G] [TopologicalSpace G]
    {spacing : PositiveLatticeSpacing}
    (bond : EpsilonSquareLatticeDirectedBond spacing) :
    Continuous (fun configuration : EpsilonSquareLatticeConfiguration G spacing =>
      configuration bond) :=
  (_root_.continuous_apply bond).comp continuous_induced_dom

end EpsilonSquareLatticeConfiguration

namespace EpsilonSquareLatticeAxialConfiguration

/-- Every directed-bond evaluation remains continuous on the axial carrier. -/
theorem continuous_apply
    {G : Type uG} [Group G] [TopologicalSpace G]
    {spacing : PositiveLatticeSpacing}
    (bond : EpsilonSquareLatticeDirectedBond spacing) :
    Continuous (fun configuration : EpsilonSquareLatticeAxialConfiguration G spacing =>
      configuration bond) :=
  (EpsilonSquareLatticeConfiguration.continuous_apply bond).comp continuous_induced_dom

end EpsilonSquareLatticeAxialConfiguration

/-- Positive box radius `N+1` used to index Driver's boundary-conditioned sequence by naturals. -/
def driverFiniteVolumeRadius (stage : ℕ) : PositiveSquareLatticeBoxRadius :=
  ⟨stage + 1, Nat.zero_lt_succ stage⟩

@[simp]
theorem driverFiniteVolumeRadius_value (stage : ℕ) :
    (driverFiniteVolumeRadius stage).1 = stage + 1 :=
  rfl

/-- An observable depends only on Driver's finite bond set `Bₙ`. -/
def TwoDimensionalAxialObservableDependsOnFiniteVolume
    {G : Type uG} [Group G]
    (spacing : PositiveLatticeSpacing) (radius : PositiveSquareLatticeBoxRadius)
    (observable : EpsilonSquareLatticeAxialConfiguration G spacing → ℝ) : Prop :=
  ∀ first second,
    (∀ bond, epsilonSquareLatticeFiniteVolumeBond spacing radius bond →
      first bond = second bond) →
    observable first = observable second

/-- Source-facing acceptance surface for the gauge-fixed assertions of Driver Theorem 7.2. -/
structure TwoDimensionalDriverAxialWeakLimitData
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    [MeasurableMul₂ G] [MeasurableInv G]
    (spacing : PositiveLatticeSpacing)
    (action : TwoDimensionalLatticeActionData G) : Type uG where
  continuous_test_coverage :
    ∀ observable : EpsilonSquareLatticeAxialConfiguration G spacing → ℝ,
      Continuous observable →
      ∃ test : BoundedContinuousRealFunction
          (EpsilonSquareLatticeAxialConfiguration G spacing),
        test.toFun = observable
  limitMeasure : Measure (EpsilonSquareLatticeAxialConfiguration G spacing)
  limit_normalized : limitMeasure univ = 1
  weak_limit_independent_of_boundary :
    ∀ boundary : EpsilonSquareLatticeAxialConfiguration G spacing,
      WeaklyConvergesFiniteMeasures
        (fun stage => twoDimensionalSquareLatticeConditionedAxialMeasure
          spacing (driverFiniteVolumeRadius stage) action boundary)
        limitMeasure
  free_finite_volume_identification :
    ∀ (radius : PositiveSquareLatticeBoxRadius)
      (observable : BoundedContinuousRealFunction
        (EpsilonSquareLatticeAxialConfiguration G spacing)),
      TwoDimensionalAxialObservableDependsOnFiniteVolume
        spacing radius observable →
      (∫ configuration, observable configuration ∂limitMeasure) =
        ∫ configuration, observable configuration
          ∂twoDimensionalSquareLatticeBoxPushforwardMeasure spacing radius action

namespace TwoDimensionalDriverAxialWeakLimitData

/-- Every two boundary conditions converge weakly to the same designated limit measure. -/
theorem boundary_pair
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    [MeasurableMul₂ G] [MeasurableInv G]
    {spacing : PositiveLatticeSpacing} {action : TwoDimensionalLatticeActionData G}
    (data : TwoDimensionalDriverAxialWeakLimitData spacing action)
    (first second : EpsilonSquareLatticeAxialConfiguration G spacing) :
    WeaklyConvergesFiniteMeasures
        (fun stage => twoDimensionalSquareLatticeConditionedAxialMeasure
          spacing (driverFiniteVolumeRadius stage) action first)
        data.limitMeasure ∧
      WeaklyConvergesFiniteMeasures
        (fun stage => twoDimensionalSquareLatticeConditionedAxialMeasure
          spacing (driverFiniteVolumeRadius stage) action second)
        data.limitMeasure :=
  ⟨data.weak_limit_independent_of_boundary first,
    data.weak_limit_independent_of_boundary second⟩

end TwoDimensionalDriverAxialWeakLimitData

end

end YangMills.Dimensions
