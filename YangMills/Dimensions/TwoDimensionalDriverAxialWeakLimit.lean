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

/-- The coordinate map is a closed embedding: reverse compatibility is the intersection of
closed coordinate equalizers. -/
theorem epsilonSquareLatticeConfiguration_isClosedEmbedding
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    {spacing : PositiveLatticeSpacing} :
    Topology.IsClosedEmbedding
      (EpsilonSquareLatticeConfiguration.value (G := G) (spacing := spacing)) := by
  let f := EpsilonSquareLatticeConfiguration.value (G := G) (spacing := spacing)
  refine { eq_induced := rfl, injective := ?_, isClosed_range := ?_ }
  · intro x y equality
    cases x with
    | mk xValue xReverse =>
      cases y with
      | mk yValue yReverse =>
        change xValue = yValue at equality
        subst yValue
        rfl
  · have range_eq : Set.range f =
        ⋂ bond, {value : EpsilonSquareLatticeDirectedBond spacing → G |
          value bond.reverse = (value bond)⁻¹} := by
      ext value
      simp only [Set.mem_range, Set.mem_iInter, Set.mem_setOf_eq]
      constructor
      · rintro ⟨configuration, rfl⟩ bond
        exact configuration.reverse_value bond
      · intro reverseValue
        exact ⟨⟨value, reverseValue⟩, rfl⟩
    rw [range_eq]
    exact isClosed_iInter fun bond =>
      isClosed_eq (_root_.continuous_apply bond.reverse)
        ((_root_.continuous_apply bond).inv)

/-- Reverse-compatible configurations inherit compactness from the compact coordinate product. -/
instance epsilonSquareLatticeConfigurationCompactSpace
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G]
    {spacing : PositiveLatticeSpacing} :
    CompactSpace (EpsilonSquareLatticeConfiguration G spacing) :=
  epsilonSquareLatticeConfiguration_isClosedEmbedding.compactSpace

/-- The exact axial carrier is closedly embedded in the reverse-compatible configuration carrier. -/
theorem epsilonSquareLatticeAxialConfiguration_isClosedEmbedding
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    {spacing : PositiveLatticeSpacing} :
    Topology.IsClosedEmbedding
      (EpsilonSquareLatticeAxialConfiguration.configuration (G := G) (spacing := spacing)) := by
  let f := EpsilonSquareLatticeAxialConfiguration.configuration
    (G := G) (spacing := spacing)
  refine { eq_induced := rfl, injective := ?_, isClosed_range := ?_ }
  · intro x y equality
    cases x with
    | mk xConfiguration xFixed =>
      cases y with
      | mk yConfiguration yFixed =>
        change xConfiguration = yConfiguration at equality
        subst yConfiguration
        rfl
  · have range_eq : Set.range f =
        ⋂ (bond : EpsilonSquareLatticeDirectedBond spacing),
          ⋂ (_tree : epsilonSquareLatticeIsAxialTreeBond bond),
            {configuration : EpsilonSquareLatticeConfiguration G spacing |
              configuration bond = 1} := by
      ext configuration
      simp only [Set.mem_range, Set.mem_iInter, Set.mem_setOf_eq]
      constructor
      · rintro ⟨axial, rfl⟩ bond tree
        exact axial.axialTree_fixed bond tree
      · intro fixed
        exact ⟨⟨configuration, fixed⟩, rfl⟩
    rw [range_eq]
    exact isClosed_iInter fun bond => isClosed_iInter fun _tree =>
      isClosed_eq (EpsilonSquareLatticeConfiguration.continuous_apply bond) continuous_const

/-- For the countable lattice bond carrier, the induced measurable space on reverse-compatible
configurations is exactly Borel whenever the group topology is second countable. -/
instance epsilonSquareLatticeConfigurationBorelSpace
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
    {spacing : PositiveLatticeSpacing} :
    BorelSpace (EpsilonSquareLatticeConfiguration G spacing) := by
  let f := EpsilonSquareLatticeConfiguration.value (G := G) (spacing := spacing)
  have closedEmbedding : Topology.IsClosedEmbedding f :=
    epsilonSquareLatticeConfiguration_isClosedEmbedding
  have measurableEmbedding : MeasurableEmbedding f :=
    MeasurableEmbedding.iff_comap_eq.mpr
      ⟨closedEmbedding.injective, rfl, closedEmbedding.isClosed_range.measurableSet⟩
  exact measurableEmbedding.borelSpace closedEmbedding.isInducing

/-- Axial gauge fixing inherits compactness as a closed condition. -/
instance epsilonSquareLatticeAxialConfigurationCompactSpace
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G]
    {spacing : PositiveLatticeSpacing} :
    CompactSpace (EpsilonSquareLatticeAxialConfiguration G spacing) :=
  epsilonSquareLatticeAxialConfiguration_isClosedEmbedding.compactSpace

/-- Under the same countability hypothesis, the existing axial comap measurable space is Borel. -/
instance epsilonSquareLatticeAxialConfigurationBorelSpace
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
    {spacing : PositiveLatticeSpacing} :
    BorelSpace (EpsilonSquareLatticeAxialConfiguration G spacing) := by
  let f := EpsilonSquareLatticeAxialConfiguration.configuration
    (G := G) (spacing := spacing)
  have closedEmbedding : Topology.IsClosedEmbedding f :=
    epsilonSquareLatticeAxialConfiguration_isClosedEmbedding
  have measurableEmbedding : MeasurableEmbedding f :=
    MeasurableEmbedding.iff_comap_eq.mpr
      ⟨closedEmbedding.injective, rfl, closedEmbedding.isClosed_range.measurableSet⟩
  exact measurableEmbedding.borelSpace closedEmbedding.isInducing

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
    [CompactSpace G] [T2Space G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G] [MeasurableMul₂ G] [MeasurableInv G]
    (spacing : PositiveLatticeSpacing)
    (action : TwoDimensionalLatticeActionData G) : Type uG where
  limitMeasure : Measure (EpsilonSquareLatticeAxialConfiguration G spacing)
  bounded_continuous_convergence :
    ∀ (boundary : EpsilonSquareLatticeAxialConfiguration G spacing)
      (observable : BoundedContinuousRealFunction
        (EpsilonSquareLatticeAxialConfiguration G spacing)),
      Tendsto (fun stage => ∫ configuration, observable configuration
        ∂twoDimensionalSquareLatticeConditionedAxialMeasure
          spacing (driverFiniteVolumeRadius stage) action boundary) atTop
        (nhds (∫ configuration, observable configuration ∂limitMeasure))
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

/-- Countable-product Borel identification and compactness of the exact closed axial carrier derive
all structured continuous-test coverage. -/
theorem continuous_test_coverage
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G] [MeasurableMul₂ G] [MeasurableInv G]
    {spacing : PositiveLatticeSpacing} {action : TwoDimensionalLatticeActionData G}
    (_data : TwoDimensionalDriverAxialWeakLimitData spacing action)
    (observable : EpsilonSquareLatticeAxialConfiguration G spacing → ℝ)
    (continuous : Continuous observable) :
    ∃ test : BoundedContinuousRealFunction
        (EpsilonSquareLatticeAxialConfiguration G spacing),
      test.toFun = observable := by
  exact ⟨BoundedContinuousRealFunction.ofContinuous observable continuous, rfl⟩

/-- Convergence of the constant-one test against normalized conditioned laws derives normalization
of the designated common limit directly, without separately assuming its finiteness. -/
theorem limit_normalized
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G] [MeasurableMul₂ G] [MeasurableInv G]
    {spacing : PositiveLatticeSpacing} {action : TwoDimensionalLatticeActionData G}
    (data : TwoDimensionalDriverAxialWeakLimitData spacing action) :
    data.limitMeasure univ = 1 := by
  let boundary : EpsilonSquareLatticeAxialConfiguration G spacing :=
    EpsilonSquareLatticeAxialConfiguration.identity
  have massTendsto :
      Tendsto (fun stage => ∫ _ : EpsilonSquareLatticeAxialConfiguration G spacing, (1 : ℝ)
        ∂twoDimensionalSquareLatticeConditionedAxialMeasure
          spacing (driverFiniteVolumeRadius stage) action boundary) atTop
        (nhds (∫ _ : EpsilonSquareLatticeAxialConfiguration G spacing, (1 : ℝ)
          ∂data.limitMeasure)) := by
    simpa [BoundedContinuousRealFunction.one] using
      data.bounded_continuous_convergence boundary
        (BoundedContinuousRealFunction.one : BoundedContinuousRealFunction
          (EpsilonSquareLatticeAxialConfiguration G spacing))
  have sequenceIntegral :
      (fun stage => ∫ _ : EpsilonSquareLatticeAxialConfiguration G spacing, (1 : ℝ)
        ∂twoDimensionalSquareLatticeConditionedAxialMeasure
          spacing (driverFiniteVolumeRadius stage) action boundary) =
      fun _stage => (1 : ℝ) := by
    funext stage
    rw [integral_const, Measure.real_def,
      twoDimensionalSquareLatticeConditionedAxialMeasure.apply_univ]
    norm_num
  rw [sequenceIntegral] at massTendsto
  have limitIntegral :
      (∫ _ : EpsilonSquareLatticeAxialConfiguration G spacing, (1 : ℝ)
        ∂data.limitMeasure) = 1 :=
    tendsto_nhds_unique massTendsto tendsto_const_nhds
  rw [integral_const] at limitIntegral
  have toReal_eq_one : (data.limitMeasure univ).toReal = 1 := by
    simpa [Measure.real_def] using limitIntegral
  exact (ENNReal.toReal_eq_one_iff _).mp toReal_eq_one

/-- Finiteness of the common limit is a consequence of its derived normalization. -/
theorem limit_finite
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G] [MeasurableMul₂ G] [MeasurableInv G]
    {spacing : PositiveLatticeSpacing} {action : TwoDimensionalLatticeActionData G}
    (data : TwoDimensionalDriverAxialWeakLimitData spacing action) :
    data.limitMeasure univ ≠ ⊤ := by
  rw [data.limit_normalized]
  exact ENNReal.one_ne_top

/-- Exact normalization derives finiteness of both the conditioned sequence and its common limit;
test convergence then reconstructs the full weak-convergence predicate for every boundary. -/
theorem weak_limit_independent_of_boundary
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G] [MeasurableMul₂ G] [MeasurableInv G]
    {spacing : PositiveLatticeSpacing} {action : TwoDimensionalLatticeActionData G}
    (data : TwoDimensionalDriverAxialWeakLimitData spacing action)
    (boundary : EpsilonSquareLatticeAxialConfiguration G spacing) :
    WeaklyConvergesFiniteMeasures
      (fun stage => twoDimensionalSquareLatticeConditionedAxialMeasure
        spacing (driverFiniteVolumeRadius stage) action boundary)
      data.limitMeasure where
  sequence_finite := by
    intro stage
    rw [twoDimensionalSquareLatticeConditionedAxialMeasure.apply_univ]
    exact ENNReal.one_ne_top
  limit_finite := data.limit_finite
  tendsto_integral := data.bounded_continuous_convergence boundary

/-- Every two boundary conditions converge weakly to the same designated limit measure. -/
theorem boundary_pair
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G] [MeasurableMul₂ G] [MeasurableInv G]
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
