/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Dimensions.TwoDimensionalDriverAxialWeakLimit
import YangMills.Mathematics.WeakMeasureConvergenceProbes

/-!
# Probes for Driver's axial weak-limit acceptance surface
-/

namespace YangMills.Dimensions.TwoDimensionalDriverAxialWeakLimit.Probes

open Filter MeasureTheory Set
open YangMills.Mathematics

noncomputable section

universe uG

variable
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G]
    [MeasurableMul₂ G] [MeasurableInv G]
    (spacing : PositiveLatticeSpacing) (action : TwoDimensionalLatticeActionData G)

omit [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [SecondCountableTopology G]
    [MeasurableSpace G]
    [BorelSpace G] [MeasurableMul₂ G] [MeasurableInv G] in
/-- Bond evaluation is continuous in the exact induced product topology. -/
theorem exact_coordinate_continuous (bond : EpsilonSquareLatticeDirectedBond spacing) :
    Continuous (fun configuration : EpsilonSquareLatticeAxialConfiguration G spacing =>
      configuration bond) :=
  EpsilonSquareLatticeAxialConfiguration.continuous_apply bond

omit [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    [MeasurableMul₂ G] [MeasurableInv G] in
/-- Reverse compatibility and axial fixing are closed conditions, so both exact infinite product
carriers inherit compactness rather than assuming bounded observables. -/
theorem exact_configuration_compactness :
    CompactSpace (EpsilonSquareLatticeConfiguration G spacing) ∧
      CompactSpace (EpsilonSquareLatticeAxialConfiguration G spacing) :=
  ⟨inferInstance, inferInstance⟩

omit [CompactSpace G] [MeasurableMul₂ G] [MeasurableInv G] in
/-- Countability of the exact directed-bond carrier identifies both induced product sigma algebras
with the corresponding Borel spaces. -/
theorem exact_configuration_borel :
    BorelSpace (EpsilonSquareLatticeConfiguration G spacing) ∧
      BorelSpace (EpsilonSquareLatticeAxialConfiguration G spacing) :=
  ⟨inferInstance, inferInstance⟩

omit [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [SecondCountableTopology G] [BorelSpace G] [MeasurableMul₂ G] [MeasurableInv G] in
/-- The constant-one observable makes the finite-volume dependence scope nonempty. -/
theorem constant_one_depends_on_every_finite_volume
    (radius : PositiveSquareLatticeBoxRadius) :
    TwoDimensionalAxialObservableDependsOnFiniteVolume spacing radius
      (BoundedContinuousRealFunction.one : BoundedContinuousRealFunction
        (EpsilonSquareLatticeAxialConfiguration G spacing)) := by
  intro first second agreement
  rfl

/-- Every continuous real observable is explicitly covered by a measurable bounded test, closing
the topology/measurability and compact-boundedness bridge required by Driver's quantifier. -/
theorem every_continuous_observable_covered
    (data : TwoDimensionalDriverAxialWeakLimitData spacing action)
    (observable : EpsilonSquareLatticeAxialConfiguration G spacing → ℝ)
    (continuous : Continuous observable) :
    ∃ test : BoundedContinuousRealFunction
        (EpsilonSquareLatticeAxialConfiguration G spacing),
      test.toFun = observable :=
  data.continuous_test_coverage observable continuous

/-- Every pair of axial boundary conditions converges to the same designated limit. -/
theorem exact_boundary_independence
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
  data.boundary_pair first second

/-- Each boundary sequence and its common limit are genuinely finite measures. -/
theorem exact_weak_finiteness
    (data : TwoDimensionalDriverAxialWeakLimitData spacing action)
    (boundary : EpsilonSquareLatticeAxialConfiguration G spacing) :
    (∀ stage, twoDimensionalSquareLatticeConditionedAxialMeasure
        spacing (driverFiniteVolumeRadius stage) action boundary univ ≠ ⊤) ∧
      data.limitMeasure univ ≠ ⊤ := by
  have weak := data.weak_limit_independent_of_boundary boundary
  exact ⟨weak.sequence_finite, weak.limit_finite⟩

/-- The limit agrees exactly with the free finite law on every eligible finite-volume observable. -/
theorem exact_free_finite_identification
    (data : TwoDimensionalDriverAxialWeakLimitData spacing action)
    (radius : PositiveSquareLatticeBoxRadius)
    (observable : BoundedContinuousRealFunction
      (EpsilonSquareLatticeAxialConfiguration G spacing))
    (depends : TwoDimensionalAxialObservableDependsOnFiniteVolume
      spacing radius observable) :
    (∫ configuration, observable configuration ∂data.limitMeasure) =
      ∫ configuration, observable configuration
        ∂twoDimensionalSquareLatticeBoxPushforwardMeasure spacing radius action :=
  data.free_finite_volume_identification radius observable depends

/-- Normalization of the common weak limit is derived from normalized conditioned laws and the
constant-one mass test. -/
theorem exact_derived_limit_normalization
    (data : TwoDimensionalDriverAxialWeakLimitData spacing action) :
    data.limitMeasure univ = 1 :=
  data.limit_normalized

/-- A zero designated weak limit is hostilely rejected by derived normalization. -/
theorem zero_limit_blocked
    (data : TwoDimensionalDriverAxialWeakLimitData spacing action)
    (claimed : data.limitMeasure = 0) : False := by
  have normalized := data.limit_normalized
  rw [claimed] at normalized
  simp at normalized

/-- Failure of the free finite-volume identity for one eligible observable is hostilely rejected. -/
theorem wrong_free_finite_identification_blocked
    (data : TwoDimensionalDriverAxialWeakLimitData spacing action)
    (radius : PositiveSquareLatticeBoxRadius)
    (observable : BoundedContinuousRealFunction
      (EpsilonSquareLatticeAxialConfiguration G spacing))
    (depends : TwoDimensionalAxialObservableDependsOnFiniteVolume
      spacing radius observable)
    (failed : (∫ configuration, observable configuration ∂data.limitMeasure) ≠
      ∫ configuration, observable configuration
        ∂twoDimensionalSquareLatticeBoxPushforwardMeasure spacing radius action) : False :=
  failed (data.free_finite_volume_identification radius observable depends)

/-- Driver's two-dimensional weak limit cannot discharge a four-dimensional endpoint. -/
theorem weak_limit_not_four_dimensional :
    EuclideanDimension.two ≠ EuclideanDimension.four :=
  EuclideanDimension.two_ne_four

end

end YangMills.Dimensions.TwoDimensionalDriverAxialWeakLimit.Probes
