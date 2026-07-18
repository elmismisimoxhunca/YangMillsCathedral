/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Minkowski.WeakOperatorProductExpansion
import YangMills.Renormalization.RunningCoupling
import YangMills.Renormalization.SchwartzScaling

/-!
# Supplied regular-variation scaling of weak OPE coefficients

Clay requires OPE singularities prescribed by asymptotic freedom and perturbative renormalization.
This module provides a *supplied preliminary regular-variation condition* for every nonzero
coefficient of one exact weak OPE. Tests are normalized by `r⁻ᵈ f(·/r)`, short distance uses logarithmic scale
`t = -log r`, and the rescaled coefficient converges in Mathlib's pointwise/weak tempered-
distribution topology to a nonzero leading distribution.

Signed real scaling degrees and real running-coupling exponents are explicit supplied data; a
negative degree permits regular or vanishing coefficients. This condition is not derived from the
cited papers and does not by itself satisfy Clay's prescribed-singularity requirement. It remains a
preliminary normal form: the group-dependent beta coefficient, renormalization scheme, operator
mixing, and perturbative coefficient calculation are not constructed.
-/

namespace YangMills.Renormalization

open Filter Set Topology
open scoped Manifold ContDiff

noncomputable section

/-- Dimensionless ultraviolet logarithmic scale associated to positive short distance `r`. -/
def shortDistanceLogScale (r : ℝ) : ℝ :=
  -Real.log r

/-- Positive short distance reaches arbitrarily far along the ultraviolet logarithmic scale. -/
theorem shortDistanceLogScale_tendsto_atTop :
    Tendsto shortDistanceLogScale (nhdsWithin 0 (Ioi 0)) atTop := by
  have h := Filter.Tendsto.const_mul_atBot_of_neg (r := (-1 : ℝ)) (by norm_num)
    Real.tendsto_log_nhdsGT_zero
  convert h using 1
  funext r
  simp [shortDistanceLogScale]

/-- Every supplied ultraviolet threshold is eventually crossed at short positive distance. -/
theorem eventually_shortDistanceLogScale_gt (threshold : ℝ) :
    ∀ᶠ r in nhdsWithin 0 (Ioi 0), threshold < shortDistanceLogScale r :=
  shortDistanceLogScale_tendsto_atTop (Ioi_mem_atTop threshold)

/-- Distributional coefficient rescaling by a radial engineering degree and a real power of the
same running coupling. -/
def rescaledOPECoefficient
    {d : EuclideanDimension}
    {Gauge GaugeModel : Type*}
    [NormedAddCommGroup GaugeModel] [NormedSpace ℝ GaugeModel]
    [FiniteDimensional ℝ GaugeModel]
    [Group Gauge] [TopologicalSpace Gauge] [T2Space Gauge]
    [SecondCountableTopology Gauge] [ChartedSpace GaugeModel Gauge]
    [LieGroup (modelWithCornersSelf ℝ GaugeModel) ∞ Gauge]
    {gaugeGroup : Geometry.CompactSimpleGaugeGroupData Gauge GaugeModel}
    (freedom : PureYangMillsAsymptoticFreedomData d gaugeGroup)
    (radialScalingDegree couplingExponent : ℝ)
    (coefficient : TemperedDistribution
      (Minkowski.BilocalRelativeConfiguration d) ℂ)
    (r : ℝ) :
    TemperedDistribution (Minkowski.BilocalRelativeConfiguration d) ℂ :=
  let radialFactor : ℝ := Real.rpow r radialScalingDegree
  let couplingFactor : ℝ := Real.rpow
    (freedom.runningCoupling (shortDistanceLogScale r)) couplingExponent
  let pulledBack : TemperedDistribution (Minkowski.BilocalRelativeConfiguration d) ℂ :=
    ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ)
      (SchwartzMap (Minkowski.BilocalRelativeConfiguration d) ℂ) ℂ
      (coefficient.comp (normalizedRelativeSchwartzDilationCLM d r))
  ((radialFactor : ℂ) * (couplingFactor : ℂ)⁻¹) • pulledBack

/-- Evaluation exposes the exact normalized test dilation and running-coupling factor. -/
@[simp]
theorem rescaledOPECoefficient_apply
    {d : EuclideanDimension}
    {Gauge GaugeModel : Type*}
    [NormedAddCommGroup GaugeModel] [NormedSpace ℝ GaugeModel]
    [FiniteDimensional ℝ GaugeModel]
    [Group Gauge] [TopologicalSpace Gauge] [T2Space Gauge]
    [SecondCountableTopology Gauge] [ChartedSpace GaugeModel Gauge]
    [LieGroup (modelWithCornersSelf ℝ GaugeModel) ∞ Gauge]
    {gaugeGroup : Geometry.CompactSimpleGaugeGroupData Gauge GaugeModel}
    (freedom : PureYangMillsAsymptoticFreedomData d gaugeGroup)
    (radialScalingDegree couplingExponent : ℝ)
    (coefficient : TemperedDistribution
      (Minkowski.BilocalRelativeConfiguration d) ℂ)
    (r : ℝ) (test : Minkowski.ScalarMinkowskiSchwartzTestFunction d) :
    rescaledOPECoefficient freedom radialScalingDegree couplingExponent coefficient r test =
      ((Real.rpow r radialScalingDegree : ℂ) *
        (Real.rpow (freedom.runningCoupling (shortDistanceLogScale r))
          couplingExponent : ℂ)⁻¹) *
        coefficient (normalizedRelativeSchwartzDilationCLM d r test) := by
  rw [rescaledOPECoefficient]
  rfl

/-- All nonzero coefficient distributions in one exact weak OPE have prescribed asymptotically free
short-distance scaling normal forms. -/
structure SuppliedWeakOPERegularVariationData
    {d : EuclideanDimension}
    {Gauge GaugeModel : Type*}
    [NormedAddCommGroup GaugeModel] [NormedSpace ℝ GaugeModel]
    [FiniteDimensional ℝ GaugeModel]
    [Group Gauge] [TopologicalSpace Gauge] [T2Space Gauge]
    [SecondCountableTopology Gauge] [ChartedSpace GaugeModel Gauge]
    [LieGroup (modelWithCornersSelf ℝ GaugeModel) ∞ Gauge]
    {gaugeGroup : Geometry.CompactSimpleGaugeGroupData Gauge GaugeModel}
    (freedom : PureYangMillsAsymptoticFreedomData d gaugeGroup)
    {PoincareGroup : Type*}
    [Group PoincareGroup] [TopologicalSpace PoincareGroup]
    [IsTopologicalGroup PoincareGroup]
    {lift : Minkowski.ProperOrthochronousPoincareLiftData d PoincareGroup}
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H]
    {U : Minkowski.StronglyContinuousUnitaryPoincareRepresentation lift H}
    {vacuumData : Minkowski.PoincareInvariantVacuumData U}
    {D : Minkowski.CommonInvariantDomainData vacuumData}
    {family : Minkowski.TemperedLocalObservableFamilyData D}
    [DecidableEq family.Label]
    {products : Minkowski.WeakTemperedBilocalObservableProductData family}
    (ope : Minkowski.WeakOperatorProductExpansionData products) where
  /-- Signed radial short-distance degree for each ordered coefficient. Under the convention used
  here, negative degree permits a regular or vanishing coefficient. -/
  radialScalingDegree : family.Label → family.Label → family.Label → ℝ
  /-- Real exponent of the same running coupling, allowing noninteger logarithmic powers. -/
  couplingExponent : family.Label → family.Label → family.Label → ℝ
  /-- Nonzero leading tempered distribution for every nonzero coefficient. -/
  leadingDistribution : family.Label → family.Label → family.Label →
    TemperedDistribution (Minkowski.BilocalRelativeConfiguration d) ℂ
  leadingDistribution_nonzero : ∀ A B C,
    ope.coefficient A B C ≠ 0 → leadingDistribution A B C ≠ 0
  /-- Exact weak tempered-distribution scaling limit at short positive distance. -/
  coefficient_scaling : ∀ A B C,
    ope.coefficient A B C ≠ 0 →
      Tendsto
        (fun r => rescaledOPECoefficient freedom
          (radialScalingDegree A B C) (couplingExponent A B C)
          (ope.coefficient A B C) r)
        (nhdsWithin 0 (Ioi 0)) (nhds (leadingDistribution A B C))
  /-- At least one genuine OPE coefficient has nonzero running-coupling dependence. -/
  running_dependence_witness :
    ∃ A B C, ope.coefficient A B C ≠ 0 ∧ couplingExponent A B C ≠ 0

end

end YangMills.Renormalization
