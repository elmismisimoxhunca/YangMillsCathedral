import YangMills.Renormalization.AsymptoticFreedomOPE

/-! Hostile probes for exact OPE scaling, nonzero limits, running dependence, and scope. -/

namespace YangMills.Renormalization.AsymptoticFreedomOPE.Probes

open Filter Set Topology
open scoped Manifold ContDiff

noncomputable section

variable {d : EuclideanDimension} {Gauge GaugeModel : Type*}
  [NormedAddCommGroup GaugeModel] [NormedSpace ℝ GaugeModel] [FiniteDimensional ℝ GaugeModel]
  [Group Gauge] [TopologicalSpace Gauge] [T2Space Gauge] [SecondCountableTopology Gauge]
  [ChartedSpace GaugeModel Gauge] [LieGroup (modelWithCornersSelf ℝ GaugeModel) ∞ Gauge]
  {gaugeGroup : Geometry.CompactSimpleGaugeGroupData Gauge GaugeModel}
  {freedom : PureYangMillsAsymptoticFreedomData d gaugeGroup}
  {PoincareGroup : Type*} [Group PoincareGroup] [TopologicalSpace PoincareGroup]
  [IsTopologicalGroup PoincareGroup]
  {lift : Minkowski.ProperOrthochronousPoincareLiftData d PoincareGroup}
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H]
  {U : Minkowski.StronglyContinuousUnitaryPoincareRepresentation lift H}
  {vacuumData : Minkowski.PoincareInvariantVacuumData U}
  {D : Minkowski.CommonInvariantDomainData vacuumData}
  {family : Minkowski.TemperedLocalObservableFamilyData D} [DecidableEq family.Label]
  {products : Minkowski.WeakTemperedBilocalObservableProductData family}
  {ope : Minkowski.WeakOperatorProductExpansionData products}

/-- Short distance eventually enters the exact open ultraviolet tail, where the same running
coupling is positive. -/
theorem exact_eventual_ultraviolet_tail :
    ∀ᶠ r in nhdsWithin 0 (Ioi 0),
      freedom.ultravioletThreshold < shortDistanceLogScale r ∧
        0 < freedom.runningCoupling (shortDistanceLogScale r) := by
  filter_upwards [eventually_shortDistanceLogScale_gt freedom.ultravioletThreshold] with r hr
  exact ⟨hr, freedom.runningCoupling_pos _ hr⟩

/-- Rescaling exposes the exact radial/running factor and normalized test dilation. -/
theorem exact_rescaled_value (degree exponent : ℝ)
    (coefficient : TemperedDistribution (Minkowski.BilocalRelativeConfiguration d) ℂ)
    (r : ℝ) (test : Minkowski.ScalarMinkowskiSchwartzTestFunction d) :
    rescaledOPECoefficient freedom degree exponent coefficient r test =
      ((Real.rpow r degree : ℂ) *
        (Real.rpow (freedom.runningCoupling (shortDistanceLogScale r)) exponent : ℂ)⁻¹) *
        coefficient (normalizedRelativeSchwartzDilationCLM d r test) :=
  rescaledOPECoefficient_apply freedom degree exponent coefficient r test

/-- Every nonzero exact coefficient has its nonzero leading distribution and weak scaling limit. -/
theorem exact_nonzero_coefficient_scaling
    (data : SuppliedWeakOPERegularVariationData freedom ope)
    (A B C : family.Label) (h : ope.coefficient A B C ≠ 0) :
    data.leadingDistribution A B C ≠ 0 ∧
      Tendsto (fun r => rescaledOPECoefficient freedom (data.radialScalingDegree A B C)
        (data.couplingExponent A B C) (ope.coefficient A B C) r)
        (nhdsWithin 0 (Ioi 0)) (nhds (data.leadingDistribution A B C)) :=
  ⟨data.leadingDistribution_nonzero A B C h, data.coefficient_scaling A B C h⟩

/-- Some nonzero coefficient genuinely depends on the same running coupling. -/
theorem exact_running_witness
    (data : SuppliedWeakOPERegularVariationData freedom ope) :
    ∃ A B C, ope.coefficient A B C ≠ 0 ∧ data.couplingExponent A B C ≠ 0 :=
  data.running_dependence_witness

/-- The bridge inherits the explicit four-dimensional scope. -/
theorem exact_four_dimensional_scope
    (_data : SuppliedWeakOPERegularVariationData freedom ope) :
    d = EuclideanDimension.four :=
  freedom.dimension_eq_four

/-- A zero leading distribution cannot be assigned to a nonzero coefficient. -/
theorem zero_leading_distribution_blocked
    (data : SuppliedWeakOPERegularVariationData freedom ope)
    (A B C : family.Label) (h : ope.coefficient A B C ≠ 0) :
    data.leadingDistribution A B C ≠ 0 :=
  data.leadingDistribution_nonzero A B C h

/-- Replacing the exact leading distribution by a disconnected unequal limit is impossible. -/
theorem disconnected_limit_blocked
    (data : SuppliedWeakOPERegularVariationData freedom ope)
    (A B C : family.Label) (h : ope.coefficient A B C ≠ 0)
    (replacement : TemperedDistribution (Minkowski.BilocalRelativeConfiguration d) ℂ)
    (hne : replacement ≠ data.leadingDistribution A B C) :
    ¬ Tendsto (fun r => rescaledOPECoefficient freedom (data.radialScalingDegree A B C)
      (data.couplingExponent A B C) (ope.coefficient A B C) r)
      (nhdsWithin 0 (Ioi 0)) (nhds replacement) := by
  intro replacementLimit
  apply hne
  exact tendsto_nhds_unique replacementLimit (data.coefficient_scaling A B C h)

/-- Constructor-surface probe: arbitrary signed degrees construct the acceptance record without any
nonnegativity premise. Adding such a premise to the structure breaks this probe. -/
def signed_degree_constructor_surface
    (degree exponent : family.Label → family.Label → family.Label → ℝ)
    (leading : family.Label → family.Label → family.Label →
      TemperedDistribution (Minkowski.BilocalRelativeConfiguration d) ℂ)
    (leadingNonzero : ∀ A B C, ope.coefficient A B C ≠ 0 → leading A B C ≠ 0)
    (scaling : ∀ A B C, ope.coefficient A B C ≠ 0 →
      Tendsto (fun r => rescaledOPECoefficient freedom (degree A B C)
        (exponent A B C) (ope.coefficient A B C) r)
        (nhdsWithin 0 (Ioi 0)) (nhds (leading A B C)))
    (running : ∃ A B C, ope.coefficient A B C ≠ 0 ∧ exponent A B C ≠ 0) :
    SuppliedWeakOPERegularVariationData freedom ope where
  radialScalingDegree := degree
  couplingExponent := exponent
  leadingDistribution := leading
  leadingDistribution_nonzero := leadingNonzero
  coefficient_scaling := scaling
  running_dependence_witness := running

/-- A supplied genuinely regular/vanishing negative degree remains visibly signed. -/
theorem negative_regular_degree_preserved
    (data : SuppliedWeakOPERegularVariationData freedom ope)
    (A B C : family.Label) (negative : data.radialScalingDegree A B C < 0) :
    ¬ 0 ≤ data.radialScalingDegree A B C :=
  not_le_of_gt negative

/-- Declaring every coupling exponent zero contradicts the running-dependence witness. -/
theorem all_zero_coupling_exponents_blocked
    (data : SuppliedWeakOPERegularVariationData freedom ope)
    (allZero : ∀ A B C, data.couplingExponent A B C = 0) : False := by
  obtain ⟨A, B, C, -, nonzeroExponent⟩ := data.running_dependence_witness
  exact nonzeroExponent (allZero A B C)

end

end YangMills.Renormalization.AsymptoticFreedomOPE.Probes
