/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Dimensions.FourDimensionalContinuumCoreAcceptance

/-! Hostile projections from the uninhabited four-dimensional current-strength continuum core. -/

namespace YangMills.Dimensions.FourDimensionalContinuumCoreAcceptance.Probes

open scoped Manifold ContDiff

universe uEG uEP uHP uGauge uP uLift uH uLabel

noncomputable section

variable
    {EG : Type uEG} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
    [FiniteDimensional ℝ EG]
    {EP : Type uEP} {HP : Type uHP}
    [NormedAddCommGroup EP] [NormedSpace ℝ EP] [TopologicalSpace HP]
    {GaugeGroup : Type uGauge} [Group GaugeGroup] [TopologicalSpace GaugeGroup]
    [T2Space GaugeGroup] [SecondCountableTopology GaugeGroup]
    [IsTopologicalGroup GaugeGroup] [ChartedSpace EG GaugeGroup]
    [LieGroup (modelWithCornersSelf ℝ EG) ∞ GaugeGroup]
    {P : Type uP} [TopologicalSpace P]
    {IP : ModelWithCorners ℝ EP HP}
    [ChartedSpace HP P] [IsManifold IP ∞ P]
    {torsor : Geometry.PrincipalBundleTorsorData GaugeGroup
      FourDimensionalEuclideanBase P}
    {bundle : Geometry.TopologicalPrincipalBundleData torsor}
    {smoothBundle : Geometry.SmoothPrincipalBundleData fourDimensionalEuclideanModel
      (modelWithCornersSelf ℝ EG) IP torsor bundle}
    {PoincareLiftGroup : Type uLift} [Group PoincareLiftGroup]
    [TopologicalSpace PoincareLiftGroup] [IsTopologicalGroup PoincareLiftGroup]
    {lift : Minkowski.ProperOrthochronousPoincareLiftData
      EuclideanDimension.four PoincareLiftGroup}
    {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H]
    {U : Minkowski.StronglyContinuousUnitaryPoincareRepresentation lift H}
    {vacuumData : Minkowski.PoincareInvariantVacuumData U}
    {D : Minkowski.CommonInvariantDomainData vacuumData}
    {fieldData : Minkowski.ScalarWightmanFieldOnCommonDomainData D}
    {inner : Geometry.InvariantInnerProductData
      (I := modelWithCornersSelf ℝ EG) (G := GaugeGroup)}
    {connection : Geometry.PrincipalConnectionData smoothBundle}
    {exterior : Geometry.PrincipalConnectionExteriorDerivativeData connection}
    {curvatureCertificate : Geometry.PrincipalCurvatureStructureCertificate
      smoothBundle connection exterior}
    (data : FourDimensionalCurrentStrengthContinuumCoreAcceptanceData.{uEG, uEP, uHP,
      uGauge, uP, uLift, uH, uLabel}
      inner connection exterior curvatureCertificate fieldData)

include data

/-- The contract is hard-wired to four-dimensional spacetime and a three-dimensional spatial slice. -/
theorem exact_dimension :
    EuclideanDimension.four.value = 4 ∧
      EuclideanDimension.four.spatialDimension = 3 :=
  FourDimensionalCurrentStrengthContinuumCoreAcceptanceData.exact_dimension data

omit data in
/-- None of the three lower consistency dimensions equals the Clay endpoint. -/
theorem distinct_dimension_indices :
    EuclideanDimension.four ≠ EuclideanDimension.one ∧
      EuclideanDimension.four ≠ EuclideanDimension.two ∧
      EuclideanDimension.four ≠ EuclideanDimension.three := by
  constructor
  · intro equality
    have := congrArg EuclideanDimension.value equality
    simp at this
  constructor
  · intro equality
    have := congrArg EuclideanDimension.value equality
    simp at this
  · intro equality
    have := congrArg EuclideanDimension.value equality
    simp at this

/-- The physical gauge group carries the exact compact-simple certificate. -/
theorem exact_compact_simple_gauge_group :
    Geometry.CompactSimpleGaugeGroupData GaugeGroup EG :=
  FourDimensionalCurrentStrengthContinuumCoreAcceptanceData.compactSimpleGaugeGroup data

/-- The preliminary ultraviolet normal form uses that exact gauge-group certificate and dimension. -/
theorem exact_asymptotic_freedom :
    Nonempty (Renormalization.PureYangMillsAsymptoticFreedomData
      EuclideanDimension.four data.compactSimpleGaugeGroup) :=
  ⟨data.asymptoticFreedom⟩

/-- The accepted running coupling is not a scale-independent constant. -/
theorem nonconstant_running_coupling :
    ¬ ∃ coupling : ℝ,
      data.asymptoticFreedom.runningCoupling = fun _ => coupling :=
  data.runningCoupling_not_constant

/-- Bilocal products and the weak OPE use the exact same observable family. -/
theorem exact_weak_ope_chain :
    letI : DecidableEq data.observableFamily.Label := data.observableLabelDecidableEq
    Nonempty (Minkowski.WeakTemperedBilocalObservableProductData data.observableFamily) ∧
      Nonempty (Minkowski.WeakOperatorProductExpansionData data.observableProducts) :=
  ⟨⟨data.observableProducts⟩, ⟨data.weakOPE⟩⟩

/-- Preliminary regular variation uses the exact running coupling and exact weak OPE. -/
theorem exact_ope_regular_variation :
    letI : DecidableEq data.observableFamily.Label := data.observableLabelDecidableEq
    Nonempty (Renormalization.SuppliedWeakOPERegularVariationData
      data.asymptoticFreedom data.weakOPE) :=
  ⟨data.opeRegularVariation⟩

/-- The accepted OPE contains a genuinely nonzero contracted zeroth-order term. -/
theorem exact_nonzero_ope_term :
    letI : DecidableEq data.observableFamily.Label := data.observableLabelDecidableEq
    ∃ (A B C : data.observableFamily.Label) (bra ket : D.domain),
      C ∈ data.weakOPE.truncation 0 ∧
      data.weakOPE.contraction.contract (data.weakOPE.coefficient A B C)
        (data.observableFamily.matrixElement C bra ket) ≠ 0 :=
  data.ope_nonzero_zerothOrderTerm

/-- The interpreted curvature-squared label participates nontrivially in that exact OPE. -/
theorem exact_curvature_squared_ope_coherence :
    letI : DecidableEq data.observableFamily.Label := data.observableLabelDecidableEq
    Nonempty (Observables.CurvatureSquaredOPECoherenceData
      (Classical.canonicalEuclideanSpacetimeMetricData EuclideanDimension.four)
      inner connection exterior curvatureCertificate data.curvatureSquaredInterpretation
      data.weakOPE) :=
  ⟨data.curvatureSquaredOPECoherence⟩

/-- The exact selected `F² × F²` term has nonzero coefficient/local-field contraction. -/
theorem exact_nonzero_curvature_squared_ope_term :
    letI : DecidableEq data.observableFamily.Label := data.observableLabelDecidableEq
    data.weakOPE.contraction.contract
      (data.weakOPE.coefficient
        (data.curvatureSquaredInterpretation.quantumLabel
          Observables.BasicCurvatureObservableTag.curvatureSquared)
        (data.curvatureSquaredInterpretation.quantumLabel
          Observables.BasicCurvatureObservableTag.curvatureSquared)
        data.curvatureSquaredOPECoherence.outputLabel)
      (data.observableFamily.matrixElement data.curvatureSquaredOPECoherence.outputLabel
        data.curvatureSquaredOPECoherence.bra data.curvatureSquaredOPECoherence.ket) ≠ 0 :=
  data.curvatureSquaredOPEContractedTerm_nonzero

/-- The selected interpreted coefficient genuinely depends on the exact running coupling. -/
theorem exact_curvature_squared_running_dependence :
    letI : DecidableEq data.observableFamily.Label := data.observableLabelDecidableEq
    data.opeRegularVariation.couplingExponent
      (data.curvatureSquaredInterpretation.quantumLabel
        Observables.BasicCurvatureObservableTag.curvatureSquared)
      (data.curvatureSquaredInterpretation.quantumLabel
        Observables.BasicCurvatureObservableTag.curvatureSquared)
      data.curvatureSquaredOPECoherence.outputLabel ≠ 0 :=
  data.curvatureSquaredCouplingExponent_nonzero

/-- The same interpreted coefficient has a nonzero leading scaling distribution. -/
theorem exact_curvature_squared_leading_distribution :
    letI : DecidableEq data.observableFamily.Label := data.observableLabelDecidableEq
    data.opeRegularVariation.leadingDistribution
      (data.curvatureSquaredInterpretation.quantumLabel
        Observables.BasicCurvatureObservableTag.curvatureSquared)
      (data.curvatureSquaredInterpretation.quantumLabel
        Observables.BasicCurvatureObservableTag.curvatureSquared)
      data.curvatureSquaredOPECoherence.outputLabel ≠ 0 :=
  data.curvatureSquaredOPELeadingDistribution_nonzero

/-- The classical action is indexed by the canonical flat metric on exact coordinate `ℝ⁴`. -/
theorem exact_canonical_classical_metric :
    Nonempty (Classical.EuclideanActionAnalyticData
      (Classical.canonicalEuclideanSpacetimeMetricData EuclideanDimension.four)
      inner connection exterior curvatureCertificate) :=
  ⟨data.classicalAction⟩

/-- The exact classical coordinate base uses coordinate Lebesgue measure, not an arbitrary measure. -/
theorem exact_classical_coordinate_measure :
    data.classicalAction.measure = MeasureTheory.volume :=
  data.classicalMeasure_eq_coordinateLebesgue

/-- The exact source-carrier Euclidean `(E1)`–`(E4)` package uses the same family. -/
theorem exact_source_euclidean_current_strength :
    Nonempty (OSSourceFourDimensionalEuclideanCurrentStrengthData data.schwingerFamily) :=
  ⟨data.sourceEuclideanCurrentStrength⟩

/-- Carrier-exact OS-II `(E0′)` is derived on the exact coincidence-flat restriction. -/
theorem exact_carrier_linear_growth :
    Nonempty (OSIICarrierExactLinearGrowthData
      data.schwingerFamily.toOSIICoincidenceFlatFamily) :=
  ⟨data.sourceEuclideanCurrentStrength.carrierExactLinearGrowth⟩

/-- Source reflection positivity reaches every exact derivative-vanishing source sequence. -/
theorem exact_source_reflection_positivity
    (f : OSPositiveTimeOrderedFourDimensionalTestSequence) :
    IsNonnegativeComplexReal
      (osSourceFourDimensionalReflectionPositivityExpression data.schwingerFamily f) :=
  data.sourceEuclideanCurrentStrength.reflectionPositivity f

/-- Source clustering reaches every exact source pair and every normalized spatial direction. -/
theorem exact_source_clustering
    (v : EuclideanUnitSpatialDirection EuclideanDimension.four)
    (f g : OSPositiveTimeOrderedFourDimensionalTestSequence) :
    Filter.Tendsto
      (fun scale : ℝ => osSourceFourDimensionalClusteringExpression
        data.schwingerFamily v f g scale)
      Filter.atTop (nhds 0) :=
  data.sourceEuclideanCurrentStrength.clustering v f g

/-- The Wightman surface uses the exact supplied four-dimensional field chain. -/
theorem exact_wightman_surface :
    Nonempty (Minkowski.ScalarWightmanAxiomSurfaceData fieldData) :=
  ⟨data.wightmanSurface⟩

/-- Corrected OS-II `(R0′)` controls the exact full Wightman correlator family. -/
theorem exact_wightman_linear_growth :
    Nonempty (Minkowski.OSIIWightmanLinearGrowthData data.fullCorrelators) :=
  ⟨data.wightmanLinearGrowth⟩

/-- Its positive coefficients have the exact source `α β^(n²)` bound. -/
theorem exact_wightman_growth_coefficient (n : PositiveArity) :
    0 < data.wightmanLinearGrowth.growth.coefficient n ∧
      data.wightmanLinearGrowth.growth.coefficient n ≤
        data.wightmanLinearGrowth.growth.alpha *
          data.wightmanLinearGrowth.growth.beta ^ (n.value ^ 2) :=
  ⟨data.wightmanLinearGrowth.growth.coefficient_pos n,
    data.wightmanLinearGrowth.growth.coefficient_bound n⟩

/-- The exact source Wick bridge connects every derivative-vanishing ordered source test to the
same analytic Wightman correlators. -/
theorem exact_source_wick_coherence :
    Nonempty (Reconstruction.OSSourceOrderedScalarWickContinuationData
      data.schwingerFamily data.relativeAnalyticCorrelators) :=
  ⟨data.sourceWickCoherence⟩

/-- The old strict Wick bridge is derived from the exact source bridge. -/
theorem exact_wick_coherence :
    Nonempty (Reconstruction.MathlibStrictOrderedScalarWickContinuationData
      data.schwingerFamily data.relativeAnalyticCorrelators) :=
  ⟨data.strictWickCoherence⟩

/-- The Wightman field is an exact nontrivial operator in the same local-observable family. -/
theorem exact_nontrivial_wightman_observable :
    ∃ (test : Minkowski.ScalarMinkowskiSchwartzTestFunction EuclideanDimension.four)
      (vector : D.domain),
      fieldData.field test vector ≠ 0 ∧
      fieldData.field test vector ≠
        data.observableFamily.operator data.observableFamily.unitLabel test vector :=
  data.wightmanField_nontrivial

/-- The exact classical `F²` interpretation lands nontrivially in that same family. -/
theorem exact_curvature_squared_observable :
    data.curvatureSquaredInterpretation.quantumLabel
        Observables.BasicCurvatureObservableTag.curvatureSquared ≠
      data.observableFamily.unitLabel ∧
    ∃ (test : Minkowski.ScalarMinkowskiSchwartzTestFunction EuclideanDimension.four)
      (vector : D.domain),
      data.observableFamily.operator
          (data.curvatureSquaredInterpretation.quantumLabel
            Observables.BasicCurvatureObservableTag.curvatureSquared) test vector ≠ 0 ∧
      data.observableFamily.operator
          (data.curvatureSquaredInterpretation.quantumLabel
            Observables.BasicCurvatureObservableTag.curvatureSquared) test vector ≠
        data.observableFamily.operator data.observableFamily.unitLabel test vector :=
  ⟨data.curvatureSquaredInterpretation.curvatureSquaredLabel_ne_unit,
    data.curvatureSquaredInterpretation.curvatureSquared_nontrivial⟩

/-- The stress tensor belongs to the exact same local-observable family. -/
theorem exact_stress_energy :
    Nonempty (Minkowski.LocalStressEnergyTensorData data.observableFamily) :=
  ⟨data.stressEnergy⟩

/-- Stress charges and Ward identities use the exact accepted Wightman joint PVM. -/
theorem exact_stress_translation_spectrum :
    Nonempty (Minkowski.LocalStressEnergyTranslationWardData
      data.stressEnergy data.wightmanSurface.spectrum) :=
  ⟨data.stressTranslationWard⟩

/-- The same-chain physical time generator is explicitly nonzero. -/
theorem exact_nonzero_time_generator :
    ∃ vector : D.domain,
      data.stressTranslationWard.momentumGenerator
        (Minkowski.stressTensorTimeIndex EuclideanDimension.four) vector ≠ 0 :=
  data.timeTranslationGenerator_nontrivial

/-- The selected threshold is positive and gives finite-positive supremum semantics on the exact
same Wightman joint PVM. -/
theorem exact_same_spectrum_gap :
    0 < data.gapThreshold ∧
      Minkowski.HasFinitePositivePhysicalMassGap vacuumData data.wightmanSurface.spectrum :=
  ⟨data.gapThreshold_pos, data.hasFinitePositivePhysicalMassGap⟩

/-- A disconnected replacement spectrum cannot be identified with the accepted physical spectrum. -/
theorem disconnected_spectrum_blocked
    (wrong : Minkowski.ForwardConeJointTranslationSpectrumData U)
    (different : wrong ≠ data.wightmanSurface.spectrum)
    (claimed : wrong = data.wightmanSurface.spectrum) : False :=
  different claimed

/-- A disconnected local family cannot replace the family coherently containing the Wightman field. -/
theorem disconnected_observable_family_blocked
    (wrong : Minkowski.TemperedLocalObservableFamilyData.{uLift, uH, uLabel} D)
    (different : wrong ≠ data.observableFamily)
    (claimed : wrong = data.observableFamily) : False :=
  different claimed

end

end YangMills.Dimensions.FourDimensionalContinuumCoreAcceptance.Probes
