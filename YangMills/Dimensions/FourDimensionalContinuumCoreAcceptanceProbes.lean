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

/-- The exact affine target carries the source-compatible named topological-group law. -/
theorem exact_poincare_target_group :
    Nonempty (Minkowski.ProperOrthochronousPoincareTargetGroupData
      EuclideanDimension.four) :=
  ⟨data.poincareTargetGroup⟩

/-- The exact lift group carries a genuine topological covering projection. -/
theorem exact_poincare_topological_cover :
    Nonempty (Minkowski.ProperOrthochronousPoincareDoubleCoverData
      EuclideanDimension.four PoincareLiftGroup) :=
  ⟨data.poincareDoubleCover⟩

/-- The double cover is the exact lift indexing the physical representation, not a disconnected projection. -/
theorem exact_poincare_cover_lift :
    data.poincareDoubleCover.toProperOrthochronousPoincareLiftData = lift :=
  data.poincareDoubleCover_toLift_eq

/-- Consequently, the exact physical cover projection is a local homeomorphism. -/
theorem exact_poincare_cover_localHomeomorph :
    IsLocalHomeomorph data.poincareDoubleCover.projection :=
  data.poincareDoubleCover.projection_isLocalHomeomorph

/-- Every affine transformation has exactly two sheets in the accepted physical cover. -/
theorem exact_poincare_two_sheets
    (target : Minkowski.ProperOrthochronousPoincareTransformation EuclideanDimension.four) :
    Nonempty ((data.poincareDoubleCover.projection ⁻¹' ({target} : Set _)) ≃ Fin 2) :=
  ⟨data.poincareDoubleCover.fiberEquivFinTwo target⟩

/-- The exact double-cover projection is multiplicative for the accepted target law. -/
theorem exact_poincare_projection_mul (first second : PoincareLiftGroup) :
    letI : Group (Minkowski.ProperOrthochronousPoincareTransformation
      EuclideanDimension.four) := data.poincareTargetGroup.group
    data.poincareTargetGroup.projectionMonoidHom data.poincareDoubleCover (first * second) =
      data.poincareTargetGroup.projectionMonoidHom data.poincareDoubleCover first *
        data.poincareTargetGroup.projectionMonoidHom data.poincareDoubleCover second := by
  letI : Group (Minkowski.ProperOrthochronousPoincareTransformation
    EuclideanDimension.four) := data.poincareTargetGroup.group
  exact (data.poincareTargetGroup.projectionMonoidHom
    data.poincareDoubleCover).map_mul first second

/-- The exact projection kernel is the literal complex sign group, with a central nonidentity
negative-sign lift of the affine identity. -/
theorem exact_poincare_complex_sign_kernel :
    Nonempty (Minkowski.properOrthochronousPoincareProjectionKernel
        EuclideanDimension.four data.poincareTargetGroup data.poincareDoubleCover ≃*
      Minkowski.ComplexSign) ∧
      data.poincareDoubleCover.projection
          (Minkowski.negativeProjectionKernelElement EuclideanDimension.four
            data.poincareTargetGroup data.poincareDoubleCover : PoincareLiftGroup) =
        Minkowski.ProperOrthochronousPoincareTransformation.identity
          EuclideanDimension.four ∧
      Minkowski.negativeProjectionKernelElement EuclideanDimension.four
        data.poincareTargetGroup data.poincareDoubleCover ≠ 1 :=
  ⟨⟨Minkowski.projectionKernelMulEquivComplexSign EuclideanDimension.four
      data.poincareTargetGroup data.poincareDoubleCover⟩,
    Minkowski.negativeProjectionKernelElement_mem_kernel EuclideanDimension.four
      data.poincareTargetGroup data.poincareDoubleCover,
    Minkowski.negativeProjectionKernelElement_ne_one EuclideanDimension.four
      data.poincareTargetGroup data.poincareDoubleCover⟩

/-- Relative to any selected physical lift, its exact affine fiber consists precisely of that lift
and its distinct negative-sign partner. -/
theorem exact_poincare_relative_sign_sheets
    {first second : PoincareLiftGroup}
    (projection_eq : data.poincareDoubleCover.projection second =
      data.poincareDoubleCover.projection first) :
    second = first ∨
      second = first * (Minkowski.negativeProjectionKernelElement
        EuclideanDimension.four data.poincareTargetGroup data.poincareDoubleCover :
          PoincareLiftGroup) :=
  Minkowski.eq_or_eq_mul_negativeKernelElement_of_projection_eq
    EuclideanDimension.four data.poincareTargetGroup data.poincareDoubleCover projection_eq

/-- The derived negative sign acts trivially on the exact scalar physical Hilbert representation,
not merely on an unrelated cover-indexed realization. -/
theorem exact_scalar_negative_sign_unitary :
    U.unitary (Minkowski.negativeProjectionKernelElement EuclideanDimension.four
      data.poincareTargetGroup data.poincareDoubleCover : PoincareLiftGroup) =
      LinearIsometryEquiv.refl ℂ H :=
  data.negativePoincareSign_unitary_eq_refl

/-- The exact scalar representation descends to a homomorphism on the named affine Poincaré target. -/
theorem exact_descended_affine_poincare_representation :
    letI : Group (Minkowski.ProperOrthochronousPoincareTransformation
      EuclideanDimension.four) := data.poincareTargetGroup.group
    Nonempty (Minkowski.ProperOrthochronousPoincareTransformation
      EuclideanDimension.four →* (H ≃ₗᵢ[ℂ] H)) :=
  ⟨data.descendedAffinePoincareUnitaryHom⟩

/-- Every exact lift recovers the original physical cover unitary, blocking a cast-chain surrogate. -/
theorem exact_descended_affine_cover_coherence (g : PoincareLiftGroup) :
    data.scalarWightmanDoubleCoverChain.descendedAffineUnitary
        (data.poincareDoubleCover.projection g) = U.unitary g :=
  data.descendedAffinePoincareUnitary_projection g

/-- Pure affine translations are exactly the original translation unitaries tied to the PVM,
stress tensor, and gap. -/
theorem exact_descended_affine_translation_coherence
    (a : EuclideanDimension.Spacetime EuclideanDimension.four) :
    data.scalarWightmanDoubleCoverChain.descendedAffineUnitary
        (Minkowski.ProperOrthochronousPoincareTransformation.pureTranslation
          EuclideanDimension.four a) = U.translationUnitary a :=
  data.descendedAffinePoincareUnitary_pureTranslation a

/-- Direct affine covariance acts on the exact original scalar field and original common domain. -/
theorem exact_descended_affine_scalar_field_covariance
    (p : Minkowski.ProperOrthochronousPoincareTransformation EuclideanDimension.four)
    (f : Minkowski.ScalarMinkowskiSchwartzTestFunction EuclideanDimension.four)
    (ψ : D.domain) :
    data.descendedAffineDomainUnitary p
        (fieldData.field f ((data.descendedAffineDomainUnitary p).symm ψ)) =
      fieldData.field
        (Minkowski.pullbackScalarMinkowskiSchwartzTestFunction
          EuclideanDimension.four p f) ψ :=
  data.scalarField_covariant_descendedAffine p f ψ

/-- Every explicitly designated scalar label of the exact original local-observable family—not a
transported copy—has direct affine covariance. -/
theorem exact_descended_affine_observable_covariance
    (A : data.observableFamily.Label)
    (hA : A ∈ data.covariantObservableFamily.scalarLabel)
    (p : Minkowski.ProperOrthochronousPoincareTransformation EuclideanDimension.four)
    (f : Minkowski.ScalarMinkowskiSchwartzTestFunction EuclideanDimension.four)
    (ψ : D.domain) :
    data.descendedAffineDomainUnitary p
        (data.observableFamily.operator A f
          ((data.descendedAffineDomainUnitary p).symm ψ)) =
      data.observableFamily.operator A
        (Minkowski.pullbackScalarMinkowskiSchwartzTestFunction
          EuclideanDimension.four p f) ψ :=
  data.localObservable_covariant_descendedAffine A hA p f ψ

/-- The descended physical affine action remains strongly continuous on every Hilbert vector. -/
theorem exact_descended_affine_poincare_strong_continuity (ψ : H) :
    Continuous (fun p : Minkowski.ProperOrthochronousPoincareTransformation
      EuclideanDimension.four =>
      data.scalarWightmanDoubleCoverChain.descendedAffineUnitary p ψ) :=
  data.descendedAffinePoincareUnitary_stronglyContinuous ψ

/-- The preliminary ultraviolet normal form uses that exact gauge-group certificate and dimension. -/
theorem exact_asymptotic_freedom :
    Nonempty (Renormalization.PureYangMillsAsymptoticFreedomData
      EuclideanDimension.four data.compactSimpleGaugeGroup) :=
  ⟨data.asymptoticFreedom⟩

/-- Its one-loop coefficient uses the exact invariant pairing and exact gauge Lie algebra. -/
theorem exact_group_normalized_oneLoop_beta :
    Nonempty (Renormalization.GroupNormalizedOneLoopBetaData
      inner data.asymptoticFreedom) :=
  ⟨data.groupNormalizedOneLoopBeta⟩

/-- The accepted leading coefficient is the exact positive adjoint-Casimir value. -/
theorem exact_group_normalized_leadingCoefficient :
    data.asymptoticFreedom.leadingCoefficient =
      (11 * data.groupNormalizedOneLoopBeta.casimirNormalization.adjointCasimir) /
        (3 * (16 * Real.pi ^ 2)) :=
  data.groupNormalizedOneLoopBeta.leadingCoefficient_eq

/-- The outer classical-action coupling is one exact value of that same running coupling. -/
theorem exact_classical_running_coupling_reference :
    data.asymptoticFreedom.ultravioletThreshold <
        data.classicalRunningCouplingReference.referenceLogScale ∧
      data.classicalAction.coupling = data.asymptoticFreedom.runningCoupling
        data.classicalRunningCouplingReference.referenceLogScale :=
  ⟨data.classicalRunningCouplingReference.reference_mem_ultraviolet,
    data.classicalRunningCouplingReference.coupling_eq_runningCoupling⟩

/-- An unrelated replacement for the exact classical coupling cannot satisfy this same bridge. -/
theorem disconnected_classical_coupling_blocked
    (replacement : ℝ)
    (replacement_eq_running : replacement = data.asymptoticFreedom.runningCoupling
      data.classicalRunningCouplingReference.referenceLogScale) :
    replacement = data.classicalAction.coupling :=
  data.classicalRunningCouplingReference.replacement_eq replacement_eq_running

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

/-- Corrected reconstruction acceptance is tied to the exact Euclidean family, selected Wightman
surface, and full correlator family of this core. It remains supplied uninhabited data. -/
theorem exact_corrected_osII_reconstruction_acceptance :
    Nonempty (Reconstruction.CorrectedOSIIReconstructionAcceptanceData
      data.schwingerFamily data.wightmanSurface data.fullCorrelators) :=
  ⟨data.correctedOSIIReconstruction⟩

/-- The old strict Wick bridge is derived from the exact source bridge. -/
theorem exact_wick_coherence :
    Nonempty (Reconstruction.MathlibStrictOrderedScalarWickContinuationData
      data.schwingerFamily data.relativeAnalyticCorrelators) :=
  ⟨data.strictWickCoherence⟩

/-- Every exact family label is scalar, an exact stress component, or covered by a residual finite
projected-Lorentz multiplet. -/
theorem exact_all_labels_covariance_classified
    (A : data.observableFamily.Label) :
    A ∈ data.covariantObservableFamily.scalarLabel ∨
      (∃ μ ν, A = data.stressEnergy.componentLabel μ ν) ∨
      A ∈ Minkowski.residualCovariantObservableLabelSet
        data.covariantObservableFamily data.stressEnergy :=
  data.observableCovarianceCoverage.label_scalar_or_stress_or_residual A

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

/-- The first new scalar curvature power `(F²)²` is a distinct nontrivial operator on that same
family, not a duplicate unit or `F²` sector. -/
theorem exact_curvature_quartic_observable :
    data.curvaturePowerInterpretation.quantumLabel .curvatureQuartic ≠
        data.observableFamily.unitLabel ∧
      data.curvaturePowerInterpretation.quantumLabel .curvatureQuartic ≠
        data.curvatureSquaredInterpretation.quantumLabel .curvatureSquared ∧
      ∃ (test : Minkowski.ScalarMinkowskiSchwartzTestFunction EuclideanDimension.four)
        (vector : D.domain),
        data.observableFamily.operator
            (data.curvaturePowerInterpretation.quantumLabel .curvatureQuartic) test vector ≠ 0 ∧
        data.observableFamily.operator
            (data.curvaturePowerInterpretation.quantumLabel .curvatureQuartic) test vector ≠
          data.observableFamily.operator data.observableFamily.unitLabel test vector ∧
        data.observableFamily.operator
            (data.curvaturePowerInterpretation.quantumLabel .curvatureQuartic) test vector ≠
          data.observableFamily.operator
            (data.curvatureSquaredInterpretation.quantumLabel .curvatureSquared) test vector :=
  ⟨data.curvatureQuarticAntiCollapse.curvatureQuarticLabel_ne_unit,
    data.curvatureQuarticAntiCollapse.curvatureQuarticLabel_ne_curvatureSquared,
    data.curvatureQuarticAntiCollapse.curvatureQuartic_nontrivial⟩

/-- The interpreted scalar curvature labels, unlike tensor component labels, are explicitly in the
scalar-covariant sector. -/
theorem exact_curvature_scalar_covariance_sector :
    data.curvatureSquaredInterpretation.quantumLabel .curvatureSquared ∈
        data.covariantObservableFamily.scalarLabel ∧
      data.curvaturePowerInterpretation.quantumLabel .curvatureQuartic ∈
        data.covariantObservableFamily.scalarLabel :=
  ⟨data.curvatureSquaredLabel_mem_scalar, data.curvatureQuarticLabel_mem_scalar⟩

/-- Every natural power has the exact canonical classical carrier and same-family label. -/
theorem exact_curvature_all_powers
    (n : ℕ) (b : FourDimensionalEuclideanBase) :
    data.curvatureAllPowersInterpretation.classicalObservable n b =
        (Classical.canonicalEuclideanSpacetimeMetricData EuclideanDimension.four).canonicalCurvatureDensity
          inner connection exterior curvatureCertificate b ^ n ∧
      data.curvatureAllPowersInterpretation.quantumLabel n ∈
        data.covariantObservableFamily.scalarLabel :=
  ⟨data.curvatureAllPowersInterpretation.classicalObservable_apply n b,
    data.curvatureAllPowersLabel_mem_scalar n⟩

/-- Restriction to exponents zero, one, and two recovers the exact existing finite interpretation. -/
theorem exact_curvature_all_powers_finite_restriction :
    data.curvatureAllPowersInterpretation.finiteRestriction =
      data.curvaturePowerInterpretation :=
  data.curvatureAllPowersInterpretation.finiteRestriction_eq

/-- The stress tensor belongs to the exact same local-observable family. -/
theorem exact_stress_energy :
    Nonempty (Minkowski.LocalStressEnergyTensorData data.observableFamily) :=
  ⟨data.stressEnergy⟩

/-- Trace-anomaly normalization is indexed by the core's exact group-normalized beta and exact
classical running-coupling reference. -/
theorem exact_trace_anomaly_normalization :
    Nonempty (Renormalization.StressTensorTraceAnomalyNormalizationData
      data.groupNormalizedOneLoopBeta data.classicalRunningCouplingReference) :=
  ⟨data.traceAnomalyNormalization⟩

/-- The accepted physical reduction selects an admissible on-shell/nonzero-momentum triple that
detects the exact existing `F²` label. -/
theorem exact_trace_anomaly_physical_selection :
    Nonempty (Renormalization.PhysicalReducedTraceMatrixElementSelectionData
      data.curvatureSquaredInterpretation) :=
  ⟨data.traceAnomalyPhysicalSelection⟩

/-- The core's trace anomaly is tied to its exact interpretation, stress, normalization, and
physical selection rather than disconnected replacements. -/
theorem exact_stress_trace_anomaly :
    Nonempty (Renormalization.StressTensorTraceAnomalyData
      data.curvatureSquaredInterpretation data.stressEnergy data.traceAnomalyNormalization
        data.traceAnomalyPhysicalSelection) :=
  ⟨data.stressTraceAnomaly⟩

/-- The selected reduced `F²` matrix element and nonzero normalization prevent a globally zero
mostly-minus trace carrier. -/
theorem exact_nonzero_stress_trace :
    ∃ (f : Minkowski.ScalarMinkowskiSchwartzTestFunction EuclideanDimension.four)
      (φ : D.domain),
      Minkowski.stressTensorTraceOperator data.stressEnergy f φ ≠ 0 :=
  data.stressTraceAnomaly.traceOperator_nontrivial

/-- A disconnected trace-anomaly normalization cannot replace the exact core field. -/
theorem disconnected_trace_anomaly_normalization_blocked
    (wrong : Renormalization.StressTensorTraceAnomalyNormalizationData
      data.groupNormalizedOneLoopBeta data.classicalRunningCouplingReference)
    (different : wrong ≠ data.traceAnomalyNormalization)
    (claimed : wrong = data.traceAnomalyNormalization) : False :=
  different claimed

/-- Every stress component is excluded from the scalar-covariant sector. -/
theorem exact_scalar_stress_covariance_separation
    (μ ν : EuclideanDimension.four.CoordinateIndex) :
    data.stressEnergy.componentLabel μ ν ∉
      data.covariantObservableFamily.scalarLabel :=
  data.stressCovarianceSeparation.componentLabel_not_mem_scalar μ ν

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

/-- Every exact observable label is fixed by the same designated canonical smooth-gauge action. -/
theorem exact_quantum_gauge_all_labels
    (g : Geometry.SmoothGaugeTransformation smoothBundle)
    (A : data.observableFamily.Label)
    (f : Minkowski.ScalarMinkowskiSchwartzTestFunction EuclideanDimension.four) :
    data.quantumGaugeAction.operatorAction g A f = data.observableFamily.operator A f :=
  data.quantumGauge_operator_invariant g A f

/-- The exact interpreted finite fragment is connected to that same action. -/
theorem exact_quantum_gauge_curvature_fragment
    (g : Geometry.SmoothGaugeTransformation smoothBundle)
    (tag : Observables.ScalarCurvaturePowerTag)
    (f : Minkowski.ScalarMinkowskiSchwartzTestFunction EuclideanDimension.four) :
    data.quantumGaugeAction.operatorAction g
        (data.curvaturePowerInterpretation.quantumLabel tag) f =
      data.observableFamily.operator (data.curvaturePowerInterpretation.quantumLabel tag) f :=
  data.quantumGauge_curvaturePower_invariant g tag f

/-- Every natural-power label is fixed by the same designated action. -/
theorem exact_quantum_gauge_curvature_all_powers
    (g : Geometry.SmoothGaugeTransformation smoothBundle)
    (n : ℕ)
    (f : Minkowski.ScalarMinkowskiSchwartzTestFunction EuclideanDimension.four) :
    data.quantumGaugeAction.operatorAction g
        (data.curvatureAllPowersInterpretation.quantumLabel n) f =
      data.observableFamily.operator
        (data.curvatureAllPowersInterpretation.quantumLabel n) f :=
  data.quantumGauge_curvatureAllPowers_invariant g n f

/-- Changing an operator under the exact designated action contradicts core acceptance. -/
theorem changed_quantum_gauge_operator_blocked
    (g : Geometry.SmoothGaugeTransformation smoothBundle)
    (A : data.observableFamily.Label)
    (f : Minkowski.ScalarMinkowskiSchwartzTestFunction EuclideanDimension.four)
    (changed : data.quantumGaugeAction.operatorAction g A f ≠
      data.observableFamily.operator A f) : False :=
  changed (data.quantumGauge_operator_invariant g A f)

/-- A disconnected local family cannot replace the family coherently containing the Wightman field. -/
theorem disconnected_observable_family_blocked
    (wrong : Minkowski.TemperedLocalObservableFamilyData.{uLift, uH, uLabel} D)
    (different : wrong ≠ data.observableFamily)
    (claimed : wrong = data.observableFamily) : False :=
  different claimed

end

end YangMills.Dimensions.FourDimensionalContinuumCoreAcceptance.Probes
