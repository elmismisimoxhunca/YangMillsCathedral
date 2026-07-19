/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Dimensions.ThreeDimensionalContinuumCoreAcceptance

/-! Hostile projections from the uninhabited three-dimensional current-strength continuum core. -/

namespace YangMills.Dimensions.ThreeDimensionalContinuumCoreAcceptance.Probes

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
      ThreeDimensionalEuclideanBase P}
    {bundle : Geometry.TopologicalPrincipalBundleData torsor}
    {smoothBundle : Geometry.SmoothPrincipalBundleData threeDimensionalEuclideanModel
      (modelWithCornersSelf ℝ EG) IP torsor bundle}
    {PoincareLiftGroup : Type uLift} [Group PoincareLiftGroup]
    [TopologicalSpace PoincareLiftGroup] [IsTopologicalGroup PoincareLiftGroup]
    {lift : Minkowski.ProperOrthochronousPoincareLiftData
      EuclideanDimension.three PoincareLiftGroup}
    {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H]
    {U : Minkowski.StronglyContinuousUnitaryPoincareRepresentation lift H}
    {vacuumData : Minkowski.PoincareInvariantVacuumData U}
    {D : Minkowski.CommonInvariantDomainData vacuumData}
    {fieldData : Minkowski.ScalarWightmanFieldOnCommonDomainData D}
    {geometry : Classical.EuclideanMetricData
      (IB := threeDimensionalEuclideanModel) (B := ThreeDimensionalEuclideanBase)}
    {inner : Geometry.InvariantInnerProductData
      (I := modelWithCornersSelf ℝ EG) (G := GaugeGroup)}
    {connection : Geometry.PrincipalConnectionData smoothBundle}
    {exterior : Geometry.PrincipalConnectionExteriorDerivativeData connection}
    {curvatureCertificate : Geometry.PrincipalCurvatureStructureCertificate
      smoothBundle connection exterior}
    (data : ThreeDimensionalCurrentStrengthContinuumCoreAcceptanceData.{uEG, uEP, uHP,
      uGauge, uP, uLift, uH, uLabel}
      geometry inner connection exterior curvatureCertificate fieldData)

include data

/-- The contract is hard-wired to three-dimensional spacetime and a two-dimensional spatial slice. -/
theorem exact_dimension :
    EuclideanDimension.three.value = 3 ∧
      EuclideanDimension.three.spatialDimension = 2 :=
  ThreeDimensionalCurrentStrengthContinuumCoreAcceptanceData.exact_dimension data

omit data in
/-- None of the lower consistency dimensions or the Clay endpoint equals this index. -/
theorem distinct_dimension_indices :
    EuclideanDimension.three ≠ EuclideanDimension.one ∧
      EuclideanDimension.three ≠ EuclideanDimension.two ∧
      EuclideanDimension.three ≠ EuclideanDimension.four := by
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
  ThreeDimensionalCurrentStrengthContinuumCoreAcceptanceData.compactSimpleGaugeGroup data

/-- The exact classical coordinate base uses coordinate Lebesgue measure, not an arbitrary measure. -/
theorem exact_classical_coordinate_measure :
    data.classicalAction.measure = MeasureTheory.volume :=
  data.classicalMeasure_eq_coordinateLebesgue

/-- The strict Euclidean family is exactly three-dimensional. -/
theorem exact_euclidean_candidate :
    Nonempty (MathlibStrictScalarEuclideanCandidate
      data.schwingerFamily data.spatialDirection) :=
  ⟨data.strictEuclideanCandidate⟩

/-- The Wightman surface uses the exact supplied three-dimensional field chain. -/
theorem exact_wightman_surface :
    Nonempty (Minkowski.ScalarWightmanAxiomSurfaceData fieldData) :=
  ⟨data.wightmanSurface⟩

/-- The strict Wick bridge connects the exact Euclidean family to the exact analytic correlators. -/
theorem exact_wick_coherence :
    Nonempty (Reconstruction.MathlibStrictOrderedScalarWickContinuationData
      data.schwingerFamily data.relativeAnalyticCorrelators) :=
  ⟨data.strictWickCoherence⟩

/-- The Wightman field is an exact nontrivial operator in the same local-observable family. -/
theorem exact_nontrivial_wightman_observable :
    ∃ (test : Minkowski.ScalarMinkowskiSchwartzTestFunction EuclideanDimension.three)
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
    ∃ (test : Minkowski.ScalarMinkowskiSchwartzTestFunction EuclideanDimension.three)
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

end YangMills.Dimensions.ThreeDimensionalContinuumCoreAcceptance.Probes
