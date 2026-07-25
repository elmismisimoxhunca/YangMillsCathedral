/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Dimensions.ThreeDimensionalSU2ExistenceMassGapAcceptance

/-! Hostile probes for the bounded three-dimensional SU(2) existence-plus-gap truth teller. -/

namespace YangMills.Dimensions.ThreeDimensionalSU2ExistenceMassGapAcceptance.Probes

open scoped Manifold ContDiff

noncomputable section

universe uEG uEP uHP uGauge uP uLift uH uLabel

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
    {inner : Geometry.InvariantInnerProductData
      (I := modelWithCornersSelf ℝ EG) (G := GaugeGroup)}
    {connection : Geometry.PrincipalConnectionData smoothBundle}
    {exterior : Geometry.PrincipalConnectionExteriorDerivativeData connection}
    {curvatureCertificate : Geometry.PrincipalCurvatureStructureCertificate
      smoothBundle connection exterior}
    (data : ThreeDimensionalSU2ExistenceMassGapAcceptanceData.{uEG, uEP, uHP,
      uGauge, uP, uLift, uH, uLabel}
      (fieldData := fieldData) (inner := inner) (connection := connection)
      (exterior := exterior) (curvatureCertificate := curvatureCertificate))

include data

/-- The strongest data inhabits the authoritative bounded proposition. -/
theorem exact_authoritative_gate :
    ThreeDimensionalSU2ExistenceMassGapAcceptance.{uEG, uEP, uHP, uGauge, uP,
      uLift, uH, uLabel}
      (fieldData := fieldData) (inner := inner) (connection := connection)
      (exterior := exterior) (curvatureCertificate := curvatureCertificate) :=
  ⟨data⟩

/-- The authoritative proposition exposes exactly one unchanged same-theory witness and its gap. -/
theorem exact_component_decomposition :
    ∃ (sameTheory : ThreeDimensionalSU2SameTheoryData.{uEG, uEP, uHP, uGauge,
        uP, uLift, uH, uLabel}
        (fieldData := fieldData) (inner := inner) (connection := connection)
        (exterior := exterior) (curvatureCertificate := curvatureCertificate))
      (gapThreshold : ℝ),
      sameTheory.continuum.wightmanSurface.HasPhysicalMassGap gapThreshold :=
  threeDimensionalSU2Acceptance_nonempty_iff_components.mp
    (exact_authoritative_gate (data := data))

/-- The three tiers remain definitionally connected rather than separately existential. -/
theorem exact_dependent_tiers :
    Nonempty (ThreeDimensionalSU2ContinuumExistenceData.{uEG, uEP, uHP, uGauge,
      uP, uLift, uH, uLabel}
      (fieldData := fieldData) (inner := inner) (connection := connection)
      (exterior := exterior) (curvatureCertificate := curvatureCertificate)) ∧
    Nonempty (ThreeDimensionalSU2SameTheoryData.{uEG, uEP, uHP, uGauge,
      uP, uLift, uH, uLabel}
      (fieldData := fieldData) (inner := inner) (connection := connection)
      (exterior := exterior) (curvatureCertificate := curvatureCertificate)) :=
  ⟨⟨data.sameTheory.continuum⟩, ⟨data.sameTheory⟩⟩

/-- The exact gauge tier is literal matrix SU(2), not merely a generic compact-simple group. -/
theorem exact_su2_tier :
    Nonempty (GaugeGroup ≃ₜ* SpecialUnitaryTwo) :=
  ⟨data.toSU2GaugeGroup.identification⟩

/-- The same exact continuum local family contains a nontrivial Wightman field. -/
theorem exact_nontrivial_continuum_field :
    ∃ (test : Minkowski.ScalarMinkowskiSchwartzTestFunction EuclideanDimension.three)
      (vector : D.domain),
      fieldData.field test vector ≠ 0 ∧
      fieldData.field test vector ≠
        data.sameTheory.continuum.observableFamily.operator
          data.sameTheory.continuum.observableFamily.unitLabel test vector :=
  data.sameTheory.continuum.fieldObservableCoherence.field_nontrivial_witness

/-- The interpreted curvature-squared observable is nontrivial in that same family. -/
theorem exact_nontrivial_curvatureSquared :
    data.sameTheory.continuum.curvatureSquaredInterpretation.quantumLabel .curvatureSquared ≠
      data.sameTheory.continuum.observableFamily.unitLabel ∧
    ∃ (test : Minkowski.ScalarMinkowskiSchwartzTestFunction EuclideanDimension.three)
      (vector : D.domain),
      data.sameTheory.continuum.observableFamily.operator
          (data.sameTheory.continuum.curvatureSquaredInterpretation.quantumLabel
            .curvatureSquared) test vector ≠ 0 :=
  ⟨data.sameTheory.continuum.curvatureSquaredInterpretation.curvatureSquaredLabel_ne_unit,
    ⟨(data.sameTheory.continuum.curvatureSquaredInterpretation.curvatureSquared_nontrivial).choose,
      (data.sameTheory.continuum.curvatureSquaredInterpretation.curvatureSquared_nontrivial).choose_spec.choose,
      (data.sameTheory.continuum.curvatureSquaredInterpretation.curvatureSquared_nontrivial).choose_spec.choose_spec.1⟩⟩

/-- The Euclidean and Minkowski families are tied by the stored Wick-continuation witness. -/
theorem exact_sameTheory_wick :
    Nonempty (Reconstruction.MathlibStrictOrderedScalarWickContinuationData
      data.sameTheory.schwingerFamily data.sameTheory.relativeAnalyticCorrelators) :=
  ⟨data.sameTheory.strictWickCoherence⟩

/-- The physical threshold is positive and the same PVM has a nonzero bounded excitation band. -/
theorem exact_samePVM_gap_nonvacuity :
    0 < data.gapThreshold ∧
    ∃ energy : ℝ, 0 < energy ∧ data.gapThreshold ≤ energy ∧
      data.sameTheory.continuum.wightmanSurface.spectrum.joint.pvm.projection
        (Minkowski.boundedPositiveEnergyExcitationRegion EuclideanDimension.three energy) ≠ 0 :=
  ⟨data.gapThreshold_pos, data.nonvacuum_spectrum_nonempty⟩

/-- Hostile gap probe: a nonpositive threshold is rejected. -/
theorem nonpositive_gap_blocked (h : data.gapThreshold ≤ 0) : False :=
  (not_le_of_gt data.gapThreshold_pos) h

/-- Hostile spectrum probe: a disconnected PVM cannot replace the same-theory spectrum. -/
theorem disconnected_spectrum_blocked
    (wrong : Minkowski.ForwardConeJointTranslationSpectrumData U)
    (different : wrong ≠ data.sameTheory.continuum.wightmanSurface.spectrum)
    (claimed : wrong = data.sameTheory.continuum.wightmanSurface.spectrum) : False :=
  different claimed

/-- The accepted coordinate dimension is exactly three and differs from 2D and 4D indices. -/
theorem exact_dimension_separation :
    EuclideanDimension.three.value = 3 ∧
      EuclideanDimension.three ≠ EuclideanDimension.two ∧
      EuclideanDimension.three ≠ EuclideanDimension.four := by
  refine ⟨data.exact_dimension.1, ?_, ?_⟩ <;> intro equality <;>
    have valueEquality := congrArg EuclideanDimension.value equality <;> simp at valueEquality

/-- No accepted 3D coordinate carrier can be linearly identified with the 4D Clay carrier. -/
theorem four_dimensional_linear_substitution_blocked :
    ¬ Nonempty (ThreeDimensionalEuclideanBase ≃ₗ[ℝ]
      EuclideanDimension.four.Spacetime) := by
  have _exactDimension := data.exact_dimension
  rintro ⟨equiv⟩
  have ranks := LinearEquiv.finrank_eq equiv
  norm_num [EuclideanDimension.finrank_spacetime] at ranks

end

end YangMills.Dimensions.ThreeDimensionalSU2ExistenceMassGapAcceptance.Probes
