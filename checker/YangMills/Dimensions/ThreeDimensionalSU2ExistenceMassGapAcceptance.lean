/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Dimensions.ThreeDimensionalCheckerFoundation
import YangMills.Dimensions.ThreeDimensionalSU2GaugeGroup

/-!
# Bounded three-dimensional SU(2) existence and mass-gap truth teller

This file separates the future construction target into three dependent tiers:

1. a nontrivial continuum Wightman/local-observable theory tied to exact classical SU(2)
   Yang--Mills geometry through the interpreted curvature-squared observable;
2. an explicit Euclidean family and strict ordered Wick-continuation identification with that same
   Minkowski theory;
3. a positive physical mass gap on that theory's exact joint translation PVM.

The final proposition is merely the nonemptiness of the strongest tier. No carrier, field, theory,
reconstruction, SU(2) Yang--Mills existence theorem, or mass gap is constructed. The Euclidean field
uses the project's current strict-domain candidate, so every declaration records that precise
contract rather than claiming a source-complete Osterwalder--Schrader reconstruction theorem.
-/

namespace YangMills.Dimensions

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

/-- Tier 1: exact SU(2) classical geometry joined to one nontrivial continuum Wightman theory and
one same-family interpretation of the classical curvature-squared observable. -/
structure ThreeDimensionalSU2ContinuumExistenceData where
  su2GaugeGroup : ThreeDimensionalSU2GaugeGroupData (E := EG) (GaugeGroup := GaugeGroup)
  classicalAction : Classical.EuclideanActionAnalyticData
    (Classical.canonicalEuclideanSpacetimeMetricData EuclideanDimension.three)
    inner connection exterior curvatureCertificate
  classicalMeasure_eq_coordinateLebesgue : classicalAction.measure = MeasureTheory.volume
  wightmanSurface : Minkowski.ScalarWightmanAxiomSurfaceData fieldData
  fullCorrelators : Minkowski.ScalarWightmanJointTemperedCorrelatorData fieldData
  observableFamily : Minkowski.TemperedLocalObservableFamilyData.{uLift, uH, uLabel} D
  covariantObservableFamily :
    Minkowski.CovariantLocalObservableFamilyData observableFamily
  fieldObservableCoherence :
    Minkowski.ScalarWightmanFieldLocalObservableCoherenceData
      fieldData observableFamily covariantObservableFamily
  curvatureSquaredInterpretation :
    Observables.CurvatureSquaredLocalObservableInterpretationData
      (Classical.canonicalEuclideanSpacetimeMetricData EuclideanDimension.three)
      inner connection exterior curvatureCertificate observableFamily
  curvatureSquaredLabel_mem_scalar :
    curvatureSquaredInterpretation.quantumLabel .curvatureSquared ∈
      covariantObservableFamily.scalarLabel

/-- Tier 2: an explicit Euclidean family is identified by strict ordered Wick continuation with the
same full-correlator Wightman theory stored in Tier 1. -/
structure ThreeDimensionalSU2SameTheoryData where
  continuum : ThreeDimensionalSU2ContinuumExistenceData.{uEG, uEP, uHP, uGauge, uP,
    uLift, uH, uLabel}
    (fieldData := fieldData) (inner := inner) (connection := connection)
    (exterior := exterior) (curvatureCertificate := curvatureCertificate)
  schwingerFamily : ScalarSchwingerDistributionFamily EuclideanDimension.three
  spatialDirection : EuclideanUnitSpatialDirection EuclideanDimension.three
  strictEuclideanCandidate :
    MathlibStrictScalarEuclideanCandidate schwingerFamily spatialDirection
  relativeAnalyticCorrelators :
    Minkowski.ScalarWightmanRelativeAnalyticCorrelatorData continuum.fullCorrelators
  strictWickCoherence : Reconstruction.MathlibStrictOrderedScalarWickContinuationData
    schwingerFamily relativeAnalyticCorrelators

/-- Tier 3 and strongest data: the same reconstructed Wightman theory has a positive physical gap
on its exact joint translation PVM. The predicate itself requires a nonvacuum spectral sector. -/
structure ThreeDimensionalSU2ExistenceMassGapAcceptanceData where
  sameTheory : ThreeDimensionalSU2SameTheoryData.{uEG, uEP, uHP, uGauge, uP,
    uLift, uH, uLabel}
    (fieldData := fieldData) (inner := inner) (connection := connection)
    (exterior := exterior) (curvatureCertificate := curvatureCertificate)
  gapThreshold : ℝ
  physicalMassGap : sameTheory.continuum.wightmanSurface.HasPhysicalMassGap gapThreshold

/-- Authoritative bounded three-dimensional SU(2) truth-teller. It is intentionally uninhabited. -/
def ThreeDimensionalSU2ExistenceMassGapAcceptance : Prop :=
  Nonempty (ThreeDimensionalSU2ExistenceMassGapAcceptanceData.{uEG, uEP, uHP, uGauge,
    uP, uLift, uH, uLabel}
    (fieldData := fieldData) (inner := inner) (connection := connection)
    (exterior := exterior) (curvatureCertificate := curvatureCertificate))

/-- Exact component decomposition of the authoritative proposition. The same dependent
`sameTheory` witness contains the continuum tier, and the gap predicate is indexed by that witness's
unchanged Wightman surface and joint translation PVM. -/
theorem threeDimensionalSU2Acceptance_nonempty_iff_components :
    ThreeDimensionalSU2ExistenceMassGapAcceptance.{uEG, uEP, uHP, uGauge, uP,
      uLift, uH, uLabel}
      (fieldData := fieldData) (inner := inner) (connection := connection)
      (exterior := exterior) (curvatureCertificate := curvatureCertificate) ↔
    ∃ (sameTheory : ThreeDimensionalSU2SameTheoryData.{uEG, uEP, uHP, uGauge, uP,
        uLift, uH, uLabel}
        (fieldData := fieldData) (inner := inner) (connection := connection)
        (exterior := exterior) (curvatureCertificate := curvatureCertificate))
      (gapThreshold : ℝ),
      sameTheory.continuum.wightmanSurface.HasPhysicalMassGap gapThreshold := by
  constructor
  · rintro ⟨data⟩
    exact ⟨data.sameTheory, data.gapThreshold, data.physicalMassGap⟩
  · rintro ⟨sameTheory, gapThreshold, physicalMassGap⟩
    exact ⟨⟨sameTheory, gapThreshold, physicalMassGap⟩⟩

namespace ThreeDimensionalSU2ExistenceMassGapAcceptanceData

/-- The strongest gate projects definitionally to exact SU(2) gauge geometry. -/
def toSU2GaugeGroup
    (data : ThreeDimensionalSU2ExistenceMassGapAcceptanceData
      (fieldData := fieldData) (inner := inner) (connection := connection)
      (exterior := exterior) (curvatureCertificate := curvatureCertificate)) :
    ThreeDimensionalSU2GaugeGroupData (E := EG) (GaugeGroup := GaugeGroup) :=
  data.sameTheory.continuum.su2GaugeGroup

/-- The strongest gate retains exact dimension three. -/
theorem exact_dimension
    (_data : ThreeDimensionalSU2ExistenceMassGapAcceptanceData
      (fieldData := fieldData) (inner := inner) (connection := connection)
      (exterior := exterior) (curvatureCertificate := curvatureCertificate)) :
    EuclideanDimension.three.value = 3 ∧
      EuclideanDimension.three.spatialDimension = 2 :=
  ⟨rfl, rfl⟩

/-- The selected physical threshold is strictly positive. -/
theorem gapThreshold_pos
    (data : ThreeDimensionalSU2ExistenceMassGapAcceptanceData
      (fieldData := fieldData) (inner := inner) (connection := connection)
      (exterior := exterior) (curvatureCertificate := curvatureCertificate)) :
    0 < data.gapThreshold :=
  data.physicalMassGap.1

/-- The gap belongs to the exact joint translation PVM stored by the same continuum theory. -/
theorem exact_sameTheory_gap
    (data : ThreeDimensionalSU2ExistenceMassGapAcceptanceData
      (fieldData := fieldData) (inner := inner) (connection := connection)
      (exterior := exterior) (curvatureCertificate := curvatureCertificate)) :
    data.sameTheory.continuum.wightmanSurface.HasPhysicalMassGap data.gapThreshold :=
  data.physicalMassGap

/-- The same-PVM gap has a nonvacuum spectral witness; it cannot hold by an empty excitation sector. -/
theorem nonvacuum_spectrum_nonempty
    (data : ThreeDimensionalSU2ExistenceMassGapAcceptanceData
      (fieldData := fieldData) (inner := inner) (connection := connection)
      (exterior := exterior) (curvatureCertificate := curvatureCertificate)) :
    ∃ energy : ℝ, 0 < energy ∧ data.gapThreshold ≤ energy ∧
      data.sameTheory.continuum.wightmanSurface.spectrum.joint.pvm.projection
        (Minkowski.boundedPositiveEnergyExcitationRegion EuclideanDimension.three energy) ≠ 0 :=
  data.physicalMassGap.2.2.2

end ThreeDimensionalSU2ExistenceMassGapAcceptanceData

end

end YangMills.Dimensions
