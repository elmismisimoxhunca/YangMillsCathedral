/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Classical.CanonicalEuclideanMetric
import YangMills.Classical.EuclideanAction
import YangMills.Euclidean.SchwingerEuclideanCandidate
import YangMills.Geometry.LieGroup
import YangMills.Minkowski.PhysicalMassGapSupremum
import YangMills.Minkowski.ScalarWightmanAxiomSurface
import YangMills.Minkowski.StressEnergyTranslationWard
import YangMills.Minkowski.WightmanJointTemperedCorrelators
import YangMills.Minkowski.WightmanLocalObservableCoherence
import YangMills.Minkowski.WightmanRelativeAnalyticCorrelators
import YangMills.Observables.CurvatureSquaredInterpretation
import YangMills.Reconstruction.StrictOrderedWickContinuation
import YangMills.Renormalization.RunningCoupling

/-!
# Four-dimensional current-strength continuum core acceptance

This module defines an uninhabited, per-carrier acceptance record hard-wired to four-dimensional
Euclidean spacetime. It joins one compact-simple physical gauge group and exact classical curvature
chain to one strict Euclidean scalar family, one independent Minkowski/Wightman chain, an explicit
strict Wick-continuation bridge, one covariant local-observable family containing that Wightman
field, an interpretation of the exact classical `F²` observable, a local stress tensor whose
regulated charges and translation Ward identities use the same joint translation PVM, and a
physical gap on that spectrum.

The classical base is exactly coordinate `ℝ⁴`, its metric is Mathlib's canonical flat inner-product
metric, and the designated action measure must equal coordinate Lebesgue measure. A general project
bridge identifying metric-induced Riemannian volume with that measure remains absent. The name includes `CurrentStrength` because the Euclidean
record is the project's current strict Mathlib candidate, not source-facing OS-II `(E0')`/OS-I
`(E2)`/`(E4)` data or a reconstruction theorem. The Poincaré object remains the current lift/pre-cover interface. No lattice datum can fill
any field of this record. The exact compact-simple gauge certificate indexes a preliminary
four-dimensional running-coupling normal form, but no source-facing OS completed-tensor carrier,
renormalized OPE coefficient bridge, inhabitant, theory, existence theorem, or mass-gap proof is
constructed.
-/

namespace YangMills.Dimensions

open scoped Manifold ContDiff

universe uEG uEP uHP uGauge uP uLift uH uLabel

noncomputable section

/-- Exact classical coordinate base for the four-dimensional core. -/
abbrev FourDimensionalEuclideanBase := EuclideanDimension.four.Spacetime

/-- Self model for the exact four-dimensional Euclidean coordinate base. -/
abbrev fourDimensionalEuclideanModel :=
  modelWithCornersSelf ℝ FourDimensionalEuclideanBase

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

/-- Current-strength four-dimensional continuum core, indexed by one exact classical geometry and
one exact Minkowski physical chain. Every quantum object is definitionally specialized to
`EuclideanDimension.four`; the physical gauge group and Poincaré lift group remain distinct. -/
structure FourDimensionalCurrentStrengthContinuumCoreAcceptanceData
    (inner : Geometry.InvariantInnerProductData
      (I := modelWithCornersSelf ℝ EG) (G := GaugeGroup))
    (connection : Geometry.PrincipalConnectionData smoothBundle)
    (exterior : Geometry.PrincipalConnectionExteriorDerivativeData connection)
    (curvatureCertificate : Geometry.PrincipalCurvatureStructureCertificate
      smoothBundle connection exterior)
    (fieldData : Minkowski.ScalarWightmanFieldOnCommonDomainData D) where
  /-- Exact compact-simple convention for the physical gauge group, not the Poincaré lift group. -/
  compactSimpleGaugeGroup : Geometry.CompactSimpleGaugeGroupData GaugeGroup EG
  /-- Preliminary four-dimensional pure-gauge ultraviolet running-coupling normal form indexed by
  that exact compact-simple gauge-group certificate. -/
  asymptoticFreedom : Renormalization.PureYangMillsAsymptoticFreedomData
    EuclideanDimension.four compactSimpleGaugeGroup
  /-- Relative-to-designated-measure analytic action data on the same classical curvature chain. -/
  classicalAction : Classical.EuclideanActionAnalyticData
    (Classical.canonicalEuclideanSpacetimeMetricData EuclideanDimension.four)
    inner connection exterior curvatureCertificate
  /-- The designated action measure is coordinate Lebesgue measure on the exact canonical-flat
  `ℝ⁴` base. A general metric-induced-volume API bridge remains separate debt. -/
  classicalMeasure_eq_coordinateLebesgue : classicalAction.measure = MeasureTheory.volume
  /-- One exact scalar Schwinger distribution family in Euclidean spacetime dimension four. -/
  schwingerFamily : ScalarSchwingerDistributionFamily EuclideanDimension.four
  /-- Explicit one-dimensional spatial-ray direction inside four-dimensional spacetime's
  three-dimensional spatial slice. -/
  spatialDirection : EuclideanUnitSpatialDirection EuclideanDimension.four
  /-- Current strict-domain Euclidean candidate on that exact family and direction. -/
  strictEuclideanCandidate :
    MathlibStrictScalarEuclideanCandidate schwingerFamily spatialDirection
  /-- Integrated Wightman requirements on the exact supplied field/domain/vacuum/representation. -/
  wightmanSurface : Minkowski.ScalarWightmanAxiomSurfaceData fieldData
  /-- Full-product tempered correlators of that exact Wightman field. -/
  fullCorrelators : Minkowski.ScalarWightmanJointTemperedCorrelatorData fieldData
  /-- Relative analytic correlators derived from the same full correlator family. -/
  relativeAnalyticCorrelators :
    Minkowski.ScalarWightmanRelativeAnalyticCorrelatorData fullCorrelators
  /-- Explicit strict ordered Wick coherence between the exact Euclidean and Minkowski families. -/
  strictWickCoherence : Reconstruction.MathlibStrictOrderedScalarWickContinuationData
    schwingerFamily relativeAnalyticCorrelators
  /-- One local-observable family on the same common invariant domain. -/
  observableFamily : Minkowski.TemperedLocalObservableFamilyData.{uLift, uH, uLabel} D
  /-- Adjoint closure, covariance, and locality on that same family and representation chain. -/
  covariantObservableFamily :
    Minkowski.CovariantLocalObservableFamilyData observableFamily
  /-- The scalar Wightman field is an exact nontrivial label of that same family. -/
  fieldObservableCoherence :
    Minkowski.ScalarWightmanFieldLocalObservableCoherenceData
      fieldData observableFamily covariantObservableFamily
  /-- Exact unit/curvature-squared interpretation from the same classical geometry into the same
  quantum family; this is not a complete curvature-polynomial grammar. -/
  curvatureSquaredInterpretation :
    Observables.CurvatureSquaredLocalObservableInterpretationData
      (Classical.canonicalEuclideanSpacetimeMetricData EuclideanDimension.four)
      inner connection exterior curvatureCertificate observableFamily
  /-- Symmetric, Hermitian, covariant, local, weakly conserved stress tensor in the same family. -/
  stressEnergy : Minkowski.LocalStressEnergyTensorData observableFamily
  /-- The stress charges, translation derivatives, Ward identity, and momentum moments use the
  exact same representation, domain, family, and Wightman joint PVM. -/
  stressTranslationWard : Minkowski.LocalStressEnergyTranslationWardData
    stressEnergy wightmanSurface.spectrum
  /-- One selected physical gap threshold; positivity and excitation nonvacuity are in the exact
  same-PVM predicate below. -/
  gapThreshold : ℝ
  /-- Physical joint-spectral gap on `wightmanSurface.spectrum`, the same PVM tied to `U`. -/
  physicalMassGap : wightmanSurface.HasPhysicalMassGap gapThreshold

namespace FourDimensionalCurrentStrengthContinuumCoreAcceptanceData

variable
    {inner : Geometry.InvariantInnerProductData
      (I := modelWithCornersSelf ℝ EG) (G := GaugeGroup)}
    {connection : Geometry.PrincipalConnectionData smoothBundle}
    {exterior : Geometry.PrincipalConnectionExteriorDerivativeData connection}
    {curvatureCertificate : Geometry.PrincipalCurvatureStructureCertificate
      smoothBundle connection exterior}

/-- The accepted spacetime dimension is definitionally four, with a three-dimensional spatial slice. -/
theorem exact_dimension
    (_data : FourDimensionalCurrentStrengthContinuumCoreAcceptanceData inner connection
      exterior curvatureCertificate fieldData) :
    EuclideanDimension.four.value = 4 ∧
      EuclideanDimension.four.spatialDimension = 3 := by
  exact ⟨rfl, rfl⟩

/-- The ultraviolet normal form is tied definitionally to the four-dimensional contract index. -/
theorem asymptoticFreedom_dimension
    (data : FourDimensionalCurrentStrengthContinuumCoreAcceptanceData inner connection
      exterior curvatureCertificate fieldData) :
    EuclideanDimension.four = EuclideanDimension.four :=
  data.asymptoticFreedom.dimension_eq_four

/-- The accepted ultraviolet running coupling cannot be a scale-independent constant. -/
theorem runningCoupling_not_constant
    (data : FourDimensionalCurrentStrengthContinuumCoreAcceptanceData inner connection
      exterior curvatureCertificate fieldData) :
    ¬ ∃ coupling : ℝ,
      data.asymptoticFreedom.runningCoupling = fun _ => coupling :=
  data.asymptoticFreedom.runningCoupling_not_constant

/-- The selected threshold is strictly positive by the exact same-PVM gap predicate. -/
theorem gapThreshold_pos
    (data : FourDimensionalCurrentStrengthContinuumCoreAcceptanceData inner connection
      exterior curvatureCertificate fieldData) :
    0 < data.gapThreshold :=
  data.physicalMassGap.1

/-- The same selected gap yields finite-positive supremum semantics on the exact surface spectrum. -/
theorem hasFinitePositivePhysicalMassGap
    (data : FourDimensionalCurrentStrengthContinuumCoreAcceptanceData inner connection
      exterior curvatureCertificate fieldData) :
    Minkowski.HasFinitePositivePhysicalMassGap vacuumData data.wightmanSurface.spectrum :=
  Minkowski.hasFinitePositivePhysicalMassGap_of_hasPhysicalJointSpectralMassGap
    data.physicalMassGap

/-- The physical time-translation generator tied to the same stress tensor and PVM is nonzero on
one exact common-domain vector. -/
theorem timeTranslationGenerator_nontrivial
    (data : FourDimensionalCurrentStrengthContinuumCoreAcceptanceData inner connection
      exterior curvatureCertificate fieldData) :
    ∃ vector : D.domain,
      data.stressTranslationWard.momentumGenerator
        (Minkowski.stressTensorTimeIndex EuclideanDimension.four) vector ≠ 0 :=
  data.stressTranslationWard.timeGenerator_nontrivial

/-- The coherently selected Wightman field is nonzero and differs from the unit on one test/vector. -/
theorem wightmanField_nontrivial
    (data : FourDimensionalCurrentStrengthContinuumCoreAcceptanceData inner connection
      exterior curvatureCertificate fieldData) :
    ∃ (test : Minkowski.ScalarMinkowskiSchwartzTestFunction EuclideanDimension.four)
      (vector : D.domain),
      fieldData.field test vector ≠ 0 ∧
      fieldData.field test vector ≠
        data.observableFamily.operator data.observableFamily.unitLabel test vector :=
  data.fieldObservableCoherence.field_nontrivial_witness

end FourDimensionalCurrentStrengthContinuumCoreAcceptanceData

end

end YangMills.Dimensions
