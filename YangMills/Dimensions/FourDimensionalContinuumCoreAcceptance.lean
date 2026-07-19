/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Classical.CanonicalEuclideanMetric
import YangMills.Classical.EuclideanAction
import YangMills.Euclidean.OSOrderedFourDimensionalEuclideanCurrentStrength
import YangMills.Geometry.LieGroup
import YangMills.Minkowski.PhysicalMassGapSupremum
import YangMills.Minkowski.PoincareTopologicalDoubleCover
import YangMills.Minkowski.ScalarWightmanAxiomSurface
import YangMills.Minkowski.StressEnergyTranslationWard
import YangMills.Minkowski.WightmanJointTemperedCorrelators
import YangMills.Minkowski.WightmanLinearGrowth
import YangMills.Minkowski.WightmanLocalObservableCoherence
import YangMills.Minkowski.WightmanRelativeAnalyticCorrelators
import YangMills.Minkowski.WeakOperatorProductExpansion
import YangMills.Observables.CurvatureSquaredInterpretation
import YangMills.Observables.CurvatureSquaredOPECoherence
import YangMills.Reconstruction.SameFieldOSIIOutputCorrelatorUniqueness
import YangMills.Renormalization.AsymptoticFreedomOPE

/-!
# Four-dimensional current-strength continuum core acceptance

This module defines an uninhabited, per-carrier acceptance record hard-wired to four-dimensional
Euclidean spacetime. It joins one compact-simple physical gauge group and exact classical curvature
chain to one ambient Euclidean scalar family with exact source restrictions, one independent
Minkowski/Wightman chain, an explicit
exact-source Wick-continuation bridge, one covariant local-observable family containing that Wightman
field, an interpretation of the exact classical `F²` observable, a local stress tensor whose
regulated charges and translation Ward identities use the same joint translation PVM, and a
physical gap on that spectrum.

The classical base is exactly coordinate `ℝ⁴`, its metric is Mathlib's canonical flat inner-product
metric, and the designated action measure must equal coordinate Lebesgue measure. A general project
bridge identifying metric-induced Riemannian volume with that measure remains absent. The name
includes `CurrentStrength` because the Euclidean record has carrier-exact OS-II `(E0′)` on the
coincidence-flat restriction and exact source-carrier OS-I `(E1)`–`(E4)`, but retains extra ambient
tempered extensions and has no corrected reconstruction theorem. The exact lift is now required to
carry a genuine two-sheeted topological covering projection, while concrete inhomogeneous
`SL(2,ℂ)`, affine-target group laws, and `{±1}` kernel identification remain open. No lattice datum can fill
any field of this record. The exact compact-simple gauge certificate indexes a preliminary
four-dimensional running-coupling normal form and a supplied weak regular-variation condition on the
exact same-family OPE. Neither provides source-faithful group-normalized perturbative coefficients,
operator mixing or remainders; no source-facing OS completed-tensor carrier, inhabitant, theory,
existence theorem, or mass-gap proof is constructed.
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
  /-- Genuine two-sheeted topological covering requirement on the exact Poincaré lift group. -/
  poincareDoubleCover : Minkowski.ProperOrthochronousPoincareDoubleCoverData
    EuclideanDimension.four PoincareLiftGroup
  /-- The double cover strengthens the exact lift already indexing the representation; no
  disconnected second projection is accepted. -/
  poincareDoubleCover_toLift_eq :
    poincareDoubleCover.toProperOrthochronousPoincareLiftData = lift
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
  /-- Current-strength Euclidean package with carrier-exact OS-II `(E0′)` on the coincidence-flat
  restriction and source-carrier OS-I `(E1)`–`(E4)` on that same ambient family. -/
  sourceEuclideanCurrentStrength :
    OSSourceFourDimensionalEuclideanCurrentStrengthData schwingerFamily
  /-- Integrated Wightman requirements on the exact supplied field/domain/vacuum/representation. -/
  wightmanSurface : Minkowski.ScalarWightmanAxiomSurfaceData fieldData
  /-- Full-product tempered correlators of that exact Wightman field. -/
  fullCorrelators : Minkowski.ScalarWightmanJointTemperedCorrelatorData fieldData
  /-- Selected `(R0′)`, relative analytic, and exact-source Wick data together with all-arity
  correlator-extension uniqueness on this same field realization. This is not reconstruction
  uniqueness across heterogeneous Wightman theories. -/
  sameFieldOSIIOutputUniqueness :
    Reconstruction.SameFieldOSIIOutputCorrelatorUniquenessData
      schwingerFamily fullCorrelators
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
  /-- Decidable equality is retained explicitly for finite OPE truncations; it is not installed as
  a global instance on an unrelated label carrier. -/
  observableLabelDecidableEq : DecidableEq observableFamily.Label
  /-- Exact weak full bilocal products for the same local-observable family. -/
  observableProducts : Minkowski.WeakTemperedBilocalObservableProductData observableFamily
  /-- Weak all-orders OPE on those exact products and labels. -/
  weakOPE :
    letI : DecidableEq observableFamily.Label := observableLabelDecidableEq
    Minkowski.WeakOperatorProductExpansionData observableProducts
  /-- Preliminary supplied regular-variation scaling of the exact OPE coefficients by the same
  running coupling. This remains weaker than Clay's prescribed perturbative singularities. -/
  opeRegularVariation :
    letI : DecidableEq observableFamily.Label := observableLabelDecidableEq
    Renormalization.SuppliedWeakOPERegularVariationData asymptoticFreedom weakOPE
  /-- The interpreted `F² × F²` product has one actual nonzero zeroth-order term in that exact OPE. -/
  curvatureSquaredOPECoherence :
    letI : DecidableEq observableFamily.Label := observableLabelDecidableEq
    Observables.CurvatureSquaredOPECoherenceData
      (Classical.canonicalEuclideanSpacetimeMetricData EuclideanDimension.four)
      inner connection exterior curvatureCertificate curvatureSquaredInterpretation weakOPE
  /-- The selected nonzero `F² × F²` coefficient genuinely depends on the same running coupling;
  the generic regular-variation witness is not allowed to come only from an unrelated coefficient. -/
  curvatureSquaredCouplingExponent_nonzero :
    letI : DecidableEq observableFamily.Label := observableLabelDecidableEq
    opeRegularVariation.couplingExponent
      (curvatureSquaredInterpretation.quantumLabel
        Observables.BasicCurvatureObservableTag.curvatureSquared)
      (curvatureSquaredInterpretation.quantumLabel
        Observables.BasicCurvatureObservableTag.curvatureSquared)
      curvatureSquaredOPECoherence.outputLabel ≠ 0
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

/-- Corrected OS-II output growth selected by the same-field correlator package. -/
def wightmanLinearGrowth
    (data : FourDimensionalCurrentStrengthContinuumCoreAcceptanceData inner connection
      exterior curvatureCertificate fieldData) :
    Minkowski.OSIIWightmanLinearGrowthData data.fullCorrelators :=
  data.sameFieldOSIIOutputUniqueness.selectedGrowth

/-- Relative analytic correlators selected by the same-field correlator package. -/
def relativeAnalyticCorrelators
    (data : FourDimensionalCurrentStrengthContinuumCoreAcceptanceData inner connection
      exterior curvatureCertificate fieldData) :
    Minkowski.ScalarWightmanRelativeAnalyticCorrelatorData data.fullCorrelators :=
  data.sameFieldOSIIOutputUniqueness.selectedRelative

/-- Exact-source Wick coherence selected by the same-field correlator package. -/
def sourceWickCoherence
    (data : FourDimensionalCurrentStrengthContinuumCoreAcceptanceData inner connection
      exterior curvatureCertificate fieldData) :
    Reconstruction.OSSourceOrderedScalarWickContinuationData
      data.schwingerFamily data.relativeAnalyticCorrelators :=
  data.sameFieldOSIIOutputUniqueness.selectedWick

/-- Restrict the exact source-carrier Wick coherence to the old strict domain. This is derived, not
an independent second Euclidean/Minkowski bridge. -/
noncomputable def strictWickCoherence
    (data : FourDimensionalCurrentStrengthContinuumCoreAcceptanceData inner connection
      exterior curvatureCertificate fieldData) :
    Reconstruction.MathlibStrictOrderedScalarWickContinuationData
      data.schwingerFamily data.relativeAnalyticCorrelators :=
  data.sourceWickCoherence.toMathlibStrict

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

/-- The exact same-family OPE has a genuinely nonzero contracted zeroth-order term. -/
theorem ope_nonzero_zerothOrderTerm
    (data : FourDimensionalCurrentStrengthContinuumCoreAcceptanceData inner connection
      exterior curvatureCertificate fieldData) :
    letI : DecidableEq data.observableFamily.Label := data.observableLabelDecidableEq
    ∃ (A B C : data.observableFamily.Label) (bra ket : D.domain),
      C ∈ data.weakOPE.truncation 0 ∧
      data.weakOPE.contraction.contract (data.weakOPE.coefficient A B C)
        (data.observableFamily.matrixElement C bra ket) ≠ 0 := by
  letI : DecidableEq data.observableFamily.Label := data.observableLabelDecidableEq
  exact data.weakOPE.exists_nonzero_zerothOrderTerm

/-- The interpreted `F² × F²` expansion has an exact nonzero contracted zeroth-order term. -/
theorem curvatureSquaredOPEContractedTerm_nonzero
    (data : FourDimensionalCurrentStrengthContinuumCoreAcceptanceData inner connection
      exterior curvatureCertificate fieldData) :
    letI : DecidableEq data.observableFamily.Label := data.observableLabelDecidableEq
    data.weakOPE.contraction.contract
      (data.weakOPE.coefficient
        (data.curvatureSquaredInterpretation.quantumLabel
          Observables.BasicCurvatureObservableTag.curvatureSquared)
        (data.curvatureSquaredInterpretation.quantumLabel
          Observables.BasicCurvatureObservableTag.curvatureSquared)
        data.curvatureSquaredOPECoherence.outputLabel)
      (data.observableFamily.matrixElement
        data.curvatureSquaredOPECoherence.outputLabel
        data.curvatureSquaredOPECoherence.bra
        data.curvatureSquaredOPECoherence.ket) ≠ 0 := by
  letI : DecidableEq data.observableFamily.Label := data.observableLabelDecidableEq
  exact data.curvatureSquaredOPECoherence.contractedTerm_nonzero

/-- The same selected `F² × F²` coefficient has nonzero leading scaling distribution. -/
theorem curvatureSquaredOPELeadingDistribution_nonzero
    (data : FourDimensionalCurrentStrengthContinuumCoreAcceptanceData inner connection
      exterior curvatureCertificate fieldData) :
    letI : DecidableEq data.observableFamily.Label := data.observableLabelDecidableEq
    data.opeRegularVariation.leadingDistribution
      (data.curvatureSquaredInterpretation.quantumLabel
        Observables.BasicCurvatureObservableTag.curvatureSquared)
      (data.curvatureSquaredInterpretation.quantumLabel
        Observables.BasicCurvatureObservableTag.curvatureSquared)
      data.curvatureSquaredOPECoherence.outputLabel ≠ 0 := by
  letI : DecidableEq data.observableFamily.Label := data.observableLabelDecidableEq
  exact data.opeRegularVariation.leadingDistribution_nonzero _ _ _
    data.curvatureSquaredOPECoherence.coefficient_nonzero

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
