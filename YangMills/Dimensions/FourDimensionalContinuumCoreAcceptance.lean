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
import YangMills.Minkowski.ScalarWightmanPoincareDescent
import YangMills.Minkowski.ScalarWightmanAxiomSurface
import YangMills.Minkowski.StressEnergyTranslationWard
import YangMills.Minkowski.WightmanJointTemperedCorrelators
import YangMills.Minkowski.WightmanLinearGrowth
import YangMills.Minkowski.WightmanLocalObservableCoherence
import YangMills.Minkowski.WightmanRelativeAnalyticCorrelators
import YangMills.Minkowski.WeakOperatorProductExpansion
import YangMills.Observables.CurvaturePowerInterpretation
import YangMills.Observables.CurvatureSquaredOPECoherence
import YangMills.Reconstruction.CorrectedOSIIReconstructionAcceptance
import YangMills.Renormalization.AdjointCasimirNormalization
import YangMills.Renormalization.AsymptoticFreedomOPE

/-!
# Four-dimensional current-strength continuum core acceptance

This module defines an uninhabited, per-carrier acceptance record hard-wired to four-dimensional
Euclidean spacetime. It joins one compact-simple physical gauge group and exact classical curvature
chain to one ambient Euclidean scalar family with exact source restrictions, one independent
Minkowski/Wightman chain, an explicit
exact-source Wick-continuation bridge, one covariant local-observable family containing that Wightman
field, interpretations of the finite scalar fragment `1`, `F²`, `(F²)²`, a local stress tensor whose
regulated charges and translation Ward identities use the same joint translation PVM, and a
physical gap on that spectrum.

The classical base is exactly coordinate `ℝ⁴`, its metric is Mathlib's canonical flat inner-product
metric, and the designated action measure must equal coordinate Lebesgue measure. A general project
bridge identifying metric-induced Riemannian volume with that measure remains absent. The name
includes `CurrentStrength` because the Euclidean record has carrier-exact OS-II `(E0′)` on the
coincidence-flat restriction and exact source-carrier OS-I `(E1)`–`(E4)`, but retains extra ambient
tempered extensions and now requires corrected same-lift, universe-relative reconstruction
acceptance without
constructing a reconstruction. The exact lift is required to
carry a genuine two-sheeted topological covering projection whose exact group kernel is identified
with the literal complex signs `{±1}`. Scalar covariance, exact vacuum invariance, and cyclicity
then derive trivial action of that kernel on the same physical Hilbert representation, which
therefore descends to a strongly continuous homomorphism on the named affine target. The original
uncast scalar field and every explicitly designated scalar label of the original covariant
observable family inherit direct affine covariance; tensor labels retain separate transformation
laws. Concrete inhomogeneous `SL(2,ℂ)` and construction of the
required named affine-target group law remain open. No lattice datum can fill
any field of this record. The exact compact-simple gauge certificate indexes a preliminary
four-dimensional running-coupling normal form and a supplied weak regular-variation condition on the
exact same-family OPE. The running coupling's leading coefficient is now tied to an exact
pairing-orthonormal basis and adjoint-Casimir identity, and its value at an explicit ultraviolet
reference scale is the exact outer coupling in the classical action. The connection-level
field-rescaling convention, independent curvature contractions/covariant-derivative observables,
calculated OPE coefficients, operator mixing, scheme dependence, and
perturbative remainders remain absent; no source-facing OS completed-tensor carrier, inhabitant, theory,
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
  /-- Exact action-compatible topological-group law on the affine Poincaré target. -/
  poincareTargetGroup : Minkowski.ProperOrthochronousPoincareTargetGroupData
    EuclideanDimension.four
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
  /-- Exact Gross–Wilczek one-loop normalization tied to the same gauge Lie algebra and the same
  invariant pairing used by the classical action. -/
  groupNormalizedOneLoopBeta : Renormalization.GroupNormalizedOneLoopBetaData
    inner asymptoticFreedom
  /-- Relative-to-designated-measure analytic action data on the same classical curvature chain. -/
  classicalAction : Classical.EuclideanActionAnalyticData
    (Classical.canonicalEuclideanSpacetimeMetricData EuclideanDimension.four)
    inner connection exterior curvatureCertificate
  /-- The designated action measure is coordinate Lebesgue measure on the exact canonical-flat
  `ℝ⁴` base. A general metric-induced-volume API bridge remains separate debt. -/
  classicalMeasure_eq_coordinateLebesgue : classicalAction.measure = MeasureTheory.volume
  /-- Reference-scale bridge: the outer coupling in this exact classical action is the value of the
  same running coupling whose one-loop coefficient is normalized above. -/
  classicalRunningCouplingReference :
    Renormalization.ClassicalRunningCouplingReferenceData
      asymptoticFreedom classicalAction.coupling
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
  /-- Corrected `(R0′)`, relative analytic, and exact-source Wick data together with universe-relative
  uniqueness across heterogeneous Hilbert realizations on the same exact lift. The selected
  Wightman surface and full
  correlator family are the exact fields above, not reconstructed copies. -/
  correctedOSIIReconstruction :
    Reconstruction.CorrectedOSIIReconstructionAcceptanceData
      schwingerFamily wightmanSurface fullCorrelators
  /-- One local-observable family on the same common invariant domain. -/
  observableFamily : Minkowski.TemperedLocalObservableFamilyData.{uLift, uH, uLabel} D
  /-- Adjoint closure, locality, and an explicit Lorentz-scalar label sector on that same family and
  representation chain. Stress-tensor labels use their separate rank-two covariance law. -/
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
  /-- The interpreted curvature-squared label belongs to the explicitly scalar-covariant sector. -/
  curvatureSquaredLabel_mem_scalar :
    curvatureSquaredInterpretation.quantumLabel .curvatureSquared ∈
      covariantObservableFamily.scalarLabel
  /-- The finite intrinsic scalar fragment `1`, `F²`, `(F²)²` extends that exact basic
  interpretation. Independent contractions and covariant derivatives remain absent. -/
  curvaturePowerInterpretation :
    Observables.ScalarCurvaturePowerLocalObservableInterpretationData
      (Classical.canonicalEuclideanSpacetimeMetricData EuclideanDimension.four)
      inner connection exterior curvatureCertificate observableFamily
      curvatureSquaredInterpretation
  /-- Explicit project anti-collapse strengthening: `(F²)²` is a genuinely new nontrivial operator.
  This is not inferred from Clay's renormalization footnote. -/
  curvatureQuarticAntiCollapse :
    Observables.CurvatureQuarticAntiCollapseData curvaturePowerInterpretation
  /-- The interpreted curvature-quartic label also belongs to the scalar-covariant sector. -/
  curvatureQuarticLabel_mem_scalar :
    curvaturePowerInterpretation.quantumLabel .curvatureQuartic ∈
      covariantObservableFamily.scalarLabel
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
  /-- Stress component labels are disjoint from the scalar-covariant label sector. -/
  stressCovarianceSeparation :
    Minkowski.ScalarStressCovarianceSeparationData covariantObservableFamily stressEnergy
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

/-- Corrected OS-II output growth selected by the reconstruction-acceptance package. -/
def wightmanLinearGrowth
    (data : FourDimensionalCurrentStrengthContinuumCoreAcceptanceData inner connection
      exterior curvatureCertificate fieldData) :
    Minkowski.OSIIWightmanLinearGrowthData data.fullCorrelators :=
  data.correctedOSIIReconstruction.selectedGrowth

/-- Relative analytic correlators selected by the reconstruction-acceptance package. -/
def relativeAnalyticCorrelators
    (data : FourDimensionalCurrentStrengthContinuumCoreAcceptanceData inner connection
      exterior curvatureCertificate fieldData) :
    Minkowski.ScalarWightmanRelativeAnalyticCorrelatorData data.fullCorrelators :=
  data.correctedOSIIReconstruction.selectedRelative

/-- Exact-source Wick coherence selected by the reconstruction-acceptance package. -/
def sourceWickCoherence
    (data : FourDimensionalCurrentStrengthContinuumCoreAcceptanceData inner connection
      exterior curvatureCertificate fieldData) :
    Reconstruction.OSSourceOrderedScalarWickContinuationData
      data.schwingerFamily data.relativeAnalyticCorrelators :=
  data.correctedOSIIReconstruction.selectedWick

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

/-- The exact existing representation/vacuum/domain/field/surface chain, bundled only for
transport and descent theorems. -/
def scalarWightmanAxiomChain
    (data : FourDimensionalCurrentStrengthContinuumCoreAcceptanceData inner connection
      exterior curvatureCertificate fieldData) :
    Minkowski.ScalarWightmanAxiomChainData EuclideanDimension.four lift H :=
  { U := U
    vacuumData := vacuumData
    D := D
    fieldData := fieldData
    surface := data.wightmanSurface }

/-- The exact scalar chain transported to the definitionally exact double-cover lift. -/
def scalarWightmanDoubleCoverChain
    (data : FourDimensionalCurrentStrengthContinuumCoreAcceptanceData inner connection
      exterior curvatureCertificate fieldData) :
    Minkowski.ScalarWightmanAxiomChainData EuclideanDimension.four
      data.poincareDoubleCover.toProperOrthochronousPoincareLiftData H :=
  data.scalarWightmanAxiomChain.transport data.poincareDoubleCover_toLift_eq.symm

/-- Strongly continuous scalar representation descended to the exact named affine Poincaré target. -/
noncomputable def descendedAffinePoincareUnitaryHom
    (data : FourDimensionalCurrentStrengthContinuumCoreAcceptanceData inner connection
      exterior curvatureCertificate fieldData) :
    letI : Group (Minkowski.ProperOrthochronousPoincareTransformation
      EuclideanDimension.four) := data.poincareTargetGroup.group
    Minkowski.ProperOrthochronousPoincareTransformation EuclideanDimension.four →*
      (H ≃ₗᵢ[ℂ] H) :=
  data.scalarWightmanDoubleCoverChain.descendedAffineUnitaryHom
    (targetGroup := data.poincareTargetGroup)

/-- Every exact cover lift recovers the original, untransported physical unitary. -/
theorem descendedAffinePoincareUnitary_projection
    (data : FourDimensionalCurrentStrengthContinuumCoreAcceptanceData inner connection
      exterior curvatureCertificate fieldData) (g : PoincareLiftGroup) :
    data.scalarWightmanDoubleCoverChain.descendedAffineUnitary
        (data.poincareDoubleCover.projection g) = U.unitary g := by
  calc
    data.scalarWightmanDoubleCoverChain.descendedAffineUnitary
        (data.poincareDoubleCover.projection g) =
      data.scalarWightmanDoubleCoverChain.U.unitary g :=
        data.scalarWightmanDoubleCoverChain.descendedAffineUnitary_projection
          data.poincareTargetGroup g
    _ = data.scalarWightmanAxiomChain.U.unitary g :=
      data.scalarWightmanAxiomChain.transport_unitary
        data.poincareDoubleCover_toLift_eq.symm g
    _ = U.unitary g := rfl

/-- On pure translations the descended affine action is the exact original physical translation
unitary tied to the joint PVM, stress tensor, and gap. -/
theorem descendedAffinePoincareUnitary_pureTranslation
    (data : FourDimensionalCurrentStrengthContinuumCoreAcceptanceData inner connection
      exterior curvatureCertificate fieldData)
    (a : EuclideanDimension.Spacetime EuclideanDimension.four) :
    data.scalarWightmanDoubleCoverChain.descendedAffineUnitary
        (Minkowski.ProperOrthochronousPoincareTransformation.pureTranslation
          EuclideanDimension.four a) = U.translationUnitary a := by
  let g := lift.translation (Multiplicative.ofAdd a)
  have projection_functions := congrArg
    (fun selected : Minkowski.ProperOrthochronousPoincareLiftData
      EuclideanDimension.four PoincareLiftGroup => selected.projection)
    data.poincareDoubleCover_toLift_eq
  have projection_eq : data.poincareDoubleCover.projection g =
      Minkowski.ProperOrthochronousPoincareTransformation.pureTranslation
        EuclideanDimension.four a := by
    rw [show data.poincareDoubleCover.projection = lift.projection from projection_functions]
    exact lift.projection_translation (Multiplicative.ofAdd a)
  rw [← projection_eq, data.descendedAffinePoincareUnitary_projection]
  rfl

/-- Descended affine unitary on the exact original common domain, with no cast-domain surrogate. -/
noncomputable def descendedAffineDomainUnitary
    (data : FourDimensionalCurrentStrengthContinuumCoreAcceptanceData inner connection
      exterior curvatureCertificate fieldData)
    (p : Minkowski.ProperOrthochronousPoincareTransformation EuclideanDimension.four) :
    D.domain ≃ₗᵢ[ℂ] D.domain :=
  data.scalarWightmanAxiomChain.descendedAffineDomainUnitaryOfLiftEq
    data.poincareDoubleCover_toLift_eq p

/-- The exact original scalar field has direct affine covariance on its original common domain. -/
theorem scalarField_covariant_descendedAffine
    (data : FourDimensionalCurrentStrengthContinuumCoreAcceptanceData inner connection
      exterior curvatureCertificate fieldData)
    (p : Minkowski.ProperOrthochronousPoincareTransformation EuclideanDimension.four)
    (f : Minkowski.ScalarMinkowskiSchwartzTestFunction EuclideanDimension.four)
    (ψ : D.domain) :
    data.descendedAffineDomainUnitary p
        (fieldData.field f ((data.descendedAffineDomainUnitary p).symm ψ)) =
      fieldData.field
        (Minkowski.pullbackScalarMinkowskiSchwartzTestFunction
          EuclideanDimension.four p f) ψ :=
  data.scalarWightmanAxiomChain.field_covariant_descendedAffineOfLiftEq
    data.poincareDoubleCover_toLift_eq p f ψ

/-- Every label in the exact original explicitly designated scalar local-observable sector has
direct affine covariance on the original domain. -/
theorem localObservable_covariant_descendedAffine
    (data : FourDimensionalCurrentStrengthContinuumCoreAcceptanceData inner connection
      exterior curvatureCertificate fieldData)
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
  data.covariantObservableFamily.operator_covariant_descendedAffineOfLiftEq
    data.scalarWightmanAxiomChain data.poincareDoubleCover_toLift_eq A hA p f ψ

/-- The descended affine representation is strongly continuous on every exact Hilbert vector. -/
theorem descendedAffinePoincareUnitary_stronglyContinuous
    (data : FourDimensionalCurrentStrengthContinuumCoreAcceptanceData inner connection
      exterior curvatureCertificate fieldData) (ψ : H) :
    Continuous (fun p : Minkowski.ProperOrthochronousPoincareTransformation
      EuclideanDimension.four =>
      data.scalarWightmanDoubleCoverChain.descendedAffineUnitary p ψ) :=
  data.scalarWightmanDoubleCoverChain.descendedAffineUnitary_stronglyContinuous
    data.poincareTargetGroup ψ

/-- Scalar covariance, exact vacuum invariance, and cyclicity force the derived negative cover sign
to act trivially on the exact four-dimensional physical Hilbert space. -/
theorem negativePoincareSign_unitary_eq_refl
    (data : FourDimensionalCurrentStrengthContinuumCoreAcceptanceData inner connection
      exterior curvatureCertificate fieldData) :
    U.unitary (Minkowski.negativeProjectionKernelElement EuclideanDimension.four
      data.poincareTargetGroup data.poincareDoubleCover : PoincareLiftGroup) =
      LinearIsometryEquiv.refl ℂ H :=
  data.scalarWightmanAxiomChain.negativeKernel_unitary_eq_refl_of_lift_eq
    data.poincareDoubleCover_toLift_eq

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
