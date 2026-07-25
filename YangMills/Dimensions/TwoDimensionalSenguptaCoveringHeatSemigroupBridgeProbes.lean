/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Dimensions.TwoDimensionalSenguptaCoveringHeatSemigroupBridge

/-! Hostile probes for the Sengupta covering heat-semigroup bridge. -/

namespace YangMills.Dimensions.TwoDimensionalSenguptaCoveringHeatSemigroupBridge.Probes

open MeasureTheory
open YangMills.Mathematics
open scoped ENNReal Manifold ContDiff BoundedContinuousFunction

noncomputable section

universe uG uCover uCoverE uGauge uSample uConnection uCurve uEdge uRegion uSenguptaSample

variable
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    {Gauge : Type uGauge} [Group Gauge]
    {Sample : Type uSample} [MeasurableSpace Sample]
    {Connection : Type uConnection}
    {base : TwoDimensionalGaugeFixedHolonomyMeasureData G Gauge Sample Connection}
    {law : TwoDimensionalSelectedLoopHaarDensityLawData base}
    {planarSemigroup : TwoDimensionalSelectedLoopConvolutionSemigroupData law}
    {CoverGroup : Type uCover} [Group CoverGroup]
    [TopologicalSpace CoverGroup] [IsTopologicalGroup CoverGroup]
    [CompactSpace CoverGroup] [T2Space CoverGroup]
    [MeasurableSpace CoverGroup] [BorelSpace CoverGroup]
    {Curve : Type uCurve} [Fintype Curve] [Nonempty Curve]
    {Edge : Type uEdge} [Fintype Edge] [DecidableEq Edge]
    {Region : Type uRegion} [Fintype Region] [DecidableEq Region]
    {SenguptaSample : Type uSenguptaSample} [MeasurableSpace SenguptaSample]
    {finiteLaw : TwoDimensionalSenguptaCompactSurfaceFiniteHolonomyLawData
      (G := G) (CoverGroup := CoverGroup) (Curve := Curve) (Edge := Edge)
      (Region := Region) (Sample := SenguptaSample)}
    {coverDensity : ℝ → CoverGroup → ℝ≥0∞}
    (bridge : TwoDimensionalSenguptaCoveringHeatSemigroupBridgeData
      (planarSemigroup := planarSemigroup) (finiteLaw := finiteLaw)
      (coverDensity := coverDensity))

variable
    [SecondCountableTopology CoverGroup]
    {CoverE : Type uCoverE} [NormedAddCommGroup CoverE] [NormedSpace ℝ CoverE]
    [ChartedSpace CoverE CoverGroup]
    [LieGroup (modelWithCornersSelf ℝ CoverE) ∞ CoverGroup]
    {coverInner : Geometry.InvariantInnerProductData
      (I := modelWithCornersSelf ℝ CoverE) (G := CoverGroup)}
    {coverLaplacian : RightInvariantPairingComplexLaplacianData coverInner}
    {coverHeatTrace : UnitaryMatrixDualHeatTraceSummabilityData (G := CoverGroup)}
    (coverLaplacianBridge : UnitaryMatrixDualCasimirLaplacianBridgeData
      coverInner coverLaplacian coverHeatTrace)
    (coverPositivity : UnitaryMatrixDualCasimirHeatPositivityData coverHeatTrace)
    (coverInitial : UnitaryMatrixDualCasimirHeatInitialIdentityData coverHeatTrace)
    (projectionHeat : NormalizedCompactHaarDensitySemigroupHomData
      (unitaryMatrixDualCasimirHeatDensitySemigroupData
        coverLaplacianBridge coverPositivity coverInitial)
      planarSemigroup.toNormalizedCompactHaarDensitySemigroupData finiteLaw.projection)

/-- The Casimir spectral chain discharges the covering semigroup field exactly; only the supplied
projection transport is retained. -/
noncomputable def exact_spectral_covering_bridge :
    TwoDimensionalSenguptaCoveringHeatSemigroupBridgeData
      (planarSemigroup := planarSemigroup) (finiteLaw := finiteLaw)
      (coverDensity := unitaryMatrixDualCasimirHeatDensityENNReal coverHeatTrace) :=
  TwoDimensionalSenguptaCoveringHeatSemigroupBridgeData.ofCasimirSpectral
    coverLaplacianBridge coverPositivity coverInitial projectionHeat

/-- Bounded-continuous real-test transport suffices for the exact spectral covering bridge. -/
noncomputable def exact_spectral_covering_bridge_of_integralTests
    [HasOuterApproxClosed G]
    (integralProjection : ∀ t : ℝ, 0 < t → ∀ f : G →ᵇ ℝ,
      (∫ g', f (finiteLaw.projection g')
        ∂normalizedCompactHaarDensitySemigroupMeasure
          (unitaryMatrixDualCasimirHeatDensityENNReal coverHeatTrace) t) =
      ∫ g, f g
        ∂normalizedCompactHaarDensitySemigroupMeasure law.selectedAreaDensity t) :
    TwoDimensionalSenguptaCoveringHeatSemigroupBridgeData
      (planarSemigroup := planarSemigroup) (finiteLaw := finiteLaw)
      (coverDensity := unitaryMatrixDualCasimirHeatDensityENNReal coverHeatTrace) :=
  TwoDimensionalSenguptaCoveringHeatSemigroupBridgeData.ofCasimirSpectralIntegralTests
    coverLaplacianBridge coverPositivity coverInitial integralProjection

include planarSemigroup coverLaplacianBridge coverPositivity coverInitial in
omit [Fintype Curve] [Nonempty Curve] [DecidableEq Edge] in
/-- Hostile extensionality probe: the integral-test constructor rejects a changed projected law. -/
theorem changed_spectral_projection_of_integralTests_blocked
    [HasOuterApproxClosed G]
    (integralProjection : ∀ t : ℝ, 0 < t → ∀ f : G →ᵇ ℝ,
      (∫ g', f (finiteLaw.projection g')
        ∂normalizedCompactHaarDensitySemigroupMeasure
          (unitaryMatrixDualCasimirHeatDensityENNReal coverHeatTrace) t) =
      ∫ g, f g
        ∂normalizedCompactHaarDensitySemigroupMeasure law.selectedAreaDensity t)
    {t : ℝ} (ht : 0 < t)
    (changed : Measure.map finiteLaw.projection
      (normalizedCompactHaarDensitySemigroupMeasure
        (unitaryMatrixDualCasimirHeatDensityENNReal coverHeatTrace) t) ≠
      normalizedCompactHaarDensitySemigroupMeasure law.selectedAreaDensity t) : False :=
  changed ((TwoDimensionalSenguptaCoveringHeatSemigroupBridgeData.ofCasimirSpectralIntegralTests
    (planarSemigroup := planarSemigroup) coverLaplacianBridge coverPositivity coverInitial integralProjection).map_coverMeasure ht)

/-- Selected physical Peter--Weyl density reduces covering transport to finite coefficient tests. -/
noncomputable def exact_spectral_covering_bridge_of_fourierCoefficients
    [T2Space G] [HasOuterApproxClosed G]
    (physicalDensity : UnitaryMatrixDual.HasContinuousPeterWeylDensity G)
    (coefficientIntegral : ∀ t : ℝ, 0 < t →
      ∀ A : UnitaryMatrixDualCoefficientSpace G,
        (∫ g', unitaryMatrixDualContinuousCoefficientSynthesis G A
            (finiteLaw.projection g')
          ∂normalizedCompactHaarDensitySemigroupMeasure
            (unitaryMatrixDualCasimirHeatDensityENNReal coverHeatTrace) t) =
        ∫ g, unitaryMatrixDualContinuousCoefficientSynthesis G A g
          ∂normalizedCompactHaarDensitySemigroupMeasure law.selectedAreaDensity t) :
    TwoDimensionalSenguptaCoveringHeatSemigroupBridgeData
      (planarSemigroup := planarSemigroup) (finiteLaw := finiteLaw)
      (coverDensity := unitaryMatrixDualCasimirHeatDensityENNReal coverHeatTrace) :=
  TwoDimensionalSenguptaCoveringHeatSemigroupBridgeData.ofCasimirSpectralFourierCoefficients
    coverLaplacianBridge coverPositivity coverInitial physicalDensity coefficientIntegral

include planarSemigroup coverLaplacianBridge coverPositivity coverInitial in
omit [Fintype Curve] [Nonempty Curve] [DecidableEq Edge] in
/-- Hostile Fourier-facing probe: changed measure transport is rejected after coefficient-density
extension. -/
theorem changed_spectral_projection_of_fourierCoefficients_blocked
    [T2Space G] [HasOuterApproxClosed G]
    (physicalDensity : UnitaryMatrixDual.HasContinuousPeterWeylDensity G)
    (coefficientIntegral : ∀ t : ℝ, 0 < t →
      ∀ A : UnitaryMatrixDualCoefficientSpace G,
        (∫ g', unitaryMatrixDualContinuousCoefficientSynthesis G A
            (finiteLaw.projection g')
          ∂normalizedCompactHaarDensitySemigroupMeasure
            (unitaryMatrixDualCasimirHeatDensityENNReal coverHeatTrace) t) =
        ∫ g, unitaryMatrixDualContinuousCoefficientSynthesis G A g
          ∂normalizedCompactHaarDensitySemigroupMeasure law.selectedAreaDensity t)
    {t : ℝ} (ht : 0 < t)
    (changed : Measure.map finiteLaw.projection
      (normalizedCompactHaarDensitySemigroupMeasure
        (unitaryMatrixDualCasimirHeatDensityENNReal coverHeatTrace) t) ≠
      normalizedCompactHaarDensitySemigroupMeasure law.selectedAreaDensity t) : False :=
  changed ((TwoDimensionalSenguptaCoveringHeatSemigroupBridgeData.ofCasimirSpectralFourierCoefficients
    (planarSemigroup := planarSemigroup) coverLaplacianBridge coverPositivity coverInitial
    physicalDensity coefficientIntegral).map_coverMeasure ht)

/-- One selected physical representation block at a time suffices after finite direct-sum
linearity. -/
noncomputable def exact_spectral_covering_bridge_of_fourierMatrixBlocks
    [T2Space G] [HasOuterApproxClosed G]
    (physicalDensity : UnitaryMatrixDual.HasContinuousPeterWeylDensity G)
    (blockIntegral : ∀ t : ℝ, 0 < t → ∀ q : UnitaryMatrixDual G,
      ∀ A : Matrix (Fin (unitaryMatrixDualDimension q))
        (Fin (unitaryMatrixDualDimension q)) ℂ,
        (∫ g', matrixCoefficientSynthesis (unitaryMatrixDualRepresentation q) A
            (finiteLaw.projection g')
          ∂normalizedCompactHaarDensitySemigroupMeasure
            (unitaryMatrixDualCasimirHeatDensityENNReal coverHeatTrace) t) =
        ∫ g, matrixCoefficientSynthesis (unitaryMatrixDualRepresentation q) A g
          ∂normalizedCompactHaarDensitySemigroupMeasure law.selectedAreaDensity t) :
    TwoDimensionalSenguptaCoveringHeatSemigroupBridgeData
      (planarSemigroup := planarSemigroup) (finiteLaw := finiteLaw)
      (coverDensity := unitaryMatrixDualCasimirHeatDensityENNReal coverHeatTrace) :=
  TwoDimensionalSenguptaCoveringHeatSemigroupBridgeData.ofCasimirSpectralFourierMatrixBlocks
    coverLaplacianBridge coverPositivity coverInitial physicalDensity blockIntegral

omit [T2Space CoverGroup] [Fintype Curve] [Nonempty Curve] [DecidableEq Edge]
    [SecondCountableTopology CoverGroup] in
/-- Hostile residual-debt probe: matrix-block compatibility remains explicit. -/
theorem missing_spectral_fourierMatrixBlocks_blocked
    [T2Space G] [HasOuterApproxClosed G]
    (blockIntegral : ∀ t : ℝ, 0 < t → ∀ q : UnitaryMatrixDual G,
      ∀ A : Matrix (Fin (unitaryMatrixDualDimension q))
        (Fin (unitaryMatrixDualDimension q)) ℂ,
        (∫ g', matrixCoefficientSynthesis (unitaryMatrixDualRepresentation q) A
            (finiteLaw.projection g')
          ∂normalizedCompactHaarDensitySemigroupMeasure
            (unitaryMatrixDualCasimirHeatDensityENNReal coverHeatTrace) t) =
        ∫ g, matrixCoefficientSynthesis (unitaryMatrixDualRepresentation q) A g
          ∂normalizedCompactHaarDensitySemigroupMeasure law.selectedAreaDensity t)
    (missing : ¬(∀ t : ℝ, 0 < t → ∀ q : UnitaryMatrixDual G,
      ∀ A : Matrix (Fin (unitaryMatrixDualDimension q))
        (Fin (unitaryMatrixDualDimension q)) ℂ,
        (∫ g', matrixCoefficientSynthesis (unitaryMatrixDualRepresentation q) A
            (finiteLaw.projection g')
          ∂normalizedCompactHaarDensitySemigroupMeasure
            (unitaryMatrixDualCasimirHeatDensityENNReal coverHeatTrace) t) =
        ∫ g, matrixCoefficientSynthesis (unitaryMatrixDualRepresentation q) A g
          ∂normalizedCompactHaarDensitySemigroupMeasure law.selectedAreaDensity t)) : False :=
  missing blockIntegral

/-- Raw row/column compatibility in each unchanged selected physical presentation suffices for the
spectral covering bridge. -/
noncomputable def exact_spectral_covering_bridge_of_fourierRawCoefficients
    [T2Space G] [HasOuterApproxClosed G]
    (physicalDensity : UnitaryMatrixDual.HasContinuousPeterWeylDensity G)
    (rawCoefficientIntegral : ∀ t : ℝ, 0 < t → ∀ q : UnitaryMatrixDual G,
      ∀ row column : Fin (unitaryMatrixDualDimension q),
        (∫ g', unitaryMatrixDualRepresentation q (finiteLaw.projection g') row column
          ∂normalizedCompactHaarDensitySemigroupMeasure
            (unitaryMatrixDualCasimirHeatDensityENNReal coverHeatTrace) t) =
        ∫ g, unitaryMatrixDualRepresentation q g row column
          ∂normalizedCompactHaarDensitySemigroupMeasure law.selectedAreaDensity t) :
    TwoDimensionalSenguptaCoveringHeatSemigroupBridgeData
      (planarSemigroup := planarSemigroup) (finiteLaw := finiteLaw)
      (coverDensity := unitaryMatrixDualCasimirHeatDensityENNReal coverHeatTrace) :=
  TwoDimensionalSenguptaCoveringHeatSemigroupBridgeData.ofCasimirSpectralFourierRawCoefficients
    coverLaplacianBridge coverPositivity coverInitial physicalDensity rawCoefficientIntegral

include projectionHeat in
omit [Fintype Curve] [Nonempty Curve] [DecidableEq Edge] in
/-- Hostile residual-debt probe: the spectral construction does not manufacture projection
compatibility. -/
theorem missing_spectral_projectionHeat_blocked
    (missing : ¬Nonempty (NormalizedCompactHaarDensitySemigroupHomData
      (unitaryMatrixDualCasimirHeatDensitySemigroupData
        coverLaplacianBridge coverPositivity coverInitial)
      planarSemigroup.toNormalizedCompactHaarDensitySemigroupData finiteLaw.projection)) : False :=
  missing ⟨projectionHeat⟩

omit [T2Space CoverGroup] [SecondCountableTopology CoverGroup]
    [Fintype Curve] [Nonempty Curve] [DecidableEq Edge] in
/-- The covering bridge inhabitance audit exposes both exact dependent witnesses. -/
theorem exact_covering_inhabitation_audit :
    Nonempty (TwoDimensionalSenguptaCoveringHeatSemigroupBridgeData
      (planarSemigroup := planarSemigroup) (finiteLaw := finiteLaw)
      (coverDensity := coverDensity)) ↔
    ∃ coverSemigroup : NormalizedCompactHaarDensitySemigroupData coverDensity,
      Nonempty (NormalizedCompactHaarDensitySemigroupHomData coverSemigroup
        planarSemigroup.toNormalizedCompactHaarDensitySemigroupData finiteLaw.projection) :=
  TwoDimensionalSenguptaCoveringHeatSemigroupBridgeData.nonempty_iff_coverSemigroup_projectionHeat

include bridge in
omit [T2Space CoverGroup] [SecondCountableTopology CoverGroup]
    [Fintype Curve] [Nonempty Curve] [DecidableEq Edge] in
/-- The exact finite-law projection transports the cover density measure at every positive time. -/
theorem exact_cover_measure_pushforward {t : ℝ} (ht : 0 < t) :
    Measure.map finiteLaw.projection
        (normalizedCompactHaarDensitySemigroupMeasure coverDensity t) =
      normalizedCompactHaarDensitySemigroupMeasure law.selectedAreaDensity t :=
  bridge.map_coverMeasure ht

include bridge in
omit [T2Space CoverGroup] [SecondCountableTopology CoverGroup]
    [Fintype Curve] [Nonempty Curve] [DecidableEq Edge] in
/-- Hostile covering-heat probe: a changed projected law is rejected. -/
theorem changed_cover_measure_blocked
    {t : ℝ} (ht : 0 < t)
    (changed : Measure.map finiteLaw.projection
        (normalizedCompactHaarDensitySemigroupMeasure coverDensity t) ≠
      normalizedCompactHaarDensitySemigroupMeasure law.selectedAreaDensity t) : False :=
  changed (bridge.map_coverMeasure ht)

include bridge in
omit [T2Space CoverGroup] [SecondCountableTopology CoverGroup]
    [Fintype Curve] [Nonempty Curve] [DecidableEq Edge] in
/-- Positive-time cover and planar measures are both normalized and nonzero. -/
theorem exact_both_positive_time_probability {t : ℝ} (ht : 0 < t) :
    normalizedCompactHaarDensitySemigroupMeasure coverDensity t Set.univ = 1 ∧
    normalizedCompactHaarDensitySemigroupMeasure coverDensity t ≠ 0 ∧
    normalizedCompactHaarDensitySemigroupMeasure law.selectedAreaDensity t Set.univ = 1 ∧
    normalizedCompactHaarDensitySemigroupMeasure law.selectedAreaDensity t ≠ 0 :=
  ⟨bridge.coverSemigroup.measure_univ ht, bridge.coverSemigroup.measure_ne_zero ht,
    planarSemigroup.toNormalizedCompactHaarDensitySemigroupData.measure_univ ht,
    planarSemigroup.toNormalizedCompactHaarDensitySemigroupData.measure_ne_zero ht⟩

end

end YangMills.Dimensions.TwoDimensionalSenguptaCoveringHeatSemigroupBridge.Probes
