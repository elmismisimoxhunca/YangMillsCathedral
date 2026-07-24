/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Dimensions.TwoDimensionalSelectedLoopPairingGraphCoreGenerator
import YangMills.Mathematics.SmoothUnitaryMatrixCoefficientCasimirLaplacianBridge
import YangMills.Mathematics.UnitaryMatrixDualCasimirHeatMatrixCoefficientGenerator

/-!
# Selected-loop generator on the smooth matrix-coefficient range

The complex spectral heat operator acts diagonally on every explicit irreducible matrix coefficient.
This file transports that result to both real components of the exact generated selected-loop heat
operator, proves the right-hand zero-time generator on every finite real matrix-coefficient
synthesis, and fills the `core_generator` obligation for the resulting range, conditional only on
the explicit coefficientwise Casimir/Laplacian bridge.

A final reduction record retains exactly the still-unproved coefficientwise Casimir bridge, smooth
graph density, and eventual uniform graph bound. It does not construct any of these fields, assert
coverage of the continuous unitary dual by smooth representatives, or extend the generator to all
smooth tests without the graph-core hypotheses.
-/

namespace YangMills
namespace Dimensions

open Filter MeasureTheory ProbabilityTheory
open YangMills.Mathematics
open scoped Manifold ContDiff Topology

noncomputable section

universe uE uG uGauge uSample uConnection uΩ

variable
    {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G] [MeasurableMul₂ G] [MeasurableInv G]
    [ChartedSpace E G] [LieGroup (modelWithCornersSelf ℝ E) ∞ G]
    {Gauge : Type uGauge} [Group Gauge]
    {Sample : Type uSample} [MeasurableSpace Sample]
    {Connection : Type uConnection}
    {Ω : Type uΩ} [MeasurableSpace Ω]
    {inner : Geometry.InvariantInnerProductData
      (I := modelWithCornersSelf ℝ E) (G := G)}
    {base : TwoDimensionalGaugeFixedHolonomyMeasureData G Gauge Sample Connection}
    {law : TwoDimensionalSelectedLoopHaarDensityLawData base}
    {realLaplacian : RightInvariantPairingLaplacianData inner}
    {complexLaplacian : RightInvariantPairingComplexLaplacianData inner}
    {heatTraceData : UnitaryMatrixDualHeatTraceSummabilityData (G := G)}

omit [FiniteDimensional ℝ E] [MeasurableMul₂ G] [MeasurableInv G] in
/-- The real selected-loop heat operator acts diagonally on either real component of every explicit
smooth irreducible matrix coefficient. -/
theorem twoDimensionalSelectedLoopHeatOperator_smoothMatrixCoefficient
    (bridge : TwoDimensionalSelectedLoopSpectralBrownianGeneratorBridgeData
      (law := law) (inner := inner) (realLaplacian := realLaplacian)
      (complexLaplacian := complexLaplacian) (heatTraceData := heatTraceData) (Ω := Ω))
    (t : ℝ) (ht : 0 < t)
    (index : SmoothUnitaryMatrixCoefficientRealIndex E G) :
    bridge.spectralHeatKernel.kernelOperator.heatOperator t
        (smoothLieGroupScalarToContinuousLinearMap
          (smoothUnitaryMatrixCoefficientRealFunction index)) =
      Real.exp (-(t / 2) * heatTraceData.casimirWeight
        (unitaryMatrixDualClass
          index.representation.toContinuousUnitaryIrreducibleMatrixRepresentation)) •
        smoothLieGroupScalarToContinuousLinearMap
          (smoothUnitaryMatrixCoefficientRealFunction index) := by
  rcases index with ⟨ρs, row, column, component⟩
  let ρ := ρs.toContinuousUnitaryIrreducibleMatrixRepresentation
  let coefficient : C(G, ℂ) := continuousMatrixRepresentationCoefficient ρ.representation
    ρ.continuous_representation row column
  have integrableCoefficientKernel (g : G) : Integrable (fun h : G => coefficient h *
      unitaryMatrixDualCasimirHeatCharacterSeries heatTraceData t (h⁻¹ * g))
      (normalizedCompactHaarMeasure G) := by
    letI : IsProbabilityMeasure (normalizedCompactHaarMeasure G) :=
      normalizedCompactHaarMeasure_isProbability G
    have continuousIntegrand : Continuous (fun h : G => coefficient h *
        unitaryMatrixDualCasimirHeatCharacterSeries heatTraceData t (h⁻¹ * g)) := by
      fun_prop
    simpa only [integrableOn_univ] using
      continuousIntegrand.continuousOn.integrableOn_compact
        (μ := normalizedCompactHaarMeasure G) isCompact_univ
  ext g
  cases component with
  | real =>
      rw [bridge.spectralHeatKernel.kernelOperator.heatOperator_eq_kernelIntegral t ht]
      change (∫ h, unitaryMatrixDualCasimirHeatDensityReal heatTraceData t (h⁻¹ * g) *
        (coefficient h).re ∂normalizedCompactHaarMeasure G) =
        Real.exp (-(t / 2) * heatTraceData.casimirWeight (unitaryMatrixDualClass ρ)) *
          (coefficient g).re
      have eigenaction := unitaryMatrixDualCasimirHeatComplexOperator_matrixCoefficient
        heatTraceData t ht ρ row column
      have pointEigenaction := congrArg (fun F : C(G, ℂ) => (F g).re) eigenaction
      rw [unitaryMatrixDualCasimirHeatComplexOperator,
        normalizedCompactHaarContinuousConvolution_apply] at pointEigenaction
      have pointEigenaction' :
          (normalizedCompactHaarComplexConvolution G coefficient
            (unitaryMatrixDualCasimirHeatCharacterSeries heatTraceData t) g).re =
          Real.exp (-(t / 2) * heatTraceData.casimirWeight (unitaryMatrixDualClass ρ)) *
            (coefficient g).re := by
        calc
          _ = (((Real.exp (-(t / 2) * heatTraceData.casimirWeight
              (unitaryMatrixDualClass ρ)) : ℂ) • coefficient) g).re := pointEigenaction
          _ = _ := by
            simp only [ContinuousMap.smul_apply, smul_eq_mul, Complex.mul_re,
              Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
      rw [← pointEigenaction', normalizedCompactHaarComplexConvolution_apply]
      calc
        _ = ∫ h, (coefficient h * unitaryMatrixDualCasimirHeatCharacterSeries
              heatTraceData t (h⁻¹ * g)).re ∂normalizedCompactHaarMeasure G := by
          apply integral_congr_ae
          filter_upwards [] with h
          rw [unitaryMatrixDualCasimirHeatCharacterSeries_eq_densityReal heatTraceData
            bridge.spectralHeatKernel.heatEquationBridge.spectralDensityBridge.positivity ht]
          simp [Complex.mul_re]
          ring
        _ = _ := integral_re (integrableCoefficientKernel g)
  | imaginary =>
      rw [bridge.spectralHeatKernel.kernelOperator.heatOperator_eq_kernelIntegral t ht]
      change (∫ h, unitaryMatrixDualCasimirHeatDensityReal heatTraceData t (h⁻¹ * g) *
        (coefficient h).im ∂normalizedCompactHaarMeasure G) =
        Real.exp (-(t / 2) * heatTraceData.casimirWeight (unitaryMatrixDualClass ρ)) *
          (coefficient g).im
      have eigenaction := unitaryMatrixDualCasimirHeatComplexOperator_matrixCoefficient
        heatTraceData t ht ρ row column
      have pointEigenaction := congrArg (fun F : C(G, ℂ) => (F g).im) eigenaction
      rw [unitaryMatrixDualCasimirHeatComplexOperator,
        normalizedCompactHaarContinuousConvolution_apply] at pointEigenaction
      have pointEigenaction' :
          (normalizedCompactHaarComplexConvolution G coefficient
            (unitaryMatrixDualCasimirHeatCharacterSeries heatTraceData t) g).im =
          Real.exp (-(t / 2) * heatTraceData.casimirWeight (unitaryMatrixDualClass ρ)) *
            (coefficient g).im := by
        calc
          _ = (((Real.exp (-(t / 2) * heatTraceData.casimirWeight
              (unitaryMatrixDualClass ρ)) : ℂ) • coefficient) g).im := pointEigenaction
          _ = _ := by
            simp only [ContinuousMap.smul_apply, smul_eq_mul, Complex.mul_im,
              Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
      rw [← pointEigenaction', normalizedCompactHaarComplexConvolution_apply]
      calc
        _ = ∫ h, (coefficient h * unitaryMatrixDualCasimirHeatCharacterSeries
              heatTraceData t (h⁻¹ * g)).im ∂normalizedCompactHaarMeasure G := by
          apply integral_congr_ae
          filter_upwards [] with h
          rw [unitaryMatrixDualCasimirHeatCharacterSeries_eq_densityReal heatTraceData
            bridge.spectralHeatKernel.heatEquationBridge.spectralDensityBridge.positivity ht]
          simp [Complex.mul_im]
          ring
        _ = _ := integral_im (integrableCoefficientKernel g)

omit [FiniteDimensional ℝ E] [MeasurableMul₂ G] [MeasurableInv G] in
/-- With the explicit coefficientwise Casimir bridge, every real matrix-coefficient component has
the exact right-hand selected-loop generator in uniform norm. -/
theorem tendsto_twoDimensionalSelectedLoop_smoothMatrixCoefficient_generator
    (bridge : TwoDimensionalSelectedLoopSpectralBrownianGeneratorBridgeData
      (law := law) (inner := inner) (realLaplacian := realLaplacian)
      (complexLaplacian := complexLaplacian) (heatTraceData := heatTraceData) (Ω := Ω))
    (casimirBridge : SmoothUnitaryMatrixCoefficientCasimirLaplacianBridgeData
      inner complexLaplacian heatTraceData)
    (index : SmoothUnitaryMatrixCoefficientRealIndex E G) :
    Tendsto (fun t : NNReal =>
      twoDimensionalSelectedLoopHeatDifferenceQuotientLinearMap bridge t
        (smoothLieGroupScalarToContinuousLinearMap
          (smoothUnitaryMatrixCoefficientRealFunction index)))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (twoDimensionalSelectedLoopPairingGeneratorLinearMap
        (realLaplacian := realLaplacian)
        (smoothUnitaryMatrixCoefficientRealFunction index))) := by
  let f : C(G, ℝ) := smoothLieGroupScalarToContinuousLinearMap
    (smoothUnitaryMatrixCoefficientRealFunction index)
  let q := unitaryMatrixDualClass
    index.representation.toContinuousUnitaryIrreducibleMatrixRepresentation
  have scalarLimit := tendsto_unitaryMatrixDualCasimirHeatEigenvalue_slope_zero heatTraceData q
  have functionLimit := scalarLimit.smul_const f
  have targetEquality : (-(heatTraceData.casimirWeight q / 2)) • f =
      twoDimensionalSelectedLoopPairingGeneratorLinearMap
        (realLaplacian := realLaplacian)
        (smoothUnitaryMatrixCoefficientRealFunction index) := by
    ext g
    rw [twoDimensionalSelectedLoopPairingGeneratorLinearMap_apply]
    rw [SmoothUnitaryMatrixCoefficientCasimirLaplacianBridgeData.laplacian_smoothRealCoefficient
      realLaplacian complexLaplacian casimirBridge index g]
    simp [f, q]
    ring
  rw [← targetEquality]
  apply functionLimit.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  have positiveTime : 0 < (t : ℝ) := by exact_mod_cast ht
  have nonzeroTime : (t : ℝ) ≠ 0 := ne_of_gt positiveTime
  rw [twoDimensionalSelectedLoopHeatDifferenceQuotientLinearMap_apply bridge t ht f]
  rw [twoDimensionalSelectedLoopHeatOperator_smoothMatrixCoefficient
    bridge (t : ℝ) positiveTime index]
  ext g
  simp only [ContinuousMap.smul_apply, ContinuousMap.sub_apply, smul_eq_mul]
  dsimp [q, f]
  field_simp [nonzeroTime]

omit [FiniteDimensional ℝ E] [MeasurableMul₂ G] [MeasurableInv G] in
/-- Finite linearity upgrades the component theorem to every finite real smooth matrix-coefficient
synthesis. -/
theorem tendsto_twoDimensionalSelectedLoop_smoothMatrixCoefficientSynthesis_generator
    (bridge : TwoDimensionalSelectedLoopSpectralBrownianGeneratorBridgeData
      (law := law) (inner := inner) (realLaplacian := realLaplacian)
      (complexLaplacian := complexLaplacian) (heatTraceData := heatTraceData) (Ω := Ω))
    (casimirBridge : SmoothUnitaryMatrixCoefficientCasimirLaplacianBridgeData
      inner complexLaplacian heatTraceData)
    (coefficients : SmoothUnitaryMatrixCoefficientRealCoefficients E G) :
    Tendsto (fun t : NNReal =>
      twoDimensionalSelectedLoopHeatDifferenceQuotientLinearMap bridge t
        (smoothLieGroupScalarToContinuousLinearMap
          (smoothUnitaryMatrixCoefficientRealSynthesis coefficients)))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (twoDimensionalSelectedLoopPairingGeneratorLinearMap
        (realLaplacian := realLaplacian)
        (smoothUnitaryMatrixCoefficientRealSynthesis coefficients))) := by
  classical
  induction coefficients using Finsupp.induction with
  | zero =>
      simp
  | @single_add index coefficient coefficients hindex hcoefficient induction =>
      have componentLimit :=
        tendsto_twoDimensionalSelectedLoop_smoothMatrixCoefficient_generator
          bridge casimirBridge index
      have scaledLimit := componentLimit.const_smul coefficient
      have combinedLimit := scaledLimit.add induction
      simpa [smoothUnitaryMatrixCoefficientRealSynthesis] using combinedLimit

omit [FiniteDimensional ℝ E] [MeasurableMul₂ G] [MeasurableInv G] in
/-- The finite real smooth matrix-coefficient range therefore satisfies the exact `core_generator`
field of the generic graph-core reduction. -/
theorem twoDimensionalSelectedLoop_smoothMatrixCoefficientCore_generator
    (bridge : TwoDimensionalSelectedLoopSpectralBrownianGeneratorBridgeData
      (law := law) (inner := inner) (realLaplacian := realLaplacian)
      (complexLaplacian := complexLaplacian) (heatTraceData := heatTraceData) (Ω := Ω))
    (casimirBridge : SmoothUnitaryMatrixCoefficientCasimirLaplacianBridgeData
      inner complexLaplacian heatTraceData) :
    ∀ f ∈ smoothUnitaryMatrixCoefficientRealCoreCandidate (E := E) (G := G),
      Tendsto (fun t : NNReal =>
        twoDimensionalSelectedLoopHeatDifferenceQuotientLinearMap bridge t
          (smoothLieGroupScalarToContinuousLinearMap f))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (twoDimensionalSelectedLoopPairingGeneratorLinearMap
          (realLaplacian := realLaplacian) f)) := by
  intro f hf
  obtain ⟨coefficients, rfl⟩ := hf
  exact tendsto_twoDimensionalSelectedLoop_smoothMatrixCoefficientSynthesis_generator
    bridge casimirBridge coefficients

/-- Exact remaining obligations after selecting the finite real smooth matrix-coefficient range and
proving its generator convergence. -/
structure TwoDimensionalSelectedLoopSmoothMatrixCoefficientGraphCoreData
    (bridge : TwoDimensionalSelectedLoopSpectralBrownianGeneratorBridgeData
      (law := law) (inner := inner) (realLaplacian := realLaplacian)
      (complexLaplacian := complexLaplacian) (heatTraceData := heatTraceData) (Ω := Ω)) where
  coefficientCasimirBridge : SmoothUnitaryMatrixCoefficientCasimirLaplacianBridgeData
    inner complexLaplacian heatTraceData
  graphDense : IsLinearMapDomainGraphDenseCore
    smoothLieGroupScalarToContinuousLinearMap
    (twoDimensionalSelectedLoopPairingGeneratorLinearMap
      (realLaplacian := realLaplacian))
    (smoothUnitaryMatrixCoefficientRealCoreCandidate (E := E) (G := G))
  graphBoundConstant : ℝ
  graphBoundConstant_nonneg : 0 ≤ graphBoundConstant
  eventual_graphBound : ∀ᶠ t : NNReal in nhdsWithin 0 (Set.Ioi 0),
    ∀ f : SmoothLieGroupScalarFunction (E := E) (G := G),
      ‖twoDimensionalSelectedLoopHeatDifferenceQuotientLinearMap bridge t
          (smoothLieGroupScalarToContinuousLinearMap f)‖ ≤
        graphBoundConstant *
          (‖smoothLieGroupScalarToContinuousLinearMap f‖ +
            ‖twoDimensionalSelectedLoopPairingGeneratorLinearMap
              (realLaplacian := realLaplacian) f‖)

namespace TwoDimensionalSelectedLoopSmoothMatrixCoefficientGraphCoreData

/-- The coefficient-specific remaining data canonically fills the generic graph-core record; its
core convergence field is now derived rather than caller supplied. -/
noncomputable def toPairingGraphCoreGeneratorData
    {bridge : TwoDimensionalSelectedLoopSpectralBrownianGeneratorBridgeData
      (law := law) (inner := inner) (realLaplacian := realLaplacian)
      (complexLaplacian := complexLaplacian) (heatTraceData := heatTraceData) (Ω := Ω)}
    (data : TwoDimensionalSelectedLoopSmoothMatrixCoefficientGraphCoreData bridge) :
    TwoDimensionalSelectedLoopPairingGraphCoreGeneratorData bridge where
  core := smoothUnitaryMatrixCoefficientRealCoreCandidate
  graphDense := data.graphDense
  graphBoundConstant := data.graphBoundConstant
  graphBoundConstant_nonneg := data.graphBoundConstant_nonneg
  eventual_graphBound := data.eventual_graphBound
  core_generator := twoDimensionalSelectedLoop_smoothMatrixCoefficientCore_generator
    bridge data.coefficientCasimirBridge

/-- The reduced coefficient-specific obligations imply the existing all-smooth stochastic generator
endpoint. -/
noncomputable def toStochasticGeneratorAtZeroData
    {bridge : TwoDimensionalSelectedLoopSpectralBrownianGeneratorBridgeData
      (law := law) (inner := inner) (realLaplacian := realLaplacian)
      (complexLaplacian := complexLaplacian) (heatTraceData := heatTraceData) (Ω := Ω)}
    (data : TwoDimensionalSelectedLoopSmoothMatrixCoefficientGraphCoreData bridge) :
    TwoDimensionalSelectedLoopStochasticGeneratorAtZeroData bridge :=
  data.toPairingGraphCoreGeneratorData.toStochasticGeneratorAtZeroData

end TwoDimensionalSelectedLoopSmoothMatrixCoefficientGraphCoreData

end

end Dimensions
end YangMills
