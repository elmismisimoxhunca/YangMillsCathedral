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
synthesis, and fills the `core_generator` obligation for the resulting range. Positive-time heat
differentiation derives the required real pairing-Laplacian eigenvalue inside the same spectral chain,
so the separate generic complex coefficient bridge is not assumed here.

A final reduction record retains exactly smooth graph density and the eventual uniform graph bound.
It does not construct either field, assert
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

/-- Finite real synthesis with each explicit matrix coordinate multiplied by its exact Casimir
heat eigenvalue. -/
noncomputable def twoDimensionalSelectedLoopSmoothMatrixCoefficientHeatEvolution
    (t : ℝ) : SmoothUnitaryMatrixCoefficientRealCoefficients E G →ₗ[ℝ]
      SmoothLieGroupScalarFunction (E := E) (G := G) :=
  Finsupp.linearCombination ℝ (fun index =>
    Real.exp (-(t / 2) * heatTraceData.casimirWeight
      (unitaryMatrixDualClass
        index.representation.toContinuousUnitaryIrreducibleMatrixRepresentation)) •
      smoothUnitaryMatrixCoefficientRealFunction index)

omit [FiniteDimensional ℝ E] [MeasurableMul₂ G] [MeasurableInv G] in
/-- Exact positive-time heat action on every finite real smooth matrix-coefficient synthesis. -/
theorem twoDimensionalSelectedLoopHeatOperator_smoothMatrixCoefficientSynthesis
    (bridge : TwoDimensionalSelectedLoopSpectralBrownianGeneratorBridgeData
      (law := law) (inner := inner) (realLaplacian := realLaplacian)
      (complexLaplacian := complexLaplacian) (heatTraceData := heatTraceData) (Ω := Ω))
    (t : ℝ) (ht : 0 < t)
    (coefficients : SmoothUnitaryMatrixCoefficientRealCoefficients E G) :
    bridge.spectralHeatKernel.kernelOperator.heatOperator t
        (smoothLieGroupScalarToContinuousLinearMap
          (smoothUnitaryMatrixCoefficientRealSynthesis coefficients)) =
      smoothLieGroupScalarToContinuousLinearMap
        (twoDimensionalSelectedLoopSmoothMatrixCoefficientHeatEvolution
          (heatTraceData := heatTraceData) t coefficients) := by
  let heatMap := twoDimensionalSelectedLoopPositiveHeatOperatorLinearMap bridge t ht
  have mapEquality :
      heatMap.comp ((smoothLieGroupScalarToContinuousLinearMap (E := E) (G := G)).comp
        (smoothUnitaryMatrixCoefficientRealSynthesis (E := E) (G := G))) =
      (smoothLieGroupScalarToContinuousLinearMap (E := E) (G := G)).comp
        (twoDimensionalSelectedLoopSmoothMatrixCoefficientHeatEvolution
          (E := E) (G := G) (heatTraceData := heatTraceData) t) := by
    apply Finsupp.lhom_ext
    intro index coefficient
    simp only [LinearMap.comp_apply, smoothUnitaryMatrixCoefficientRealSynthesis,
      twoDimensionalSelectedLoopSmoothMatrixCoefficientHeatEvolution,
      Finsupp.linearCombination_single]
    change heatMap (coefficient • smoothLieGroupScalarToContinuousLinearMap
      (smoothUnitaryMatrixCoefficientRealFunction index)) =
      coefficient • smoothLieGroupScalarToContinuousLinearMap
        (Real.exp (-(t / 2) * heatTraceData.casimirWeight
          (unitaryMatrixDualClass
            index.representation.toContinuousUnitaryIrreducibleMatrixRepresentation)) •
          smoothUnitaryMatrixCoefficientRealFunction index)
    rw [map_smul, map_smul]
    congr 1
    change bridge.spectralHeatKernel.kernelOperator.heatOperator t
      (smoothLieGroupScalarToContinuousLinearMap
        (smoothUnitaryMatrixCoefficientRealFunction index)) = _
    rw [twoDimensionalSelectedLoopHeatOperator_smoothMatrixCoefficient bridge t ht index]
  exact LinearMap.congr_fun mapEquality coefficients

omit [FiniteDimensional ℝ E] [MeasurableMul₂ G] [MeasurableInv G] in
/-- Positive-time heat differentiation and the exact diagonal heat action force the real pairing-
Laplacian Casimir equation for every smooth matrix-coefficient component. This derives the equation
inside the selected-loop spectral chain without assuming the separate generic complex coefficient
bridge. -/
theorem twoDimensionalSelectedLoop_smoothMatrixCoefficient_laplacian
    (bridge : TwoDimensionalSelectedLoopSpectralBrownianGeneratorBridgeData
      (law := law) (inner := inner) (realLaplacian := realLaplacian)
      (complexLaplacian := complexLaplacian) (heatTraceData := heatTraceData) (Ω := Ω))
    (index : SmoothUnitaryMatrixCoefficientRealIndex E G) (g : G) :
    realLaplacian.laplacian (smoothUnitaryMatrixCoefficientRealFunction index) g =
      -(heatTraceData.casimirWeight (unitaryMatrixDualClass
        index.representation.toContinuousUnitaryIrreducibleMatrixRepresentation)) *
        smoothUnitaryMatrixCoefficientRealFunction index g := by
  let f := smoothUnitaryMatrixCoefficientRealFunction index
  let q := unitaryMatrixDualClass
    index.representation.toContinuousUnitaryIrreducibleMatrixRepresentation
  let t : ℝ := 1
  have ht : 0 < t := by norm_num [t]
  let eigen : ℝ := Real.exp (-(t / 2) * heatTraceData.casimirWeight q)
  have smoothEquality :
      TwoDimensionalSelectedLoopHeatKernelOperatorData.positiveTimeSmooth
        bridge.spectralHeatKernel.kernelOperator t ht
          (smoothLieGroupScalarToContinuousLinearMap f) = eigen • f := by
    ext x
    rw [TwoDimensionalSelectedLoopHeatKernelOperatorData.positiveTimeSmooth_apply
      bridge.spectralHeatKernel.kernelOperator]
    have action := twoDimensionalSelectedLoopHeatOperator_smoothMatrixCoefficient
      bridge t ht index
    have pointAction := congrArg (fun F : C(G, ℝ) => F x) action
    simpa [f, q, eigen] using pointAction
  have storedDerivative :=
    TwoDimensionalSelectedLoopHeatKernelOperatorData.heatOperator_hasDerivAt
      bridge.spectralHeatKernel.kernelOperator t ht
        (smoothLieGroupScalarToContinuousLinearMap f) g
  rw [smoothEquality] at storedDerivative
  rw [RightInvariantScalarDerivativeSmoothnessData.pairingLaplacian_smul
    realLaplacian rightInvariantScalarDerivativeSmoothnessData] at storedDerivative
  have scalarDerivative : HasDerivAt
      (fun s : ℝ => Real.exp (-(s / 2) * heatTraceData.casimirWeight q) * f g)
      (-(heatTraceData.casimirWeight q / 2) * eigen * f g) t := by
    have innerDerivative : HasDerivAt
        (fun s : ℝ => -(s / 2) * heatTraceData.casimirWeight q)
        (-(heatTraceData.casimirWeight q / 2)) t := by
      have raw := (((hasDerivAt_id t).div_const 2).neg.mul_const
        (heatTraceData.casimirWeight q))
      have transformed : HasDerivAt
          (fun s : ℝ => -(s / 2) * heatTraceData.casimirWeight q)
          (-(1 / 2) * heatTraceData.casimirWeight q) t := by
        apply raw.congr_of_eventuallyEq
        filter_upwards [] with s
        simp only [Function.id_def, Pi.neg_apply]
      exact transformed.congr_deriv (by ring)
    have raw := innerDerivative.exp.mul_const (f g)
    exact raw.congr_deriv (by dsimp [eigen]; ring)
  have eventualPositive : ∀ᶠ s : ℝ in nhds t, 0 < s :=
    isOpen_Ioi.eventually_mem ht
  have trajectoryEquality :
      (fun s : ℝ => bridge.spectralHeatKernel.kernelOperator.heatOperator s
        (smoothLieGroupScalarToContinuousLinearMap f) g) =ᶠ[nhds t]
      (fun s : ℝ => Real.exp (-(s / 2) * heatTraceData.casimirWeight q) * f g) := by
    filter_upwards [eventualPositive] with s hs
    have action := twoDimensionalSelectedLoopHeatOperator_smoothMatrixCoefficient
      bridge s hs index
    have pointAction := congrArg (fun F : C(G, ℝ) => F g) action
    simpa [f, q] using pointAction
  have scalarDerivativeOnHeat :=
    scalarDerivative.congr_of_eventuallyEq trajectoryEquality
  have derivativeEquality := storedDerivative.unique scalarDerivativeOnHeat
  have eigenPositive : 0 < eigen := Real.exp_pos _
  dsimp [q, f] at derivativeEquality ⊢
  nlinarith

omit [FiniteDimensional ℝ E] [MeasurableMul₂ G] [MeasurableInv G] in
/-- The same-chain real and imaginary eigenvalue equations, together with canonical same-pairing
real/complex coherence, construct the previously explicit generic complex coefficientwise Casimir
bridge for this spectral selected-loop chain. -/
noncomputable def twoDimensionalSelectedLoopCoefficientCasimirLaplacianBridgeData
    (bridge : TwoDimensionalSelectedLoopSpectralBrownianGeneratorBridgeData
      (law := law) (inner := inner) (realLaplacian := realLaplacian)
      (complexLaplacian := complexLaplacian) (heatTraceData := heatTraceData) (Ω := Ω)) :
    SmoothUnitaryMatrixCoefficientCasimirLaplacianBridgeData
      inner complexLaplacian heatTraceData where
  coefficient_laplacian := by
    intro ρ row column g
    let coefficient := smoothUnitaryMatrixCoefficient ρ row column
    let coherence := rightInvariantPairingRealComplexLaplacianCoherenceData
      realLaplacian complexLaplacian
    apply Complex.ext
    · rw [← coherence.laplacian_realPart coefficient g]
      have realEquation := twoDimensionalSelectedLoop_smoothMatrixCoefficient_laplacian
        bridge ⟨ρ, row, column, .real⟩ g
      simpa [coefficient, smoothUnitaryMatrixCoefficientRealFunction, Complex.mul_re] using
        realEquation
    · rw [← coherence.laplacian_imaginaryPart coefficient g]
      have imaginaryEquation := twoDimensionalSelectedLoop_smoothMatrixCoefficient_laplacian
        bridge ⟨ρ, row, column, .imaginary⟩ g
      simpa [coefficient, smoothUnitaryMatrixCoefficientRealFunction, Complex.mul_im] using
        imaginaryEquation

omit [FiniteDimensional ℝ E] [MeasurableMul₂ G] [MeasurableInv G] in
/-- Every real matrix-coefficient component has the exact right-hand selected-loop generator in
uniform norm. The pairing-Laplacian identification is now derived from the same spectral heat chain,
not supplied by the generic coefficientwise bridge. -/
theorem tendsto_twoDimensionalSelectedLoop_smoothMatrixCoefficient_generator
    (bridge : TwoDimensionalSelectedLoopSpectralBrownianGeneratorBridgeData
      (law := law) (inner := inner) (realLaplacian := realLaplacian)
      (complexLaplacian := complexLaplacian) (heatTraceData := heatTraceData) (Ω := Ω))
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
    rw [twoDimensionalSelectedLoop_smoothMatrixCoefficient_laplacian bridge index g]
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
          bridge index
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
    : ∀ f ∈ smoothUnitaryMatrixCoefficientRealCoreCandidate (E := E) (G := G),
      Tendsto (fun t : NNReal =>
        twoDimensionalSelectedLoopHeatDifferenceQuotientLinearMap bridge t
          (smoothLieGroupScalarToContinuousLinearMap f))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (twoDimensionalSelectedLoopPairingGeneratorLinearMap
          (realLaplacian := realLaplacian) f)) := by
  intro f hf
  obtain ⟨coefficients, rfl⟩ := hf
  exact tendsto_twoDimensionalSelectedLoop_smoothMatrixCoefficientSynthesis_generator
    bridge coefficients

/-- Exact remaining obligations after selecting the finite real smooth matrix-coefficient range,
deriving its real pairing-Laplacian eigenvalues, and proving its generator convergence. -/
structure TwoDimensionalSelectedLoopSmoothMatrixCoefficientGraphCoreData
    (bridge : TwoDimensionalSelectedLoopSpectralBrownianGeneratorBridgeData
      (law := law) (inner := inner) (realLaplacian := realLaplacian)
      (complexLaplacian := complexLaplacian) (heatTraceData := heatTraceData) (Ω := Ω)) where
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

omit [FiniteDimensional ℝ E] [MeasurableMul₂ G] [MeasurableInv G] in
/-- Exact inhabitance audit: after the derived coefficient Laplacian and core convergence, the
coefficient-specific record is inhabited precisely by smooth graph density together with one
nonnegative eventual graph-bound constant. -/
theorem nonempty_iff_graphDense_and_eventualGraphBound
    {bridge : TwoDimensionalSelectedLoopSpectralBrownianGeneratorBridgeData
      (law := law) (inner := inner) (realLaplacian := realLaplacian)
      (complexLaplacian := complexLaplacian) (heatTraceData := heatTraceData) (Ω := Ω)} :
    Nonempty (TwoDimensionalSelectedLoopSmoothMatrixCoefficientGraphCoreData bridge) ↔
      IsLinearMapDomainGraphDenseCore
        smoothLieGroupScalarToContinuousLinearMap
        (twoDimensionalSelectedLoopPairingGeneratorLinearMap
          (realLaplacian := realLaplacian))
        (smoothUnitaryMatrixCoefficientRealCoreCandidate (E := E) (G := G)) ∧
      ∃ C : ℝ, 0 ≤ C ∧
        ∀ᶠ t : NNReal in nhdsWithin 0 (Set.Ioi 0),
          ∀ f : SmoothLieGroupScalarFunction (E := E) (G := G),
            ‖twoDimensionalSelectedLoopHeatDifferenceQuotientLinearMap bridge t
                (smoothLieGroupScalarToContinuousLinearMap f)‖ ≤
              C * (‖smoothLieGroupScalarToContinuousLinearMap f‖ +
                ‖twoDimensionalSelectedLoopPairingGeneratorLinearMap
                  (realLaplacian := realLaplacian) f‖) := by
  constructor
  · rintro ⟨data⟩
    exact ⟨data.graphDense, data.graphBoundConstant,
      data.graphBoundConstant_nonneg, data.eventual_graphBound⟩
  · rintro ⟨graphDense, C, hC, graphBound⟩
    exact ⟨{
      graphDense := graphDense
      graphBoundConstant := C
      graphBoundConstant_nonneg := hC
      eventual_graphBound := graphBound }⟩

/-- The coefficient-specific remaining data canonically fills the generic graph-core record; both its
core convergence and coefficient Laplacian identification are now derived rather than caller supplied. -/
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
  core_generator := twoDimensionalSelectedLoop_smoothMatrixCoefficientCore_generator bridge

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
