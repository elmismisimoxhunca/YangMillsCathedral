/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Dimensions.TwoDimensionalSelectedLoopPairingGraphCoreGenerator
import YangMills.Mathematics.SmoothUnitaryMatrixCoefficientCasimirLaplacianBridge
import YangMills.Mathematics.SmoothUnitaryMatrixCoefficientSelectedRealification
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

omit [FiniteDimensional ℝ E] [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    [MeasurableMul₂ G] [MeasurableInv G]
    [LieGroup (modelWithCornersSelf ℝ E) ∞ G] in
/-- Finite coefficientwise heat evolution remains in the same algebraic smooth core. -/
theorem twoDimensionalSelectedLoopSmoothMatrixCoefficientHeatEvolution_mem_coreCandidate
    (t : ℝ) (coefficients : SmoothUnitaryMatrixCoefficientRealCoefficients E G) :
    twoDimensionalSelectedLoopSmoothMatrixCoefficientHeatEvolution
      (heatTraceData := heatTraceData) t coefficients ∈
      smoothUnitaryMatrixCoefficientRealCoreCandidate (E := E) (G := G) := by
  classical
  induction coefficients using Finsupp.induction with
  | zero =>
      rw [map_zero]
      change (0 : SmoothLieGroupScalarFunction (E := E) (G := G)) ∈
        smoothUnitaryMatrixCoefficientRealCoreSubmodule (E := E) (G := G)
      exact (smoothUnitaryMatrixCoefficientRealCoreSubmodule (E := E) (G := G)).zero_mem
  | @single_add index coefficient coefficients hindex hcoefficient induction =>
      rw [map_add]
      apply (smoothUnitaryMatrixCoefficientRealCoreSubmodule (E := E) (G := G)).add_mem
      · simp only [twoDimensionalSelectedLoopSmoothMatrixCoefficientHeatEvolution,
          Finsupp.linearCombination_single]
        apply (smoothUnitaryMatrixCoefficientRealCoreSubmodule (E := E) (G := G)).smul_mem
        apply (smoothUnitaryMatrixCoefficientRealCoreSubmodule (E := E) (G := G)).smul_mem
        exact smoothUnitaryMatrixCoefficientRealFunction_mem_coreCandidate index
      · exact induction

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

/-- Total coefficient-space form of the selected-loop heat difference quotient. The zero branch
matches the totalized ambient `NNReal` family and is irrelevant on `Ioi 0`. -/
noncomputable def twoDimensionalSelectedLoopSmoothMatrixCoefficientDifferenceQuotientEvolution
    (t : NNReal) : SmoothUnitaryMatrixCoefficientRealCoefficients E G →ₗ[ℝ]
      SmoothLieGroupScalarFunction (E := E) (G := G) :=
  if _ht : 0 < t then
    ((t : ℝ)⁻¹) •
      (twoDimensionalSelectedLoopSmoothMatrixCoefficientHeatEvolution
        (E := E) (G := G) (heatTraceData := heatTraceData) (t : ℝ) -
        smoothUnitaryMatrixCoefficientRealSynthesis)
  else 0

omit [FiniteDimensional ℝ E] [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    [MeasurableMul₂ G] [MeasurableInv G]
    [LieGroup (modelWithCornersSelf ℝ E) ∞ G] in
@[simp]
theorem twoDimensionalSelectedLoopSmoothMatrixCoefficientDifferenceQuotientEvolution_zero :
    twoDimensionalSelectedLoopSmoothMatrixCoefficientDifferenceQuotientEvolution
      (E := E) (G := G) (heatTraceData := heatTraceData) 0 = 0 := by
  unfold twoDimensionalSelectedLoopSmoothMatrixCoefficientDifferenceQuotientEvolution
  rw [dif_neg]
  simp

omit [FiniteDimensional ℝ E] [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    [MeasurableMul₂ G] [MeasurableInv G]
    [LieGroup (modelWithCornersSelf ℝ E) ∞ G] in
/-- Exact positive-time coefficient-space difference quotient. -/
theorem twoDimensionalSelectedLoopSmoothMatrixCoefficientDifferenceQuotientEvolution_apply
    (t : NNReal) (ht : 0 < t)
    (coefficients : SmoothUnitaryMatrixCoefficientRealCoefficients E G) :
    twoDimensionalSelectedLoopSmoothMatrixCoefficientDifferenceQuotientEvolution
        (E := E) (G := G) (heatTraceData := heatTraceData) t coefficients =
      ((t : ℝ)⁻¹) •
        (twoDimensionalSelectedLoopSmoothMatrixCoefficientHeatEvolution
            (heatTraceData := heatTraceData) (t : ℝ) coefficients -
          smoothUnitaryMatrixCoefficientRealSynthesis coefficients) := by
  unfold twoDimensionalSelectedLoopSmoothMatrixCoefficientDifferenceQuotientEvolution
  rw [dif_pos ht]
  rfl

omit [FiniteDimensional ℝ E] [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    [MeasurableMul₂ G] [MeasurableInv G]
    [LieGroup (modelWithCornersSelf ℝ E) ∞ G] in
/-- Every positive coefficient-space heat difference quotient remains in the same algebraic smooth
core. -/
theorem twoDimensionalSelectedLoopSmoothMatrixCoefficientDifferenceQuotientEvolution_mem_coreCandidate
    (t : NNReal) (ht : 0 < t)
    (coefficients : SmoothUnitaryMatrixCoefficientRealCoefficients E G) :
    twoDimensionalSelectedLoopSmoothMatrixCoefficientDifferenceQuotientEvolution
      (heatTraceData := heatTraceData) t coefficients ∈
      smoothUnitaryMatrixCoefficientRealCoreCandidate (E := E) (G := G) := by
  rw [twoDimensionalSelectedLoopSmoothMatrixCoefficientDifferenceQuotientEvolution_apply
    t ht coefficients]
  change ((t : ℝ)⁻¹) •
      (twoDimensionalSelectedLoopSmoothMatrixCoefficientHeatEvolution
          (heatTraceData := heatTraceData) (t : ℝ) coefficients -
        smoothUnitaryMatrixCoefficientRealSynthesis coefficients) ∈
    smoothUnitaryMatrixCoefficientRealCoreSubmodule (E := E) (G := G)
  apply (smoothUnitaryMatrixCoefficientRealCoreSubmodule (E := E) (G := G)).smul_mem
  apply (smoothUnitaryMatrixCoefficientRealCoreSubmodule (E := E) (G := G)).sub_mem
  · exact twoDimensionalSelectedLoopSmoothMatrixCoefficientHeatEvolution_mem_coreCandidate
      (heatTraceData := heatTraceData) (t : ℝ) coefficients
  · exact ⟨coefficients, rfl⟩

omit [FiniteDimensional ℝ E] [MeasurableMul₂ G] [MeasurableInv G] in
/-- The ambient selected-loop difference quotient on a finite coefficient synthesis is exactly the
continuous realization of the coefficient-space difference quotient. -/
theorem twoDimensionalSelectedLoopHeatDifferenceQuotient_smoothMatrixCoefficientSynthesis
    (bridge : TwoDimensionalSelectedLoopSpectralBrownianGeneratorBridgeData
      (law := law) (inner := inner) (realLaplacian := realLaplacian)
      (complexLaplacian := complexLaplacian) (heatTraceData := heatTraceData) (Ω := Ω))
    (t : NNReal) (ht : 0 < t)
    (coefficients : SmoothUnitaryMatrixCoefficientRealCoefficients E G) :
    twoDimensionalSelectedLoopHeatDifferenceQuotientLinearMap bridge t
        (smoothLieGroupScalarToContinuousLinearMap
          (smoothUnitaryMatrixCoefficientRealSynthesis coefficients)) =
      smoothLieGroupScalarToContinuousLinearMap
        (twoDimensionalSelectedLoopSmoothMatrixCoefficientDifferenceQuotientEvolution
          (heatTraceData := heatTraceData) t coefficients) := by
  rw [twoDimensionalSelectedLoopHeatDifferenceQuotientLinearMap_apply bridge t ht]
  rw [twoDimensionalSelectedLoopHeatOperator_smoothMatrixCoefficientSynthesis
    bridge (t : ℝ) (by exact_mod_cast ht) coefficients]
  rw [twoDimensionalSelectedLoopSmoothMatrixCoefficientDifferenceQuotientEvolution_apply
    t ht coefficients]
  rw [map_smul, map_sub]

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

omit [FiniteDimensional ℝ E] [MeasurableMul₂ G] [MeasurableInv G] in
/-- Generator convergence and the exact quotient identity make the total continuous-linear heat
semigroup strongly right-continuous at zero on every test in the finite coefficient core. This does
not claim strong continuity on all of `C(G, ℝ)`. -/
theorem twoDimensionalSelectedLoop_smoothMatrixCoefficientCore_heatOperator_tendsto_zero
    (bridge : TwoDimensionalSelectedLoopSpectralBrownianGeneratorBridgeData
      (law := law) (inner := inner) (realLaplacian := realLaplacian)
      (complexLaplacian := complexLaplacian) (heatTraceData := heatTraceData) (Ω := Ω))
    (f : SmoothLieGroupScalarFunction (E := E) (G := G))
    (hf : f ∈ smoothUnitaryMatrixCoefficientRealCoreCandidate (E := E) (G := G)) :
    Tendsto (fun t : NNReal =>
      twoDimensionalSelectedLoopHeatOperatorContinuousLinearMap bridge t
        (smoothLieGroupScalarToContinuousLinearMap f))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (smoothLieGroupScalarToContinuousLinearMap f)) := by
  have hcoe : Tendsto (fun t : NNReal => (t : ℝ))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    change Tendsto NNReal.toReal (nhdsWithin 0 (Set.Ioi 0))
      (nhds ((0 : NNReal) : ℝ))
    exact NNReal.continuous_coe.continuousAt.mono_left inf_le_left
  have hquotient :=
    twoDimensionalSelectedLoop_smoothMatrixCoefficientCore_generator bridge f hf
  have hscaled : Tendsto (fun t : NNReal =>
      (t : ℝ) • twoDimensionalSelectedLoopHeatDifferenceQuotientLinearMap bridge t
        (smoothLieGroupScalarToContinuousLinearMap f))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    simpa using hcoe.smul hquotient
  have hadd : Tendsto (fun t : NNReal =>
      smoothLieGroupScalarToContinuousLinearMap f +
        (t : ℝ) • twoDimensionalSelectedLoopHeatDifferenceQuotientLinearMap bridge t
          (smoothLieGroupScalarToContinuousLinearMap f))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (smoothLieGroupScalarToContinuousLinearMap f)) := by
    simpa only [add_zero] using tendsto_const_nhds.add hscaled
  apply hadd.congr'
  filter_upwards [] with t
  exact (twoDimensionalSelectedLoopHeatOperator_eq_add_smul_differenceQuotient
    bridge t (smoothLieGroupScalarToContinuousLinearMap f)).symm

omit [FiniteDimensional ℝ E] [MeasurableMul₂ G] [MeasurableInv G] in
/-- Contractivity extends strong right-continuity from the finite coefficient core to its uniform-
norm closure in `C(G, ℝ)`. Reaching every continuous function still requires a separate uniform
density theorem for this selected smooth coefficient family. -/
theorem twoDimensionalSelectedLoop_smoothMatrixCoefficientCore_heatOperator_tendsto_zero_of_mem_closure
    (bridge : TwoDimensionalSelectedLoopSpectralBrownianGeneratorBridgeData
      (law := law) (inner := inner) (realLaplacian := realLaplacian)
      (complexLaplacian := complexLaplacian) (heatTraceData := heatTraceData) (Ω := Ω))
    (f : C(G, ℝ))
    (hf : f ∈ closure
      (smoothLieGroupScalarToContinuousLinearMap ''
        smoothUnitaryMatrixCoefficientRealCoreCandidate (E := E) (G := G))) :
    Tendsto (fun t : NNReal =>
      twoDimensionalSelectedLoopHeatOperatorContinuousLinearMap bridge t f)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds f) := by
  apply tendsto_continuousLinearMap_id_of_mem_closure_of_contraction
    (twoDimensionalSelectedLoopHeatOperatorContinuousLinearMap bridge)
    (smoothLieGroupScalarToContinuousLinearMap ''
      smoothUnitaryMatrixCoefficientRealCoreCandidate (E := E) (G := G))
  · exact Filter.Eventually.of_forall fun t h =>
      twoDimensionalSelectedLoopHeatOperatorContinuousLinearMap_apply_norm_le bridge t h
  · intro h hh
    obtain ⟨coreTest, hcoreTest, rfl⟩ := hh
    exact twoDimensionalSelectedLoop_smoothMatrixCoefficientCore_heatOperator_tendsto_zero
      bridge coreTest hcoreTest
  · exact hf

omit [FiniteDimensional ℝ E] [MeasurableMul₂ G] [MeasurableInv G] in
/-- A future uniform Peter–Weyl density theorem for the selected smooth coefficient image would
upgrade the contraction semigroup to strong right-continuity at zero on every continuous function.
The density premise remains explicit and is not inferred from the spectral bridge. -/
theorem twoDimensionalSelectedLoop_smoothMatrixCoefficientCore_heatOperator_tendsto_zero_of_dense
    (bridge : TwoDimensionalSelectedLoopSpectralBrownianGeneratorBridgeData
      (law := law) (inner := inner) (realLaplacian := realLaplacian)
      (complexLaplacian := complexLaplacian) (heatTraceData := heatTraceData) (Ω := Ω))
    (dense : Dense
      (smoothLieGroupScalarToContinuousLinearMap ''
        smoothUnitaryMatrixCoefficientRealCoreCandidate (E := E) (G := G))) :
    ∀ f : C(G, ℝ), Tendsto (fun t : NNReal =>
      twoDimensionalSelectedLoopHeatOperatorContinuousLinearMap bridge t f)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds f) := by
  intro f
  apply
    twoDimensionalSelectedLoop_smoothMatrixCoefficientCore_heatOperator_tendsto_zero_of_mem_closure
      bridge f
  rw [dense.closure_eq]
  exact Set.mem_univ f

omit [FiniteDimensional ℝ E] [MeasurableMul₂ G] [MeasurableInv G] in
/-- Selected continuous Peter--Weyl density and explicit smooth-dual coverage construct the exact
uniform-density premise above, hence strong right-continuity at zero on every continuous test. -/
theorem twoDimensionalSelectedLoop_heatOperator_tendsto_zero_of_continuousPeterWeyl_of_smoothCoverage
    (bridge : TwoDimensionalSelectedLoopSpectralBrownianGeneratorBridgeData
      (law := law) (inner := inner) (realLaplacian := realLaplacian)
      (complexLaplacian := complexLaplacian) (heatTraceData := heatTraceData) (Ω := Ω))
    (continuousDensity : UnitaryMatrixDual.HasContinuousPeterWeylDensity G)
    (smoothCoverage : ∀ q : UnitaryMatrixDual G,
      q.HasSmoothRepresentative (E := E)) :
    ∀ f : C(G, ℝ), Tendsto (fun t : NNReal =>
      twoDimensionalSelectedLoopHeatOperatorContinuousLinearMap bridge t f)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds f) :=
  twoDimensionalSelectedLoop_smoothMatrixCoefficientCore_heatOperator_tendsto_zero_of_dense
    bridge (smoothUnitaryMatrixCoefficientRealCore_continuousImage_dense
      continuousDensity smoothCoverage)

omit [FiniteDimensional ℝ E] [MeasurableMul₂ G] [MeasurableInv G] in
/-- Automatic smoothness of all bundled continuous irreducible unitary coordinates discharges the
smooth-coverage premise in the Fourier-to-semigroup bridge. -/
theorem twoDimensionalSelectedLoop_heatOperator_tendsto_zero_of_continuousPeterWeyl_of_automaticSmoothness
    (bridge : TwoDimensionalSelectedLoopSpectralBrownianGeneratorBridgeData
      (law := law) (inner := inner) (realLaplacian := realLaplacian)
      (complexLaplacian := complexLaplacian) (heatTraceData := heatTraceData) (Ω := Ω))
    (continuousDensity : UnitaryMatrixDual.HasContinuousPeterWeylDensity G)
    (automaticSmoothness :
      AllContinuousUnitaryIrreducibleMatrixRepresentationsHaveSmoothCoordinates
        (E := E) (G := G)) :
    ∀ f : C(G, ℝ), Tendsto (fun t : NNReal =>
      twoDimensionalSelectedLoopHeatOperatorContinuousLinearMap bridge t f)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds f) :=
  twoDimensionalSelectedLoop_heatOperator_tendsto_zero_of_continuousPeterWeyl_of_smoothCoverage
    bridge continuousDensity
      (all_unitaryMatrixDual_hasSmoothRepresentative_of_all_hasSmoothCoordinates
        automaticSmoothness)

omit [FiniteDimensional ℝ E] [MeasurableMul₂ G] [MeasurableInv G] in
/-- Faithful compact matrix coordinates discharge the continuous density premise; smooth-dual
coverage remains explicit. -/
theorem twoDimensionalSelectedLoop_heatOperator_tendsto_zero_of_faithful_of_smoothCoverage
    (bridge : TwoDimensionalSelectedLoopSpectralBrownianGeneratorBridgeData
      (law := law) (inner := inner) (realLaplacian := realLaplacian)
      (complexLaplacian := complexLaplacian) (heatTraceData := heatTraceData) (Ω := Ω))
    (faithful : ContinuousFaithfulFiniteMatrixRepresentation G)
    (smoothCoverage : ∀ q : UnitaryMatrixDual G,
      q.HasSmoothRepresentative (E := E)) :
    ∀ f : C(G, ℝ), Tendsto (fun t : NNReal =>
      twoDimensionalSelectedLoopHeatOperatorContinuousLinearMap bridge t f)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds f) :=
  twoDimensionalSelectedLoop_smoothMatrixCoefficientCore_heatOperator_tendsto_zero_of_dense
    bridge (smoothUnitaryMatrixCoefficientRealCore_continuousImage_dense_of_faithful
      faithful smoothCoverage)

omit [FiniteDimensional ℝ E] [MeasurableMul₂ G] [MeasurableInv G] in
/-- Faithful finite matrix coordinates and automatic smoothness together imply strong right-
continuity at zero on every continuous test. -/
theorem twoDimensionalSelectedLoop_heatOperator_tendsto_zero_of_faithful_of_automaticSmoothness
    (bridge : TwoDimensionalSelectedLoopSpectralBrownianGeneratorBridgeData
      (law := law) (inner := inner) (realLaplacian := realLaplacian)
      (complexLaplacian := complexLaplacian) (heatTraceData := heatTraceData) (Ω := Ω))
    (faithful : ContinuousFaithfulFiniteMatrixRepresentation G)
    (automaticSmoothness :
      AllContinuousUnitaryIrreducibleMatrixRepresentationsHaveSmoothCoordinates
        (E := E) (G := G)) :
    ∀ f : C(G, ℝ), Tendsto (fun t : NNReal =>
      twoDimensionalSelectedLoopHeatOperatorContinuousLinearMap bridge t f)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds f) :=
  twoDimensionalSelectedLoop_heatOperator_tendsto_zero_of_faithful_of_smoothCoverage
    bridge faithful
      (all_unitaryMatrixDual_hasSmoothRepresentative_of_all_hasSmoothCoordinates
        automaticSmoothness)

omit [FiniteDimensional ℝ E] [MeasurableMul₂ G] [MeasurableInv G] in
/-- Smooth graph density alone extends strong right-continuity of the contraction semigroup from the
coefficient core to every smooth test. The separate uniform graph bound is still required for
all-smooth generator convergence, not for this zeroth-order continuity statement. -/
theorem twoDimensionalSelectedLoop_smoothMatrixCoefficientCore_heatOperator_tendsto_zero_of_graphDense
    (bridge : TwoDimensionalSelectedLoopSpectralBrownianGeneratorBridgeData
      (law := law) (inner := inner) (realLaplacian := realLaplacian)
      (complexLaplacian := complexLaplacian) (heatTraceData := heatTraceData) (Ω := Ω))
    (graphDense : IsLinearMapDomainGraphDenseCore
      smoothLieGroupScalarToContinuousLinearMap
      (twoDimensionalSelectedLoopPairingGeneratorLinearMap
        (realLaplacian := realLaplacian))
      (smoothUnitaryMatrixCoefficientRealCoreCandidate (E := E) (G := G)))
    (f : SmoothLieGroupScalarFunction (E := E) (G := G)) :
    Tendsto (fun t : NNReal =>
      twoDimensionalSelectedLoopHeatOperatorContinuousLinearMap bridge t
        (smoothLieGroupScalarToContinuousLinearMap f))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (smoothLieGroupScalarToContinuousLinearMap f)) := by
  have hclosure : smoothLieGroupScalarToContinuousLinearMap f ∈ closure
      (smoothLieGroupScalarToContinuousLinearMap ''
        smoothUnitaryMatrixCoefficientRealCoreCandidate (E := E) (G := G)) :=
    IsLinearMapDomainGraphDenseAt.mem_closure_image
      (𝕜 := ℝ)
      (D := SmoothLieGroupScalarFunction (E := E) (G := G))
      (X := C(G, ℝ))
      smoothLieGroupScalarToContinuousLinearMap
      (twoDimensionalSelectedLoopPairingGeneratorLinearMap
        (realLaplacian := realLaplacian))
      (smoothUnitaryMatrixCoefficientRealCoreCandidate (E := E) (G := G)) f
      (graphDense f)
  exact
    twoDimensionalSelectedLoop_smoothMatrixCoefficientCore_heatOperator_tendsto_zero_of_mem_closure
      bridge (smoothLieGroupScalarToContinuousLinearMap f) hclosure

omit [FiniteDimensional ℝ E] [MeasurableMul₂ G] [MeasurableInv G] in
/-- Core convergence supplies an eventual norm bound separately for each finite coefficient test.
The quantifiers are deliberately pointwise in `f`; this is strictly weaker than the single uniform
all-domain graph bound required below. -/
theorem twoDimensionalSelectedLoop_smoothMatrixCoefficientCore_eventually_pointwiseNormBound
    (bridge : TwoDimensionalSelectedLoopSpectralBrownianGeneratorBridgeData
      (law := law) (inner := inner) (realLaplacian := realLaplacian)
      (complexLaplacian := complexLaplacian) (heatTraceData := heatTraceData) (Ω := Ω))
    (f : SmoothLieGroupScalarFunction (E := E) (G := G))
    (hf : f ∈ smoothUnitaryMatrixCoefficientRealCoreCandidate (E := E) (G := G)) :
    ∀ᶠ t : NNReal in nhdsWithin 0 (Set.Ioi 0),
      ‖twoDimensionalSelectedLoopHeatDifferenceQuotientLinearMap bridge t
          (smoothLieGroupScalarToContinuousLinearMap f)‖ ≤
        ‖twoDimensionalSelectedLoopPairingGeneratorLinearMap
          (realLaplacian := realLaplacian) f‖ + 1 :=
  eventually_norm_le_norm_add_one_of_tendsto
    (twoDimensionalSelectedLoop_smoothMatrixCoefficientCore_generator bridge f hf)

omit [FiniteDimensional ℝ E] [MeasurableMul₂ G] [MeasurableInv G] in
/-- The core therefore satisfies a graph-relative bound in the weaker pointwise quantifier order:
each fixed test has its own nonnegative constant and eventual set. This does not commute those
quantifiers into the uniform field required by the graph-core reduction. -/
theorem twoDimensionalSelectedLoop_smoothMatrixCoefficientCore_exists_eventually_pointwiseGraphBound
    (bridge : TwoDimensionalSelectedLoopSpectralBrownianGeneratorBridgeData
      (law := law) (inner := inner) (realLaplacian := realLaplacian)
      (complexLaplacian := complexLaplacian) (heatTraceData := heatTraceData) (Ω := Ω))
    (f : SmoothLieGroupScalarFunction (E := E) (G := G))
    (hf : f ∈ smoothUnitaryMatrixCoefficientRealCoreCandidate (E := E) (G := G)) :
    ∃ Cf : ℝ, 0 ≤ Cf ∧ ∀ᶠ t : NNReal in nhdsWithin 0 (Set.Ioi 0),
      ‖twoDimensionalSelectedLoopHeatDifferenceQuotientLinearMap bridge t
          (smoothLieGroupScalarToContinuousLinearMap f)‖ ≤
        Cf * (‖smoothLieGroupScalarToContinuousLinearMap f‖ +
          ‖twoDimensionalSelectedLoopPairingGeneratorLinearMap
            (realLaplacian := realLaplacian) f‖) :=
  exists_eventually_pointwise_graphBound_of_tendsto
    (𝕜 := ℝ)
    (D := SmoothLieGroupScalarFunction (E := E) (G := G))
    (X := C(G, ℝ)) (ι := NNReal) (l := nhdsWithin 0 (Set.Ioi 0))
    smoothLieGroupScalarToContinuousLinearMap
    (twoDimensionalSelectedLoopPairingGeneratorLinearMap
      (realLaplacian := realLaplacian))
    (twoDimensionalSelectedLoopHeatDifferenceQuotientLinearMap bridge) f
    (twoDimensionalSelectedLoop_smoothMatrixCoefficientCore_generator bridge f hf)

/-- Exact unit-interval Duhamel identity for the selected pairing generator. This proposition does
not include integrability or claim that the identity follows from the stored positive-time heat
equation. -/
def TwoDimensionalSelectedLoopPairingDuhamelIdentity
    (bridge : TwoDimensionalSelectedLoopSpectralBrownianGeneratorBridgeData
      (law := law) (inner := inner) (realLaplacian := realLaplacian)
      (complexLaplacian := complexLaplacian) (heatTraceData := heatTraceData) (Ω := Ω)) : Prop :=
  ∀ (t : NNReal), 0 < t →
    ∀ f : SmoothLieGroupScalarFunction (E := E) (G := G),
      twoDimensionalSelectedLoopHeatDifferenceQuotientLinearMap bridge t
          (smoothLieGroupScalarToContinuousLinearMap f) =
        ∫ s : ℝ in 0..1,
          twoDimensionalSelectedLoopHeatOperatorContinuousLinearMap bridge
            (Real.toNNReal s * t)
            (twoDimensionalSelectedLoopPairingGeneratorLinearMap
              (realLaplacian := realLaplacian) f)

/-- Proof-local semigroup-analytic Duhamel strengthening for the right heat difference quotient on
the full smooth domain. It requires genuine interval integrability and identifies the quotient with
the unit-interval average of the total contraction semigroup applied to the pairing generator. This
is not quoted from Driver Remark 4.13 and no such datum is asserted without a witness. -/
structure TwoDimensionalSelectedLoopPairingDuhamelData
    (bridge : TwoDimensionalSelectedLoopSpectralBrownianGeneratorBridgeData
      (law := law) (inner := inner) (realLaplacian := realLaplacian)
      (complexLaplacian := complexLaplacian) (heatTraceData := heatTraceData) (Ω := Ω)) where
  trajectory_intervalIntegrable : ∀ (t : NNReal),
    ∀ f : SmoothLieGroupScalarFunction (E := E) (G := G),
      IntervalIntegrable (fun s : ℝ =>
        twoDimensionalSelectedLoopHeatOperatorContinuousLinearMap bridge
          (Real.toNNReal s * t)
          (twoDimensionalSelectedLoopPairingGeneratorLinearMap
            (realLaplacian := realLaplacian) f)) volume 0 1
  duhamel : TwoDimensionalSelectedLoopPairingDuhamelIdentity bridge

namespace TwoDimensionalSelectedLoopPairingDuhamelData

omit [FiniteDimensional ℝ E] [MeasurableMul₂ G] [MeasurableInv G] in
/-- Duhamel plus heat contraction gives the sharp all-domain quotient bound by the pairing generator. -/
theorem quotient_norm_le_generator
    {bridge : TwoDimensionalSelectedLoopSpectralBrownianGeneratorBridgeData
      (law := law) (inner := inner) (realLaplacian := realLaplacian)
      (complexLaplacian := complexLaplacian) (heatTraceData := heatTraceData) (Ω := Ω)}
    (data : TwoDimensionalSelectedLoopPairingDuhamelData bridge)
    (t : NNReal) (ht : 0 < t)
    (f : SmoothLieGroupScalarFunction (E := E) (G := G)) :
    ‖twoDimensionalSelectedLoopHeatDifferenceQuotientLinearMap bridge t
        (smoothLieGroupScalarToContinuousLinearMap f)‖ ≤
      ‖twoDimensionalSelectedLoopPairingGeneratorLinearMap
        (realLaplacian := realLaplacian) f‖ := by
  rw [data.duhamel t ht f]
  calc
    ‖∫ s : ℝ in 0..1,
        twoDimensionalSelectedLoopHeatOperatorContinuousLinearMap bridge
          (Real.toNNReal s * t)
          (twoDimensionalSelectedLoopPairingGeneratorLinearMap
            (realLaplacian := realLaplacian) f)‖
        ≤ ‖twoDimensionalSelectedLoopPairingGeneratorLinearMap
            (realLaplacian := realLaplacian) f‖ * |1 - 0| :=
      intervalIntegral.norm_integral_le_of_norm_le_const (fun s _ =>
        twoDimensionalSelectedLoopHeatOperatorContinuousLinearMap_apply_norm_le
          bridge (Real.toNNReal s * t)
          (twoDimensionalSelectedLoopPairingGeneratorLinearMap
            (realLaplacian := realLaplacian) f))
    _ = ‖twoDimensionalSelectedLoopPairingGeneratorLinearMap
          (realLaplacian := realLaplacian) f‖ := by simp

omit [FiniteDimensional ℝ E] [MeasurableMul₂ G] [MeasurableInv G] in
/-- Duhamel constructs the exact uniform graph-bound field with constant one. -/
theorem eventual_graphBound_one
    {bridge : TwoDimensionalSelectedLoopSpectralBrownianGeneratorBridgeData
      (law := law) (inner := inner) (realLaplacian := realLaplacian)
      (complexLaplacian := complexLaplacian) (heatTraceData := heatTraceData) (Ω := Ω)}
    (data : TwoDimensionalSelectedLoopPairingDuhamelData bridge) :
    ∀ᶠ t : NNReal in nhdsWithin 0 (Set.Ioi 0),
      ∀ f : SmoothLieGroupScalarFunction (E := E) (G := G),
        ‖twoDimensionalSelectedLoopHeatDifferenceQuotientLinearMap bridge t
            (smoothLieGroupScalarToContinuousLinearMap f)‖ ≤
          1 * (‖smoothLieGroupScalarToContinuousLinearMap f‖ +
            ‖twoDimensionalSelectedLoopPairingGeneratorLinearMap
              (realLaplacian := realLaplacian) f‖) := by
  filter_upwards [self_mem_nhdsWithin] with t ht
  intro f
  have hbound := data.quotient_norm_le_generator t ht f
  simpa only [one_mul] using hbound.trans
    (le_add_of_nonneg_left (norm_nonneg (smoothLieGroupScalarToContinuousLinearMap f)))

end TwoDimensionalSelectedLoopPairingDuhamelData

/-- Strong continuity of the total nonnegative-time selected-loop heat semigroup on all continuous
real tests. This is a separate semigroup-analytic target; right continuity at zero on the coefficient
core does not by itself inhabit it. -/
structure TwoDimensionalSelectedLoopStrongContinuousHeatSemigroupData
    (bridge : TwoDimensionalSelectedLoopSpectralBrownianGeneratorBridgeData
      (law := law) (inner := inner) (realLaplacian := realLaplacian)
      (complexLaplacian := complexLaplacian) (heatTraceData := heatTraceData) (Ω := Ω)) where
  trajectory_continuous : ∀ f : C(G, ℝ),
    Continuous (fun t : NNReal =>
      twoDimensionalSelectedLoopHeatOperatorContinuousLinearMap bridge t f)

namespace TwoDimensionalSelectedLoopStrongContinuousHeatSemigroupData

omit [FiniteDimensional ℝ E] [MeasurableMul₂ G] [MeasurableInv G] in
/-- For the already constructed Markov contraction semigroup, right continuity at zero on every
continuous test upgrades to global strong continuity by the generic nonnegative-time semigroup
lemma. Thus no separate continuity-at-positive-time premise is needed. -/
noncomputable def ofTendstoZero
    {bridge : TwoDimensionalSelectedLoopSpectralBrownianGeneratorBridgeData
      (law := law) (inner := inner) (realLaplacian := realLaplacian)
      (complexLaplacian := complexLaplacian) (heatTraceData := heatTraceData) (Ω := Ω)}
    (atZero : ∀ f : C(G, ℝ), Tendsto (fun t : NNReal =>
      twoDimensionalSelectedLoopHeatOperatorContinuousLinearMap bridge t f)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds f)) :
    TwoDimensionalSelectedLoopStrongContinuousHeatSemigroupData bridge where
  trajectory_continuous f := by
    apply continuous_nnreal_semigroup_orbit_of_contractive_of_tendsto_zero
      (fun t : NNReal =>
        twoDimensionalSelectedLoopHeatOperatorContinuousLinearMap bridge t)
    · intro h
      simp [twoDimensionalSelectedLoopHeatOperatorContinuousLinearMap]
    · intro s t h
      have hadd := congrArg (fun operator : C(G, ℝ) →L[ℝ] C(G, ℝ) => operator h)
        (twoDimensionalSelectedLoopHeatOperatorContinuousLinearMap_add bridge s t)
      simpa using hadd
    · intro t h k
      rw [dist_eq_norm, dist_eq_norm, ← map_sub]
      exact twoDimensionalSelectedLoopHeatOperatorContinuousLinearMap_apply_norm_le bridge t (h - k)
    · exact atZero

omit [FiniteDimensional ℝ E] [MeasurableMul₂ G] [MeasurableInv G] in
/-- Uniform density of the designated smooth coefficient image gives right continuity at zero on all
continuous tests and hence global strong continuity of the heat semigroup. -/
noncomputable def ofDense
    {bridge : TwoDimensionalSelectedLoopSpectralBrownianGeneratorBridgeData
      (law := law) (inner := inner) (realLaplacian := realLaplacian)
      (complexLaplacian := complexLaplacian) (heatTraceData := heatTraceData) (Ω := Ω)}
    (dense : Dense
      (smoothLieGroupScalarToContinuousLinearMap ''
        smoothUnitaryMatrixCoefficientRealCoreCandidate (E := E) (G := G))) :
    TwoDimensionalSelectedLoopStrongContinuousHeatSemigroupData bridge :=
  ofTendstoZero
    (twoDimensionalSelectedLoop_smoothMatrixCoefficientCore_heatOperator_tendsto_zero_of_dense
      bridge dense)

omit [FiniteDimensional ℝ E] [MeasurableMul₂ G] [MeasurableInv G] in
/-- Selected continuous Peter--Weyl density plus smooth-dual coverage therefore construct global
strong continuity, while retaining both Fourier hypotheses explicitly. -/
noncomputable def ofContinuousPeterWeylOfSmoothCoverage
    {bridge : TwoDimensionalSelectedLoopSpectralBrownianGeneratorBridgeData
      (law := law) (inner := inner) (realLaplacian := realLaplacian)
      (complexLaplacian := complexLaplacian) (heatTraceData := heatTraceData) (Ω := Ω)}
    (continuousDensity : UnitaryMatrixDual.HasContinuousPeterWeylDensity G)
    (smoothCoverage : ∀ q : UnitaryMatrixDual G,
      q.HasSmoothRepresentative (E := E)) :
    TwoDimensionalSelectedLoopStrongContinuousHeatSemigroupData bridge :=
  ofTendstoZero
    (twoDimensionalSelectedLoop_heatOperator_tendsto_zero_of_continuousPeterWeyl_of_smoothCoverage
      bridge continuousDensity smoothCoverage)

end TwoDimensionalSelectedLoopStrongContinuousHeatSemigroupData

/-- Exact right derivative of every unit-rescaled heat trajectory, separated from the global strong
continuity needed to integrate it. This is a proof-local analytic target and is not attributed to
Driver Remark 4.13. -/
def TwoDimensionalSelectedLoopPairingRescaledHeatDerivative
    (bridge : TwoDimensionalSelectedLoopSpectralBrownianGeneratorBridgeData
      (law := law) (inner := inner) (realLaplacian := realLaplacian)
      (complexLaplacian := complexLaplacian) (heatTraceData := heatTraceData) (Ω := Ω)) : Prop :=
  ∀ (t : NNReal), 0 < t →
    ∀ f : SmoothLieGroupScalarFunction (E := E) (G := G),
      ∀ s ∈ Set.Ioo (0 : ℝ) 1,
        HasDerivWithinAt (fun r : ℝ =>
          twoDimensionalSelectedLoopHeatOperatorContinuousLinearMap bridge
            (Real.toNNReal r * t)
            (smoothLieGroupScalarToContinuousLinearMap f))
          ((t : ℝ) • twoDimensionalSelectedLoopHeatOperatorContinuousLinearMap bridge
            (Real.toNNReal s * t)
            (twoDimensionalSelectedLoopPairingGeneratorLinearMap
              (realLaplacian := realLaplacian) f))
          (Set.Ioi s) s

/-- Differentiability of every unit-rescaled heat trajectory with derivative given by the heat
semigroup applied to the pairing generator, together with global strong continuity. The derivative
is required only on the open unit interval and only from the right. -/
structure TwoDimensionalSelectedLoopPairingRescaledHeatDerivativeData
    (bridge : TwoDimensionalSelectedLoopSpectralBrownianGeneratorBridgeData
      (law := law) (inner := inner) (realLaplacian := realLaplacian)
      (complexLaplacian := complexLaplacian) (heatTraceData := heatTraceData) (Ω := Ω)) where
  strongContinuity : TwoDimensionalSelectedLoopStrongContinuousHeatSemigroupData bridge
  derivative : TwoDimensionalSelectedLoopPairingRescaledHeatDerivative bridge

namespace TwoDimensionalSelectedLoopPairingRescaledHeatDerivativeData

omit [FiniteDimensional ℝ E] [MeasurableMul₂ G] [MeasurableInv G] in
/-- Coefficient-image density supplies global strong continuity, so the raw rescaled derivative is
the only remaining field needed for derivative data. -/
noncomputable def ofDense
    {bridge : TwoDimensionalSelectedLoopSpectralBrownianGeneratorBridgeData
      (law := law) (inner := inner) (realLaplacian := realLaplacian)
      (complexLaplacian := complexLaplacian) (heatTraceData := heatTraceData) (Ω := Ω)}
    (dense : Dense
      (smoothLieGroupScalarToContinuousLinearMap ''
        smoothUnitaryMatrixCoefficientRealCoreCandidate (E := E) (G := G)))
    (derivative : TwoDimensionalSelectedLoopPairingRescaledHeatDerivative bridge) :
    TwoDimensionalSelectedLoopPairingRescaledHeatDerivativeData bridge where
  strongContinuity :=
    TwoDimensionalSelectedLoopStrongContinuousHeatSemigroupData.ofDense dense
  derivative := derivative

omit [FiniteDimensional ℝ E] [MeasurableMul₂ G] [MeasurableInv G] in
/-- Selected continuous Peter--Weyl density plus smooth-dual coverage supplies the density and strong
continuity fields, retaining only the exact rescaled derivative as analytic input. -/
noncomputable def ofContinuousPeterWeylOfSmoothCoverage
    {bridge : TwoDimensionalSelectedLoopSpectralBrownianGeneratorBridgeData
      (law := law) (inner := inner) (realLaplacian := realLaplacian)
      (complexLaplacian := complexLaplacian) (heatTraceData := heatTraceData) (Ω := Ω)}
    (continuousDensity : UnitaryMatrixDual.HasContinuousPeterWeylDensity G)
    (smoothCoverage : ∀ q : UnitaryMatrixDual G,
      q.HasSmoothRepresentative (E := E))
    (derivative : TwoDimensionalSelectedLoopPairingRescaledHeatDerivative bridge) :
    TwoDimensionalSelectedLoopPairingRescaledHeatDerivativeData bridge where
  strongContinuity :=
    TwoDimensionalSelectedLoopStrongContinuousHeatSemigroupData.ofContinuousPeterWeylOfSmoothCoverage
      continuousDensity smoothCoverage
  derivative := derivative

omit [FiniteDimensional ℝ E] [MeasurableMul₂ G] [MeasurableInv G] in
/-- Strong continuity and the exact rescaled heat-trajectory derivative imply the unit-interval
Duhamel identity by the one-sided Banach-valued fundamental theorem of calculus. -/
theorem duhamelIdentity
    {bridge : TwoDimensionalSelectedLoopSpectralBrownianGeneratorBridgeData
      (law := law) (inner := inner) (realLaplacian := realLaplacian)
      (complexLaplacian := complexLaplacian) (heatTraceData := heatTraceData) (Ω := Ω)}
    (data : TwoDimensionalSelectedLoopPairingRescaledHeatDerivativeData bridge) :
    TwoDimensionalSelectedLoopPairingDuhamelIdentity bridge := by
  intro t ht f
  let Jf := smoothLieGroupScalarToContinuousLinearMap f
  let Af := twoDimensionalSelectedLoopPairingGeneratorLinearMap
    (realLaplacian := realLaplacian) f
  let F : ℝ → C(G, ℝ) := fun s =>
    twoDimensionalSelectedLoopHeatOperatorContinuousLinearMap bridge
      (Real.toNNReal s * t) Jf
  let V : ℝ → C(G, ℝ) := fun s =>
    twoDimensionalSelectedLoopHeatOperatorContinuousLinearMap bridge
      (Real.toNNReal s * t) Af
  have htime : Continuous (fun s : ℝ => Real.toNNReal s * t) :=
    continuous_real_toNNReal.mul continuous_const
  have hFcont : Continuous F :=
    (data.strongContinuity.trajectory_continuous Jf).comp htime
  have hVcont : Continuous V :=
    (data.strongContinuity.trajectory_continuous Af).comp htime
  have hscaledInt : IntervalIntegrable (fun s : ℝ => (t : ℝ) • V s) volume 0 1 :=
    (hVcont.const_smul (t : ℝ)).intervalIntegrable 0 1
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le
    (E := C(G, ℝ)) zero_le_one hFcont.continuousOn (by
      intro s hs
      exact data.derivative t ht f s hs) hscaledInt
  rw [intervalIntegral.integral_smul] at hFTC
  have hFzero : F 0 = Jf := by
    simp [F, twoDimensionalSelectedLoopHeatOperatorContinuousLinearMap]
  have hFone : F 1 =
      twoDimensionalSelectedLoopHeatOperatorContinuousLinearMap bridge t Jf := by
    simp [F]
  rw [hFzero, hFone] at hFTC
  have hrecovery :=
    twoDimensionalSelectedLoopHeatOperator_eq_add_smul_differenceQuotient bridge t Jf
  have hdifference :
      twoDimensionalSelectedLoopHeatOperatorContinuousLinearMap bridge t Jf - Jf =
        (t : ℝ) • twoDimensionalSelectedLoopHeatDifferenceQuotientLinearMap bridge t Jf := by
    rw [hrecovery]
    abel
  rw [hdifference] at hFTC
  have htne : (t : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt ht
  have heq := (smul_right_injective C(G, ℝ) htne) hFTC
  exact heq.symm

end TwoDimensionalSelectedLoopPairingRescaledHeatDerivativeData

/-- A continuous Duhamel strengthening stores strong semigroup continuity and the exact identity.
Strong continuity derives the genuine interval-integrability field of the prior Duhamel record. -/
structure TwoDimensionalSelectedLoopPairingContinuousDuhamelData
    (bridge : TwoDimensionalSelectedLoopSpectralBrownianGeneratorBridgeData
      (law := law) (inner := inner) (realLaplacian := realLaplacian)
      (complexLaplacian := complexLaplacian) (heatTraceData := heatTraceData) (Ω := Ω)) where
  strongContinuity : TwoDimensionalSelectedLoopStrongContinuousHeatSemigroupData bridge
  duhamel : TwoDimensionalSelectedLoopPairingDuhamelIdentity bridge

namespace TwoDimensionalSelectedLoopPairingContinuousDuhamelData

omit [FiniteDimensional ℝ E] [MeasurableMul₂ G] [MeasurableInv G] in
/-- Rescaled heat-trajectory differentiability derives the exact Duhamel identity, so it constructs
continuous Duhamel data without taking the identity as a separate premise. -/
noncomputable def ofRescaledHeatDerivative
    {bridge : TwoDimensionalSelectedLoopSpectralBrownianGeneratorBridgeData
      (law := law) (inner := inner) (realLaplacian := realLaplacian)
      (complexLaplacian := complexLaplacian) (heatTraceData := heatTraceData) (Ω := Ω)}
    (data : TwoDimensionalSelectedLoopPairingRescaledHeatDerivativeData bridge) :
    TwoDimensionalSelectedLoopPairingContinuousDuhamelData bridge where
  strongContinuity := data.strongContinuity
  duhamel := data.duhamelIdentity

omit [FiniteDimensional ℝ E] [MeasurableMul₂ G] [MeasurableInv G] in
/-- Uniform coefficient-image density plus the exact Duhamel identity constructs continuous Duhamel
data; global strong continuity and interval integrability are then derived rather than assumed. -/
noncomputable def ofDense
    {bridge : TwoDimensionalSelectedLoopSpectralBrownianGeneratorBridgeData
      (law := law) (inner := inner) (realLaplacian := realLaplacian)
      (complexLaplacian := complexLaplacian) (heatTraceData := heatTraceData) (Ω := Ω)}
    (dense : Dense
      (smoothLieGroupScalarToContinuousLinearMap ''
        smoothUnitaryMatrixCoefficientRealCoreCandidate (E := E) (G := G)))
    (duhamelIdentity : TwoDimensionalSelectedLoopPairingDuhamelIdentity bridge) :
    TwoDimensionalSelectedLoopPairingContinuousDuhamelData bridge where
  strongContinuity :=
    TwoDimensionalSelectedLoopStrongContinuousHeatSemigroupData.ofDense dense
  duhamel := duhamelIdentity

omit [FiniteDimensional ℝ E] [MeasurableMul₂ G] [MeasurableInv G] in
/-- Strong continuity supplies genuine interval integrability, so continuous Duhamel data canonically
inhabits the integrable Duhamel interface. -/
noncomputable def toDuhamelData
    {bridge : TwoDimensionalSelectedLoopSpectralBrownianGeneratorBridgeData
      (law := law) (inner := inner) (realLaplacian := realLaplacian)
      (complexLaplacian := complexLaplacian) (heatTraceData := heatTraceData) (Ω := Ω)}
    (data : TwoDimensionalSelectedLoopPairingContinuousDuhamelData bridge) :
    TwoDimensionalSelectedLoopPairingDuhamelData bridge where
  trajectory_intervalIntegrable t f := by
    have htime : Continuous (fun s : ℝ => Real.toNNReal s * t) :=
      continuous_real_toNNReal.mul continuous_const
    exact ((data.strongContinuity.trajectory_continuous
      (twoDimensionalSelectedLoopPairingGeneratorLinearMap
        (realLaplacian := realLaplacian) f)).comp htime).intervalIntegrable 0 1
  duhamel := data.duhamel

end TwoDimensionalSelectedLoopPairingContinuousDuhamelData

/-- Explicit Fourier-facing simultaneous approximation target for the smooth coefficient core. -/
def TwoDimensionalSelectedLoopSmoothMatrixCoefficientFiniteGraphApproximation : Prop :=
  ∀ f : SmoothLieGroupScalarFunction (E := E) (G := G),
    ∀ ε : ℝ, 0 < ε →
      ∃ coefficients : SmoothUnitaryMatrixCoefficientRealCoefficients E G,
        ‖smoothLieGroupScalarToContinuousLinearMap f -
            smoothLieGroupScalarToContinuousLinearMap
              (smoothUnitaryMatrixCoefficientRealSynthesis coefficients)‖ < ε ∧
          ‖twoDimensionalSelectedLoopPairingGeneratorLinearMap
              (realLaplacian := realLaplacian) f -
            twoDimensionalSelectedLoopPairingGeneratorLinearMap
              (realLaplacian := realLaplacian)
              (smoothUnitaryMatrixCoefficientRealSynthesis coefficients)‖ < ε

omit [FiniteDimensional ℝ E] [IsTopologicalGroup G] [T2Space G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    [MeasurableMul₂ G] [MeasurableInv G] in
/-- Smooth graph density of the designated core is exactly simultaneous uniform approximation of a
smooth test and its pairing generator by one finite real coefficient synthesis. This source-facing
form exposes the precise Fourier approximation theorem still required. -/
theorem smoothMatrixCoefficient_graphDense_iff_finiteSynthesis_graphApproximation :
    IsLinearMapDomainGraphDenseCore
      smoothLieGroupScalarToContinuousLinearMap
      (twoDimensionalSelectedLoopPairingGeneratorLinearMap
        (realLaplacian := realLaplacian))
      (smoothUnitaryMatrixCoefficientRealCoreCandidate (E := E) (G := G)) ↔
    TwoDimensionalSelectedLoopSmoothMatrixCoefficientFiniteGraphApproximation
      (realLaplacian := realLaplacian) := by
  constructor
  · intro graphDense f ε hε
    obtain ⟨z, hz, hJ, hA⟩ := graphDense f ε hε
    obtain ⟨coefficients, rfl⟩ := hz
    exact ⟨coefficients, hJ, hA⟩
  · intro finiteApproximation f ε hε
    obtain ⟨coefficients, hJ, hA⟩ := finiteApproximation f ε hε
    exact ⟨smoothUnitaryMatrixCoefficientRealSynthesis coefficients,
      ⟨coefficients, rfl⟩, hJ, hA⟩

omit [FiniteDimensional ℝ E] [IsTopologicalGroup G] [T2Space G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    [MeasurableMul₂ G] [MeasurableInv G] in
/-- Simultaneous finite graph approximation contains uniform approximation of every smooth test.
If smooth real functions themselves are dense in the continuous ambient space, this zeroth graph
coordinate therefore makes the smooth coefficient image dense in all continuous tests. -/
theorem smoothMatrixCoefficient_continuousImage_dense_of_finiteGraphApproximation_of_smoothDense
    (finiteApproximation :
      TwoDimensionalSelectedLoopSmoothMatrixCoefficientFiniteGraphApproximation
        (realLaplacian := realLaplacian))
    (smoothDense : SmoothLieGroupScalarFunctionsDenseInContinuous (E := E) (G := G)) :
    Dense
      (smoothLieGroupScalarToContinuousLinearMap ''
        smoothUnitaryMatrixCoefficientRealCoreCandidate (E := E) (G := G)) := by
  let J := smoothLieGroupScalarToContinuousLinearMap (E := E) (G := G)
  let A := twoDimensionalSelectedLoopPairingGeneratorLinearMap
    (realLaplacian := realLaplacian)
  let core := smoothUnitaryMatrixCoefficientRealCoreCandidate (E := E) (G := G)
  have graphDense : IsLinearMapDomainGraphDenseCore J A core :=
    smoothMatrixCoefficient_graphDense_iff_finiteSynthesis_graphApproximation.mpr
      finiteApproximation
  have range_subset : Set.range J ⊆ closure (J '' core) := by
    rintro _ ⟨f, rfl⟩
    exact (graphDense f).mem_closure_image J A core
  have closure_subset : closure (Set.range J) ⊆ closure (J '' core) :=
    closure_minimal range_subset isClosed_closure
  rw [dense_iff_closure_eq]
  apply Set.Subset.antisymm
  · exact Set.subset_univ _
  intro f _hf
  apply closure_subset
  rw [smoothDense.closure_eq]
  exact Set.mem_univ f

namespace TwoDimensionalSelectedLoopStrongContinuousHeatSemigroupData

omit [FiniteDimensional ℝ E] [MeasurableMul₂ G] [MeasurableInv G] in
/-- Finite graph approximation plus density of all smooth tests in the continuous ambient space
constructs global strong continuity of the selected heat semigroup. -/
noncomputable def ofFiniteGraphApproximationOfSmoothDense
    {bridge : TwoDimensionalSelectedLoopSpectralBrownianGeneratorBridgeData
      (law := law) (inner := inner) (realLaplacian := realLaplacian)
      (complexLaplacian := complexLaplacian) (heatTraceData := heatTraceData) (Ω := Ω)}
    (finiteApproximation :
      TwoDimensionalSelectedLoopSmoothMatrixCoefficientFiniteGraphApproximation
        (realLaplacian := realLaplacian))
    (smoothDense : SmoothLieGroupScalarFunctionsDenseInContinuous (E := E) (G := G)) :
    TwoDimensionalSelectedLoopStrongContinuousHeatSemigroupData bridge :=
  ofDense
    (smoothMatrixCoefficient_continuousImage_dense_of_finiteGraphApproximation_of_smoothDense
      finiteApproximation smoothDense)

end TwoDimensionalSelectedLoopStrongContinuousHeatSemigroupData

namespace TwoDimensionalSelectedLoopPairingContinuousDuhamelData

omit [FiniteDimensional ℝ E] [MeasurableMul₂ G] [MeasurableInv G] in
/-- Finite graph approximation, ambient smooth density, and the exact Duhamel identity construct
continuous Duhamel data without an additional coefficient-density premise. -/
noncomputable def ofFiniteGraphApproximationOfSmoothDense
    {bridge : TwoDimensionalSelectedLoopSpectralBrownianGeneratorBridgeData
      (law := law) (inner := inner) (realLaplacian := realLaplacian)
      (complexLaplacian := complexLaplacian) (heatTraceData := heatTraceData) (Ω := Ω)}
    (finiteApproximation :
      TwoDimensionalSelectedLoopSmoothMatrixCoefficientFiniteGraphApproximation
        (realLaplacian := realLaplacian))
    (smoothDense : SmoothLieGroupScalarFunctionsDenseInContinuous (E := E) (G := G))
    (duhamelIdentity : TwoDimensionalSelectedLoopPairingDuhamelIdentity bridge) :
    TwoDimensionalSelectedLoopPairingContinuousDuhamelData bridge :=
  ofDense
    (smoothMatrixCoefficient_continuousImage_dense_of_finiteGraphApproximation_of_smoothDense
      finiteApproximation smoothDense)
    duhamelIdentity

end TwoDimensionalSelectedLoopPairingContinuousDuhamelData

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
/-- Smooth graph density together with the proof-local Duhamel strengthening constructs the coefficient
graph-core record with sharp graph-bound constant one. -/
noncomputable def ofGraphDenseDuhamel
    {bridge : TwoDimensionalSelectedLoopSpectralBrownianGeneratorBridgeData
      (law := law) (inner := inner) (realLaplacian := realLaplacian)
      (complexLaplacian := complexLaplacian) (heatTraceData := heatTraceData) (Ω := Ω)}
    (graphDense : IsLinearMapDomainGraphDenseCore
      smoothLieGroupScalarToContinuousLinearMap
      (twoDimensionalSelectedLoopPairingGeneratorLinearMap
        (realLaplacian := realLaplacian))
      (smoothUnitaryMatrixCoefficientRealCoreCandidate (E := E) (G := G)))
    (duhamel : TwoDimensionalSelectedLoopPairingDuhamelData bridge) :
    TwoDimensionalSelectedLoopSmoothMatrixCoefficientGraphCoreData bridge where
  graphDense := graphDense
  graphBoundConstant := 1
  graphBoundConstant_nonneg := zero_le_one
  eventual_graphBound := duhamel.eventual_graphBound_one

omit [FiniteDimensional ℝ E] [MeasurableMul₂ G] [MeasurableInv G] in
/-- Fully analytic constructor: simultaneous finite coefficient graph approximation plus the
integrable Duhamel identity constructs the coefficient graph-core record. -/
noncomputable def ofFiniteSynthesisGraphApproximationDuhamel
    {bridge : TwoDimensionalSelectedLoopSpectralBrownianGeneratorBridgeData
      (law := law) (inner := inner) (realLaplacian := realLaplacian)
      (complexLaplacian := complexLaplacian) (heatTraceData := heatTraceData) (Ω := Ω)}
    (finiteApproximation :
      TwoDimensionalSelectedLoopSmoothMatrixCoefficientFiniteGraphApproximation
        (realLaplacian := realLaplacian))
    (duhamel : TwoDimensionalSelectedLoopPairingDuhamelData bridge) :
    TwoDimensionalSelectedLoopSmoothMatrixCoefficientGraphCoreData bridge :=
  ofGraphDenseDuhamel
    (smoothMatrixCoefficient_graphDense_iff_finiteSynthesis_graphApproximation.mpr
      finiteApproximation) duhamel

omit [FiniteDimensional ℝ E] [MeasurableMul₂ G] [MeasurableInv G] in
/-- Simultaneous finite graph approximation plus continuous Duhamel data constructs the graph core;
strong continuity supplies the required integrability automatically. -/
noncomputable def ofFiniteSynthesisGraphApproximationContinuousDuhamel
    {bridge : TwoDimensionalSelectedLoopSpectralBrownianGeneratorBridgeData
      (law := law) (inner := inner) (realLaplacian := realLaplacian)
      (complexLaplacian := complexLaplacian) (heatTraceData := heatTraceData) (Ω := Ω)}
    (finiteApproximation :
      TwoDimensionalSelectedLoopSmoothMatrixCoefficientFiniteGraphApproximation
        (realLaplacian := realLaplacian))
    (duhamel : TwoDimensionalSelectedLoopPairingContinuousDuhamelData bridge) :
    TwoDimensionalSelectedLoopSmoothMatrixCoefficientGraphCoreData bridge :=
  ofFiniteSynthesisGraphApproximationDuhamel finiteApproximation duhamel.toDuhamelData

omit [FiniteDimensional ℝ E] [MeasurableMul₂ G] [MeasurableInv G] in
/-- Any coefficient graph-core witness already supplies strong right-continuity of the heat
semigroup on every smooth test through its graph-density field alone. -/
theorem allSmooth_heatOperator_tendsto_zero
    {bridge : TwoDimensionalSelectedLoopSpectralBrownianGeneratorBridgeData
      (law := law) (inner := inner) (realLaplacian := realLaplacian)
      (complexLaplacian := complexLaplacian) (heatTraceData := heatTraceData) (Ω := Ω)}
    (data : TwoDimensionalSelectedLoopSmoothMatrixCoefficientGraphCoreData bridge)
    (f : SmoothLieGroupScalarFunction (E := E) (G := G)) :
    Tendsto (fun t : NNReal =>
      twoDimensionalSelectedLoopHeatOperatorContinuousLinearMap bridge t
        (smoothLieGroupScalarToContinuousLinearMap f))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (smoothLieGroupScalarToContinuousLinearMap f)) :=
  twoDimensionalSelectedLoop_smoothMatrixCoefficientCore_heatOperator_tendsto_zero_of_graphDense
    bridge data.graphDense f

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

omit [FiniteDimensional ℝ E] [MeasurableMul₂ G] [MeasurableInv G] in
/-- Fourier-facing inhabitance audit: the graph-core record is inhabited exactly when every smooth
test and its pairing generator have one simultaneous finite coefficient approximation and one
uniform eventual all-domain graph bound is supplied. -/
theorem nonempty_iff_finiteSynthesis_graphApproximation_and_eventualGraphBound
    {bridge : TwoDimensionalSelectedLoopSpectralBrownianGeneratorBridgeData
      (law := law) (inner := inner) (realLaplacian := realLaplacian)
      (complexLaplacian := complexLaplacian) (heatTraceData := heatTraceData) (Ω := Ω)} :
    Nonempty (TwoDimensionalSelectedLoopSmoothMatrixCoefficientGraphCoreData bridge) ↔
      TwoDimensionalSelectedLoopSmoothMatrixCoefficientFiniteGraphApproximation
        (realLaplacian := realLaplacian) ∧
        ∃ C : ℝ, 0 ≤ C ∧
          ∀ᶠ t : NNReal in nhdsWithin 0 (Set.Ioi 0),
            ∀ f : SmoothLieGroupScalarFunction (E := E) (G := G),
              ‖twoDimensionalSelectedLoopHeatDifferenceQuotientLinearMap bridge t
                  (smoothLieGroupScalarToContinuousLinearMap f)‖ ≤
                C * (‖smoothLieGroupScalarToContinuousLinearMap f‖ +
                  ‖twoDimensionalSelectedLoopPairingGeneratorLinearMap
                    (realLaplacian := realLaplacian) f‖) := by
  rw [nonempty_iff_graphDense_and_eventualGraphBound,
    smoothMatrixCoefficient_graphDense_iff_finiteSynthesis_graphApproximation]

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

/-- Duhamel-strengthened analytic acceptance surface for the selected smooth matrix-coefficient
track. It retains exactly simultaneous finite graph approximation and an inhabited integrable
Duhamel identity; it does not assert either premise. -/
def TwoDimensionalSelectedLoopSmoothMatrixCoefficientDuhamelAnalyticAcceptance
    (bridge : TwoDimensionalSelectedLoopSpectralBrownianGeneratorBridgeData
      (law := law) (inner := inner) (realLaplacian := realLaplacian)
      (complexLaplacian := complexLaplacian) (heatTraceData := heatTraceData) (Ω := Ω)) : Prop :=
  TwoDimensionalSelectedLoopSmoothMatrixCoefficientFiniteGraphApproximation
      (realLaplacian := realLaplacian) ∧
    Nonempty (TwoDimensionalSelectedLoopPairingDuhamelData bridge)

namespace TwoDimensionalSelectedLoopSmoothMatrixCoefficientDuhamelAnalyticAcceptance

omit [FiniteDimensional ℝ E] [MeasurableMul₂ G] [MeasurableInv G] in
/-- The Duhamel-strengthened acceptance canonically constructs the exact coefficient graph-core data. -/
noncomputable def toGraphCoreData
    {bridge : TwoDimensionalSelectedLoopSpectralBrownianGeneratorBridgeData
      (law := law) (inner := inner) (realLaplacian := realLaplacian)
      (complexLaplacian := complexLaplacian) (heatTraceData := heatTraceData) (Ω := Ω)}
    (acceptance :
      TwoDimensionalSelectedLoopSmoothMatrixCoefficientDuhamelAnalyticAcceptance bridge) :
    TwoDimensionalSelectedLoopSmoothMatrixCoefficientGraphCoreData bridge :=
  TwoDimensionalSelectedLoopSmoothMatrixCoefficientGraphCoreData.ofFiniteSynthesisGraphApproximationDuhamel
    acceptance.1 (Classical.choice acceptance.2)

omit [FiniteDimensional ℝ E] [MeasurableMul₂ G] [MeasurableInv G] in
/-- The same analytic acceptance reaches the existing all-smooth stochastic generator endpoint. -/
noncomputable def toStochasticGeneratorAtZeroData
    {bridge : TwoDimensionalSelectedLoopSpectralBrownianGeneratorBridgeData
      (law := law) (inner := inner) (realLaplacian := realLaplacian)
      (complexLaplacian := complexLaplacian) (heatTraceData := heatTraceData) (Ω := Ω)}
    (acceptance :
      TwoDimensionalSelectedLoopSmoothMatrixCoefficientDuhamelAnalyticAcceptance bridge) :
    TwoDimensionalSelectedLoopStochasticGeneratorAtZeroData bridge :=
  acceptance.toGraphCoreData.toStochasticGeneratorAtZeroData

end TwoDimensionalSelectedLoopSmoothMatrixCoefficientDuhamelAnalyticAcceptance

/-- Strongly-continuous Duhamel analytic acceptance. It replaces raw interval-integrability data by
strong continuity of the total contraction semigroup together with the exact Duhamel identity. -/
def TwoDimensionalSelectedLoopSmoothMatrixCoefficientContinuousDuhamelAnalyticAcceptance
    (bridge : TwoDimensionalSelectedLoopSpectralBrownianGeneratorBridgeData
      (law := law) (inner := inner) (realLaplacian := realLaplacian)
      (complexLaplacian := complexLaplacian) (heatTraceData := heatTraceData) (Ω := Ω)) : Prop :=
  TwoDimensionalSelectedLoopSmoothMatrixCoefficientFiniteGraphApproximation
      (realLaplacian := realLaplacian) ∧
    Nonempty (TwoDimensionalSelectedLoopPairingContinuousDuhamelData bridge)

namespace TwoDimensionalSelectedLoopSmoothMatrixCoefficientContinuousDuhamelAnalyticAcceptance

omit [FiniteDimensional ℝ E] [MeasurableMul₂ G] [MeasurableInv G] in
/-- Forgetting the strong-continuity derivation of integrability recovers the prior Duhamel analytic
acceptance. -/
theorem implies_DuhamelAnalyticAcceptance
    {bridge : TwoDimensionalSelectedLoopSpectralBrownianGeneratorBridgeData
      (law := law) (inner := inner) (realLaplacian := realLaplacian)
      (complexLaplacian := complexLaplacian) (heatTraceData := heatTraceData) (Ω := Ω)}
    (acceptance :
      TwoDimensionalSelectedLoopSmoothMatrixCoefficientContinuousDuhamelAnalyticAcceptance bridge) :
    TwoDimensionalSelectedLoopSmoothMatrixCoefficientDuhamelAnalyticAcceptance bridge := by
  rcases acceptance with ⟨finiteApproximation, ⟨duhamel⟩⟩
  exact ⟨finiteApproximation, ⟨duhamel.toDuhamelData⟩⟩

omit [FiniteDimensional ℝ E] [MeasurableMul₂ G] [MeasurableInv G] in
/-- The strongly-continuous Duhamel acceptance reaches the all-smooth stochastic generator endpoint. -/
noncomputable def toStochasticGeneratorAtZeroData
    {bridge : TwoDimensionalSelectedLoopSpectralBrownianGeneratorBridgeData
      (law := law) (inner := inner) (realLaplacian := realLaplacian)
      (complexLaplacian := complexLaplacian) (heatTraceData := heatTraceData) (Ω := Ω)}
    (acceptance :
      TwoDimensionalSelectedLoopSmoothMatrixCoefficientContinuousDuhamelAnalyticAcceptance bridge) :
    TwoDimensionalSelectedLoopStochasticGeneratorAtZeroData bridge :=
  acceptance.implies_DuhamelAnalyticAcceptance.toStochasticGeneratorAtZeroData

end TwoDimensionalSelectedLoopSmoothMatrixCoefficientContinuousDuhamelAnalyticAcceptance

/-- Differentiability-facing analytic acceptance: simultaneous finite graph approximation together
with inhabited strong-continuous rescaled heat-trajectory derivative data. The Duhamel identity,
interval integrability, and graph bound are all derived. -/
def TwoDimensionalSelectedLoopSmoothMatrixCoefficientRescaledDerivativeAnalyticAcceptance
    (bridge : TwoDimensionalSelectedLoopSpectralBrownianGeneratorBridgeData
      (law := law) (inner := inner) (realLaplacian := realLaplacian)
      (complexLaplacian := complexLaplacian) (heatTraceData := heatTraceData) (Ω := Ω)) : Prop :=
  TwoDimensionalSelectedLoopSmoothMatrixCoefficientFiniteGraphApproximation
      (realLaplacian := realLaplacian) ∧
    Nonempty (TwoDimensionalSelectedLoopPairingRescaledHeatDerivativeData bridge)

namespace TwoDimensionalSelectedLoopSmoothMatrixCoefficientRescaledDerivativeAnalyticAcceptance

omit [FiniteDimensional ℝ E] [MeasurableMul₂ G] [MeasurableInv G] in
/-- Rescaled derivative acceptance implies the strongly-continuous Duhamel acceptance by the
one-sided fundamental theorem of calculus. -/
theorem implies_continuousDuhamelAnalyticAcceptance
    {bridge : TwoDimensionalSelectedLoopSpectralBrownianGeneratorBridgeData
      (law := law) (inner := inner) (realLaplacian := realLaplacian)
      (complexLaplacian := complexLaplacian) (heatTraceData := heatTraceData) (Ω := Ω)}
    (acceptance :
      TwoDimensionalSelectedLoopSmoothMatrixCoefficientRescaledDerivativeAnalyticAcceptance
        bridge) :
    TwoDimensionalSelectedLoopSmoothMatrixCoefficientContinuousDuhamelAnalyticAcceptance
      bridge := by
  rcases acceptance with ⟨finiteApproximation, ⟨derivativeData⟩⟩
  exact ⟨finiteApproximation,
    ⟨TwoDimensionalSelectedLoopPairingContinuousDuhamelData.ofRescaledHeatDerivative
      derivativeData⟩⟩

omit [FiniteDimensional ℝ E] [MeasurableMul₂ G] [MeasurableInv G] in
/-- The differentiability-facing acceptance reaches the all-smooth stochastic generator endpoint. -/
noncomputable def toStochasticGeneratorAtZeroData
    {bridge : TwoDimensionalSelectedLoopSpectralBrownianGeneratorBridgeData
      (law := law) (inner := inner) (realLaplacian := realLaplacian)
      (complexLaplacian := complexLaplacian) (heatTraceData := heatTraceData) (Ω := Ω)}
    (acceptance :
      TwoDimensionalSelectedLoopSmoothMatrixCoefficientRescaledDerivativeAnalyticAcceptance
        bridge) :
    TwoDimensionalSelectedLoopStochasticGeneratorAtZeroData bridge :=
  acceptance.implies_continuousDuhamelAnalyticAcceptance.toStochasticGeneratorAtZeroData

end TwoDimensionalSelectedLoopSmoothMatrixCoefficientRescaledDerivativeAnalyticAcceptance

/-- Selected-Fourier differentiability acceptance with four explicit obligations: finite graph
approximation, selected continuous Peter--Weyl density, smooth-dual coverage, and the raw rescaled
heat-trajectory derivative. Strong continuity and all Duhamel consequences are derived. -/
structure TwoDimensionalSelectedLoopSmoothMatrixCoefficientSelectedFourierDerivativeAnalyticAcceptance
    (bridge : TwoDimensionalSelectedLoopSpectralBrownianGeneratorBridgeData
      (law := law) (inner := inner) (realLaplacian := realLaplacian)
      (complexLaplacian := complexLaplacian) (heatTraceData := heatTraceData) (Ω := Ω)) : Prop where
  finiteGraphApproximation :
    TwoDimensionalSelectedLoopSmoothMatrixCoefficientFiniteGraphApproximation
      (realLaplacian := realLaplacian)
  continuousDensity : UnitaryMatrixDual.HasContinuousPeterWeylDensity G
  smoothCoverage : ∀ q : UnitaryMatrixDual G,
    q.HasSmoothRepresentative (E := E)
  rescaledDerivative : TwoDimensionalSelectedLoopPairingRescaledHeatDerivative bridge

namespace TwoDimensionalSelectedLoopSmoothMatrixCoefficientSelectedFourierDerivativeAnalyticAcceptance

omit [FiniteDimensional ℝ E] [MeasurableMul₂ G] [MeasurableInv G] in
/-- The exact four selected-Fourier/differentiability obligations construct the prior derivative
acceptance. -/
theorem implies_rescaledDerivativeAnalyticAcceptance
    {bridge : TwoDimensionalSelectedLoopSpectralBrownianGeneratorBridgeData
      (law := law) (inner := inner) (realLaplacian := realLaplacian)
      (complexLaplacian := complexLaplacian) (heatTraceData := heatTraceData) (Ω := Ω)}
    (acceptance :
      TwoDimensionalSelectedLoopSmoothMatrixCoefficientSelectedFourierDerivativeAnalyticAcceptance
        bridge) :
    TwoDimensionalSelectedLoopSmoothMatrixCoefficientRescaledDerivativeAnalyticAcceptance
      bridge :=
  ⟨acceptance.finiteGraphApproximation,
    ⟨TwoDimensionalSelectedLoopPairingRescaledHeatDerivativeData.ofContinuousPeterWeylOfSmoothCoverage
      acceptance.continuousDensity
        acceptance.smoothCoverage acceptance.rescaledDerivative⟩⟩

omit [FiniteDimensional ℝ E] [MeasurableMul₂ G] [MeasurableInv G] in
/-- The same four explicit obligations reach the all-smooth stochastic generator endpoint. -/
noncomputable def toStochasticGeneratorAtZeroData
    {bridge : TwoDimensionalSelectedLoopSpectralBrownianGeneratorBridgeData
      (law := law) (inner := inner) (realLaplacian := realLaplacian)
      (complexLaplacian := complexLaplacian) (heatTraceData := heatTraceData) (Ω := Ω)}
    (acceptance :
      TwoDimensionalSelectedLoopSmoothMatrixCoefficientSelectedFourierDerivativeAnalyticAcceptance
        bridge) :
    TwoDimensionalSelectedLoopStochasticGeneratorAtZeroData bridge :=
  acceptance.implies_rescaledDerivativeAnalyticAcceptance.toStochasticGeneratorAtZeroData

end TwoDimensionalSelectedLoopSmoothMatrixCoefficientSelectedFourierDerivativeAnalyticAcceptance

/-- Exact three-part analytic acceptance route: simultaneous finite graph approximation, uniform
density of all smooth real tests in the continuous ambient space, and the exact Duhamel identity.
All continuity, interval integrability, and graph bounds are derived from these fields. -/
structure TwoDimensionalSelectedLoopSmoothMatrixCoefficientSmoothDensityDuhamelAnalyticAcceptance
    (bridge : TwoDimensionalSelectedLoopSpectralBrownianGeneratorBridgeData
      (law := law) (inner := inner) (realLaplacian := realLaplacian)
      (complexLaplacian := complexLaplacian) (heatTraceData := heatTraceData) (Ω := Ω)) : Prop where
  finiteGraphApproximation :
    TwoDimensionalSelectedLoopSmoothMatrixCoefficientFiniteGraphApproximation
      (realLaplacian := realLaplacian)
  smoothDense : SmoothLieGroupScalarFunctionsDenseInContinuous (E := E) (G := G)
  duhamelIdentity : TwoDimensionalSelectedLoopPairingDuhamelIdentity bridge

namespace TwoDimensionalSelectedLoopSmoothMatrixCoefficientSmoothDensityDuhamelAnalyticAcceptance

omit [FiniteDimensional ℝ E] [MeasurableMul₂ G] [MeasurableInv G] in
/-- Selected continuous Peter--Weyl density and smooth-dual coverage discharge the ambient smooth
density field of the exact three-part acceptance. Finite graph approximation and the Duhamel
identity remain explicit. -/
def ofContinuousPeterWeylOfSmoothCoverage
    {bridge : TwoDimensionalSelectedLoopSpectralBrownianGeneratorBridgeData
      (law := law) (inner := inner) (realLaplacian := realLaplacian)
      (complexLaplacian := complexLaplacian) (heatTraceData := heatTraceData) (Ω := Ω)}
    (finiteGraphApproximation :
      TwoDimensionalSelectedLoopSmoothMatrixCoefficientFiniteGraphApproximation
        (realLaplacian := realLaplacian))
    (continuousDensity : UnitaryMatrixDual.HasContinuousPeterWeylDensity G)
    (smoothCoverage : ∀ q : UnitaryMatrixDual G,
      q.HasSmoothRepresentative (E := E))
    (duhamelIdentity : TwoDimensionalSelectedLoopPairingDuhamelIdentity bridge) :
    TwoDimensionalSelectedLoopSmoothMatrixCoefficientSmoothDensityDuhamelAnalyticAcceptance
      bridge where
  finiteGraphApproximation := finiteGraphApproximation
  smoothDense :=
    smoothLieGroupScalarFunctionsDenseInContinuous_of_continuousPeterWeyl_of_smoothCoverage
      continuousDensity smoothCoverage
  duhamelIdentity := duhamelIdentity

omit [FiniteDimensional ℝ E] [MeasurableMul₂ G] [MeasurableInv G] in
/-- The exact three-part route constructs the prior strongly-continuous Duhamel acceptance. -/
theorem implies_continuousDuhamelAnalyticAcceptance
    {bridge : TwoDimensionalSelectedLoopSpectralBrownianGeneratorBridgeData
      (law := law) (inner := inner) (realLaplacian := realLaplacian)
      (complexLaplacian := complexLaplacian) (heatTraceData := heatTraceData) (Ω := Ω)}
    (acceptance :
      TwoDimensionalSelectedLoopSmoothMatrixCoefficientSmoothDensityDuhamelAnalyticAcceptance
        bridge) :
    TwoDimensionalSelectedLoopSmoothMatrixCoefficientContinuousDuhamelAnalyticAcceptance
      bridge :=
  ⟨acceptance.finiteGraphApproximation,
    ⟨TwoDimensionalSelectedLoopPairingContinuousDuhamelData.ofFiniteGraphApproximationOfSmoothDense
        acceptance.finiteGraphApproximation
        acceptance.smoothDense acceptance.duhamelIdentity⟩⟩

omit [FiniteDimensional ℝ E] [MeasurableMul₂ G] [MeasurableInv G] in
/-- The same exact three obligations reach the all-smooth stochastic generator endpoint. -/
noncomputable def toStochasticGeneratorAtZeroData
    {bridge : TwoDimensionalSelectedLoopSpectralBrownianGeneratorBridgeData
      (law := law) (inner := inner) (realLaplacian := realLaplacian)
      (complexLaplacian := complexLaplacian) (heatTraceData := heatTraceData) (Ω := Ω)}
    (acceptance :
      TwoDimensionalSelectedLoopSmoothMatrixCoefficientSmoothDensityDuhamelAnalyticAcceptance
        bridge) :
    TwoDimensionalSelectedLoopStochasticGeneratorAtZeroData bridge :=
  acceptance.implies_continuousDuhamelAnalyticAcceptance.toStochasticGeneratorAtZeroData

end TwoDimensionalSelectedLoopSmoothMatrixCoefficientSmoothDensityDuhamelAnalyticAcceptance

end

end Dimensions
end YangMills
