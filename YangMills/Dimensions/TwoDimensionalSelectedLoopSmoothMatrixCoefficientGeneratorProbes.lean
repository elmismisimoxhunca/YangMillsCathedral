/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Dimensions.TwoDimensionalSelectedLoopSmoothMatrixCoefficientGenerator

namespace YangMills
namespace Dimensions

open Filter
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
    (bridge : TwoDimensionalSelectedLoopSpectralBrownianGeneratorBridgeData
      (law := law) (inner := inner) (realLaplacian := realLaplacian)
      (complexLaplacian := complexLaplacian) (heatTraceData := heatTraceData) (Ω := Ω))

omit [FiniteDimensional ℝ E] [MeasurableMul₂ G] [MeasurableInv G] in
/-- Exact real/imaginary matrix-coefficient heat action probe. -/
theorem exact_selectedLoopHeatOperator_smoothMatrixCoefficient
    (t : ℝ) (ht : 0 < t) (index : SmoothUnitaryMatrixCoefficientRealIndex E G) :
    bridge.spectralHeatKernel.kernelOperator.heatOperator t
        (smoothLieGroupScalarToContinuousLinearMap
          (smoothUnitaryMatrixCoefficientRealFunction index)) =
      Real.exp (-(t / 2) * heatTraceData.casimirWeight
        (unitaryMatrixDualClass
          index.representation.toContinuousUnitaryIrreducibleMatrixRepresentation)) •
        smoothLieGroupScalarToContinuousLinearMap
          (smoothUnitaryMatrixCoefficientRealFunction index) :=
  twoDimensionalSelectedLoopHeatOperator_smoothMatrixCoefficient bridge t ht index

omit [FiniteDimensional ℝ E] [MeasurableMul₂ G] [MeasurableInv G] in
/-- Exact positive-time heat evolution on every finite real coefficient synthesis. -/
theorem exact_selectedLoopHeatOperator_smoothMatrixCoefficientSynthesis
    (t : ℝ) (ht : 0 < t)
    (coefficients : SmoothUnitaryMatrixCoefficientRealCoefficients E G) :
    bridge.spectralHeatKernel.kernelOperator.heatOperator t
        (smoothLieGroupScalarToContinuousLinearMap
          (smoothUnitaryMatrixCoefficientRealSynthesis coefficients)) =
      smoothLieGroupScalarToContinuousLinearMap
        (twoDimensionalSelectedLoopSmoothMatrixCoefficientHeatEvolution
          (heatTraceData := heatTraceData) t coefficients) :=
  twoDimensionalSelectedLoopHeatOperator_smoothMatrixCoefficientSynthesis
    bridge t ht coefficients

omit [FiniteDimensional ℝ E] [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    [MeasurableMul₂ G] [MeasurableInv G]
    [LieGroup (modelWithCornersSelf ℝ E) ∞ G] in
/-- Exact algebraic-core invariance under finite coefficient heat evolution. -/
theorem exact_smoothMatrixCoefficientHeatEvolution_mem_core
    (t : ℝ) (coefficients : SmoothUnitaryMatrixCoefficientRealCoefficients E G) :
    twoDimensionalSelectedLoopSmoothMatrixCoefficientHeatEvolution
      (heatTraceData := heatTraceData) t coefficients ∈
      smoothUnitaryMatrixCoefficientRealCoreCandidate (E := E) (G := G) :=
  twoDimensionalSelectedLoopSmoothMatrixCoefficientHeatEvolution_mem_coreCandidate
    (heatTraceData := heatTraceData) t coefficients

omit [FiniteDimensional ℝ E] [MeasurableMul₂ G] [MeasurableInv G] in
/-- Hostile finite-evolution probe: changing the coefficientwise heat synthesis is contradictory. -/
theorem changed_selectedLoopHeatOperator_smoothMatrixCoefficientSynthesis_blocked
    (t : ℝ) (ht : 0 < t)
    (coefficients : SmoothUnitaryMatrixCoefficientRealCoefficients E G)
    (changed : C(G, ℝ))
    (changed_ne_exact : changed ≠ smoothLieGroupScalarToContinuousLinearMap
      (twoDimensionalSelectedLoopSmoothMatrixCoefficientHeatEvolution
        (heatTraceData := heatTraceData) t coefficients))
    (claimed : bridge.spectralHeatKernel.kernelOperator.heatOperator t
      (smoothLieGroupScalarToContinuousLinearMap
        (smoothUnitaryMatrixCoefficientRealSynthesis coefficients)) = changed) : False :=
  changed_ne_exact (claimed.symm.trans
    (twoDimensionalSelectedLoopHeatOperator_smoothMatrixCoefficientSynthesis
      bridge t ht coefficients))

omit [FiniteDimensional ℝ E] [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    [MeasurableMul₂ G] [MeasurableInv G]
    [LieGroup (modelWithCornersSelf ℝ E) ∞ G] in
/-- Exact zero branch of the coefficient-space difference quotient. -/
theorem exact_smoothMatrixCoefficientDifferenceQuotient_zero :
    twoDimensionalSelectedLoopSmoothMatrixCoefficientDifferenceQuotientEvolution
      (E := E) (G := G) (heatTraceData := heatTraceData) 0 = 0 :=
  twoDimensionalSelectedLoopSmoothMatrixCoefficientDifferenceQuotientEvolution_zero

omit [FiniteDimensional ℝ E] [MeasurableMul₂ G] [MeasurableInv G] in
/-- Exact ambient/coefficient-space difference-quotient coherence on finite syntheses. -/
theorem exact_selectedLoopHeatDifferenceQuotient_smoothMatrixCoefficientSynthesis
    (t : NNReal) (ht : 0 < t)
    (coefficients : SmoothUnitaryMatrixCoefficientRealCoefficients E G) :
    twoDimensionalSelectedLoopHeatDifferenceQuotientLinearMap bridge t
        (smoothLieGroupScalarToContinuousLinearMap
          (smoothUnitaryMatrixCoefficientRealSynthesis coefficients)) =
      smoothLieGroupScalarToContinuousLinearMap
        (twoDimensionalSelectedLoopSmoothMatrixCoefficientDifferenceQuotientEvolution
          (heatTraceData := heatTraceData) t coefficients) :=
  twoDimensionalSelectedLoopHeatDifferenceQuotient_smoothMatrixCoefficientSynthesis
    bridge t ht coefficients

omit [FiniteDimensional ℝ E] [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    [MeasurableMul₂ G] [MeasurableInv G]
    [LieGroup (modelWithCornersSelf ℝ E) ∞ G] in
/-- Exact algebraic-core invariance under every positive coefficient difference quotient. -/
theorem exact_smoothMatrixCoefficientDifferenceQuotient_mem_core
    (t : NNReal) (ht : 0 < t)
    (coefficients : SmoothUnitaryMatrixCoefficientRealCoefficients E G) :
    twoDimensionalSelectedLoopSmoothMatrixCoefficientDifferenceQuotientEvolution
      (heatTraceData := heatTraceData) t coefficients ∈
      smoothUnitaryMatrixCoefficientRealCoreCandidate (E := E) (G := G) :=
  twoDimensionalSelectedLoopSmoothMatrixCoefficientDifferenceQuotientEvolution_mem_coreCandidate
    (heatTraceData := heatTraceData) t ht coefficients

omit [FiniteDimensional ℝ E] [MeasurableMul₂ G] [MeasurableInv G] in
/-- Hostile quotient-coherence probe: a changed coefficient-space realization is contradictory. -/
theorem changed_selectedLoopHeatDifferenceQuotient_smoothMatrixCoefficientSynthesis_blocked
    (t : NNReal) (ht : 0 < t)
    (coefficients : SmoothUnitaryMatrixCoefficientRealCoefficients E G)
    (changed : C(G, ℝ))
    (changed_ne_exact : changed ≠ smoothLieGroupScalarToContinuousLinearMap
      (twoDimensionalSelectedLoopSmoothMatrixCoefficientDifferenceQuotientEvolution
        (heatTraceData := heatTraceData) t coefficients))
    (claimed : twoDimensionalSelectedLoopHeatDifferenceQuotientLinearMap bridge t
      (smoothLieGroupScalarToContinuousLinearMap
        (smoothUnitaryMatrixCoefficientRealSynthesis coefficients)) = changed) : False :=
  changed_ne_exact (claimed.symm.trans
    (twoDimensionalSelectedLoopHeatDifferenceQuotient_smoothMatrixCoefficientSynthesis
      bridge t ht coefficients))

omit [FiniteDimensional ℝ E] [MeasurableMul₂ G] [MeasurableInv G] in
include bridge in
/-- Exact derived real pairing-Laplacian eigenvalue probe. -/
theorem exact_selectedLoop_smoothMatrixCoefficient_laplacian
    (index : SmoothUnitaryMatrixCoefficientRealIndex E G) (g : G) :
    realLaplacian.laplacian (smoothUnitaryMatrixCoefficientRealFunction index) g =
      -(heatTraceData.casimirWeight (unitaryMatrixDualClass
        index.representation.toContinuousUnitaryIrreducibleMatrixRepresentation)) *
        smoothUnitaryMatrixCoefficientRealFunction index g :=
  twoDimensionalSelectedLoop_smoothMatrixCoefficient_laplacian bridge index g

omit [FiniteDimensional ℝ E] [MeasurableMul₂ G] [MeasurableInv G] in
include bridge in
/-- Hostile derived-Laplacian probe: changing the selected eigenvalue output is contradictory. -/
theorem changed_selectedLoop_smoothMatrixCoefficient_laplacian_blocked
    (index : SmoothUnitaryMatrixCoefficientRealIndex E G) (g : G) (changed : ℝ)
    (changed_ne_exact : changed ≠
      -(heatTraceData.casimirWeight (unitaryMatrixDualClass
        index.representation.toContinuousUnitaryIrreducibleMatrixRepresentation)) *
        smoothUnitaryMatrixCoefficientRealFunction index g)
    (claimed : realLaplacian.laplacian
      (smoothUnitaryMatrixCoefficientRealFunction index) g = changed) : False := by
  apply changed_ne_exact
  rw [← claimed]
  exact twoDimensionalSelectedLoop_smoothMatrixCoefficient_laplacian bridge index g

omit [FiniteDimensional ℝ E] [MeasurableMul₂ G] [MeasurableInv G] in
include bridge in
/-- Exact constructed complex coefficientwise Casimir-bridge probe. -/
theorem exact_selectedLoop_constructedCoefficientCasimirBridge
    (ρ : SmoothUnitaryIrreducibleMatrixRepresentation E G)
    (row column : Fin ρ.dimension) (g : G) :
    complexLaplacian.laplacian (smoothUnitaryMatrixCoefficient ρ row column) g =
      -(heatTraceData.casimirWeight (unitaryMatrixDualClass
        ρ.toContinuousUnitaryIrreducibleMatrixRepresentation) : ℂ) *
        smoothUnitaryMatrixCoefficient ρ row column g :=
  SmoothUnitaryMatrixCoefficientCasimirLaplacianBridgeData.laplacian_smoothCoefficient
    (twoDimensionalSelectedLoopCoefficientCasimirLaplacianBridgeData bridge)
    ρ row column g

omit [FiniteDimensional ℝ E] [MeasurableMul₂ G] [MeasurableInv G] in
/-- Exact uniform-norm zero-time generator probe for either real component. -/
theorem exact_selectedLoop_smoothMatrixCoefficient_generator
    (index : SmoothUnitaryMatrixCoefficientRealIndex E G) :
    Tendsto (fun t : NNReal =>
      twoDimensionalSelectedLoopHeatDifferenceQuotientLinearMap bridge t
        (smoothLieGroupScalarToContinuousLinearMap
          (smoothUnitaryMatrixCoefficientRealFunction index)))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (twoDimensionalSelectedLoopPairingGeneratorLinearMap
        (realLaplacian := realLaplacian)
        (smoothUnitaryMatrixCoefficientRealFunction index))) :=
  tendsto_twoDimensionalSelectedLoop_smoothMatrixCoefficient_generator
    bridge index

omit [FiniteDimensional ℝ E] [MeasurableMul₂ G] [MeasurableInv G] in
/-- Exact finite-synthesis generator probe. -/
theorem exact_selectedLoop_smoothMatrixCoefficientSynthesis_generator
    (coefficients : SmoothUnitaryMatrixCoefficientRealCoefficients E G) :
    Tendsto (fun t : NNReal =>
      twoDimensionalSelectedLoopHeatDifferenceQuotientLinearMap bridge t
        (smoothLieGroupScalarToContinuousLinearMap
          (smoothUnitaryMatrixCoefficientRealSynthesis coefficients)))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (twoDimensionalSelectedLoopPairingGeneratorLinearMap
        (realLaplacian := realLaplacian)
        (smoothUnitaryMatrixCoefficientRealSynthesis coefficients))) :=
  tendsto_twoDimensionalSelectedLoop_smoothMatrixCoefficientSynthesis_generator
    bridge coefficients

omit [FiniteDimensional ℝ E] [MeasurableMul₂ G] [MeasurableInv G] in
/-- Exact fixed-range `core_generator` probe. -/
theorem exact_selectedLoop_smoothMatrixCoefficientCore_generator :
    ∀ f ∈ smoothUnitaryMatrixCoefficientRealCoreCandidate (E := E) (G := G),
      Tendsto (fun t : NNReal =>
        twoDimensionalSelectedLoopHeatDifferenceQuotientLinearMap bridge t
          (smoothLieGroupScalarToContinuousLinearMap f))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (twoDimensionalSelectedLoopPairingGeneratorLinearMap
          (realLaplacian := realLaplacian) f)) :=
  twoDimensionalSelectedLoop_smoothMatrixCoefficientCore_generator
    bridge

omit [FiniteDimensional ℝ E] [MeasurableMul₂ G] [MeasurableInv G] in
/-- Exact strong right-continuity probe on the designated finite coefficient core only. -/
theorem exact_selectedLoop_smoothMatrixCoefficientCore_heatOperator_tendsto_zero
    (f : SmoothLieGroupScalarFunction (E := E) (G := G))
    (hf : f ∈ smoothUnitaryMatrixCoefficientRealCoreCandidate (E := E) (G := G)) :
    Tendsto (fun t : NNReal =>
      twoDimensionalSelectedLoopHeatOperatorContinuousLinearMap bridge t
        (smoothLieGroupScalarToContinuousLinearMap f))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (smoothLieGroupScalarToContinuousLinearMap f)) :=
  twoDimensionalSelectedLoop_smoothMatrixCoefficientCore_heatOperator_tendsto_zero
    bridge f hf

omit [FiniteDimensional ℝ E] [MeasurableMul₂ G] [MeasurableInv G] in
/-- Exact contraction extension to the uniform closure of the continuous coefficient-core image. -/
theorem exact_selectedLoop_smoothMatrixCoefficientCore_heatOperator_tendsto_zero_on_closure
    (f : C(G, ℝ))
    (hf : f ∈ closure
      (smoothLieGroupScalarToContinuousLinearMap ''
        smoothUnitaryMatrixCoefficientRealCoreCandidate (E := E) (G := G))) :
    Tendsto (fun t : NNReal =>
      twoDimensionalSelectedLoopHeatOperatorContinuousLinearMap bridge t f)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds f) :=
  twoDimensionalSelectedLoop_smoothMatrixCoefficientCore_heatOperator_tendsto_zero_of_mem_closure
    bridge f hf

omit [FiniteDimensional ℝ E] [MeasurableMul₂ G] [MeasurableInv G] in
/-- Exact Peter–Weyl-facing bridge: uniform density of the smooth coefficient image would give
strong right-continuity on every continuous function. -/
theorem exact_selectedLoop_smoothMatrixCoefficientCore_heatOperator_tendsto_zero_of_dense
    (dense : Dense
      (smoothLieGroupScalarToContinuousLinearMap ''
        smoothUnitaryMatrixCoefficientRealCoreCandidate (E := E) (G := G))) :
    ∀ f : C(G, ℝ), Tendsto (fun t : NNReal =>
      twoDimensionalSelectedLoopHeatOperatorContinuousLinearMap bridge t f)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds f) :=
  twoDimensionalSelectedLoop_smoothMatrixCoefficientCore_heatOperator_tendsto_zero_of_dense
    bridge dense

omit [FiniteDimensional ℝ E] [MeasurableMul₂ G] [MeasurableInv G] in
/-- Exact Fourier-to-semigroup bridge under selected continuous density and smooth-dual coverage. -/
theorem exact_selectedLoop_heatOperator_tendsto_zero_of_continuousPeterWeyl_of_smoothCoverage
    (continuousDensity : UnitaryMatrixDual.HasContinuousPeterWeylDensity G)
    (smoothCoverage : ∀ q : UnitaryMatrixDual G,
      q.HasSmoothRepresentative (E := E)) :
    ∀ f : C(G, ℝ), Tendsto (fun t : NNReal =>
      twoDimensionalSelectedLoopHeatOperatorContinuousLinearMap bridge t f)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds f) :=
  twoDimensionalSelectedLoop_heatOperator_tendsto_zero_of_continuousPeterWeyl_of_smoothCoverage
    bridge continuousDensity smoothCoverage

omit [FiniteDimensional ℝ E] [MeasurableMul₂ G] [MeasurableInv G] in
/-- Exact automatic-smoothness Fourier-to-semigroup specialization. -/
theorem exact_selectedLoop_heatOperator_tendsto_zero_of_continuousPeterWeyl_of_automaticSmoothness
    (continuousDensity : UnitaryMatrixDual.HasContinuousPeterWeylDensity G)
    (automaticSmoothness :
      AllContinuousUnitaryIrreducibleMatrixRepresentationsHaveSmoothCoordinates
        (E := E) (G := G)) :
    ∀ f : C(G, ℝ), Tendsto (fun t : NNReal =>
      twoDimensionalSelectedLoopHeatOperatorContinuousLinearMap bridge t f)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds f) :=
  twoDimensionalSelectedLoop_heatOperator_tendsto_zero_of_continuousPeterWeyl_of_automaticSmoothness
    bridge continuousDensity automaticSmoothness

omit [FiniteDimensional ℝ E] [MeasurableMul₂ G] [MeasurableInv G] in
/-- Hostile Fourier-to-semigroup probe: failure of strong continuity at one continuous test blocks
the joint selected-density and smooth-coverage hypotheses. -/
theorem missing_selectedLoop_heatOperator_continuity_blocks_PeterWeyl_smoothCoverage
    (f : C(G, ℝ))
    (missing : ¬ Tendsto (fun t : NNReal =>
      twoDimensionalSelectedLoopHeatOperatorContinuousLinearMap bridge t f)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds f))
    (continuousDensity : UnitaryMatrixDual.HasContinuousPeterWeylDensity G)
    (smoothCoverage : ∀ q : UnitaryMatrixDual G,
      q.HasSmoothRepresentative (E := E)) : False :=
  missing
    (twoDimensionalSelectedLoop_heatOperator_tendsto_zero_of_continuousPeterWeyl_of_smoothCoverage
      bridge continuousDensity smoothCoverage f)

omit [FiniteDimensional ℝ E] [MeasurableMul₂ G] [MeasurableInv G] in
/-- Exact faithful compact matrix-group Fourier-to-semigroup specialization. -/
theorem exact_selectedLoop_heatOperator_tendsto_zero_of_faithful_of_smoothCoverage
    (faithful : ContinuousFaithfulFiniteMatrixRepresentation G)
    (smoothCoverage : ∀ q : UnitaryMatrixDual G,
      q.HasSmoothRepresentative (E := E)) :
    ∀ f : C(G, ℝ), Tendsto (fun t : NNReal =>
      twoDimensionalSelectedLoopHeatOperatorContinuousLinearMap bridge t f)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds f) :=
  twoDimensionalSelectedLoop_heatOperator_tendsto_zero_of_faithful_of_smoothCoverage
    bridge faithful smoothCoverage

omit [FiniteDimensional ℝ E] [MeasurableMul₂ G] [MeasurableInv G] in
/-- Exact faithful-plus-automatic-smoothness Fourier-to-semigroup specialization. -/
theorem exact_selectedLoop_heatOperator_tendsto_zero_of_faithful_of_automaticSmoothness
    (faithful : ContinuousFaithfulFiniteMatrixRepresentation G)
    (automaticSmoothness :
      AllContinuousUnitaryIrreducibleMatrixRepresentationsHaveSmoothCoordinates
        (E := E) (G := G)) :
    ∀ f : C(G, ℝ), Tendsto (fun t : NNReal =>
      twoDimensionalSelectedLoopHeatOperatorContinuousLinearMap bridge t f)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds f) :=
  twoDimensionalSelectedLoop_heatOperator_tendsto_zero_of_faithful_of_automaticSmoothness
    bridge faithful automaticSmoothness

omit [FiniteDimensional ℝ E] [MeasurableMul₂ G] [MeasurableInv G] in
/-- Exact consequence of the still-open graph-density field: zeroth-order strong heat continuity
then holds on every smooth test without using the uniform graph bound. -/
theorem exact_selectedLoop_smoothMatrixCoefficientCore_heatOperator_tendsto_zero_of_graphDense
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
      (nhds (smoothLieGroupScalarToContinuousLinearMap f)) :=
  twoDimensionalSelectedLoop_smoothMatrixCoefficientCore_heatOperator_tendsto_zero_of_graphDense
    bridge graphDense f

omit [FiniteDimensional ℝ E] [MeasurableMul₂ G] [MeasurableInv G] in
/-- Exact pointwise boundedness probe. Its event and bound may depend on the chosen core vector, so
it is not the uniform graph-bound field of the reduction record. -/
theorem exact_selectedLoop_smoothMatrixCoefficientCore_eventually_pointwiseNormBound
    (f : SmoothLieGroupScalarFunction (E := E) (G := G))
    (hf : f ∈ smoothUnitaryMatrixCoefficientRealCoreCandidate (E := E) (G := G)) :
    ∀ᶠ t : NNReal in nhdsWithin 0 (Set.Ioi 0),
      ‖twoDimensionalSelectedLoopHeatDifferenceQuotientLinearMap bridge t
          (smoothLieGroupScalarToContinuousLinearMap f)‖ ≤
        ‖twoDimensionalSelectedLoopPairingGeneratorLinearMap
          (realLaplacian := realLaplacian) f‖ + 1 :=
  twoDimensionalSelectedLoop_smoothMatrixCoefficientCore_eventually_pointwiseNormBound
    bridge f hf

omit [FiniteDimensional ℝ E] [MeasurableMul₂ G] [MeasurableInv G] in
/-- Exact weaker-quantifier probe: each fixed core test has some pointwise graph-bound constant. -/
theorem exact_selectedLoop_smoothMatrixCoefficientCore_exists_eventually_pointwiseGraphBound
    (f : SmoothLieGroupScalarFunction (E := E) (G := G))
    (hf : f ∈ smoothUnitaryMatrixCoefficientRealCoreCandidate (E := E) (G := G)) :
    ∃ Cf : ℝ, 0 ≤ Cf ∧ ∀ᶠ t : NNReal in nhdsWithin 0 (Set.Ioi 0),
      ‖twoDimensionalSelectedLoopHeatDifferenceQuotientLinearMap bridge t
          (smoothLieGroupScalarToContinuousLinearMap f)‖ ≤
        Cf * (‖smoothLieGroupScalarToContinuousLinearMap f‖ +
          ‖twoDimensionalSelectedLoopPairingGeneratorLinearMap
            (realLaplacian := realLaplacian) f‖) :=
  twoDimensionalSelectedLoop_smoothMatrixCoefficientCore_exists_eventually_pointwiseGraphBound
    bridge f hf

omit [FiniteDimensional ℝ E] [MeasurableMul₂ G] [MeasurableInv G] in
/-- Exact Duhamel probe: contraction gives the sharp generator bound and hence the uniform graph
bound with constant one. -/
theorem exact_selectedLoopPairingDuhamel_graphBound
    (data : TwoDimensionalSelectedLoopPairingDuhamelData bridge)
    (t : NNReal) (ht : 0 < t)
    (f : SmoothLieGroupScalarFunction (E := E) (G := G)) :
    IntervalIntegrable (fun s : ℝ =>
        twoDimensionalSelectedLoopHeatOperatorContinuousLinearMap bridge
          (Real.toNNReal s * t)
          (twoDimensionalSelectedLoopPairingGeneratorLinearMap
            (realLaplacian := realLaplacian) f)) MeasureTheory.volume 0 1 ∧
    ‖twoDimensionalSelectedLoopHeatDifferenceQuotientLinearMap bridge t
        (smoothLieGroupScalarToContinuousLinearMap f)‖ ≤
      ‖twoDimensionalSelectedLoopPairingGeneratorLinearMap
        (realLaplacian := realLaplacian) f‖ ∧
    (∀ᶠ t : NNReal in nhdsWithin 0 (Set.Ioi 0),
      ∀ f : SmoothLieGroupScalarFunction (E := E) (G := G),
        ‖twoDimensionalSelectedLoopHeatDifferenceQuotientLinearMap bridge t
            (smoothLieGroupScalarToContinuousLinearMap f)‖ ≤
          1 * (‖smoothLieGroupScalarToContinuousLinearMap f‖ +
            ‖twoDimensionalSelectedLoopPairingGeneratorLinearMap
              (realLaplacian := realLaplacian) f‖)) :=
  ⟨data.trajectory_intervalIntegrable t f,
    data.quotient_norm_le_generator t ht f, data.eventual_graphBound_one⟩

omit [FiniteDimensional ℝ E] [MeasurableMul₂ G] [MeasurableInv G] in
/-- Hostile Duhamel probe: changing the exact averaged heat trajectory is contradictory. -/
theorem changed_selectedLoopPairingDuhamel_blocked
    (data : TwoDimensionalSelectedLoopPairingDuhamelData bridge)
    (t : NNReal) (ht : 0 < t)
    (f : SmoothLieGroupScalarFunction (E := E) (G := G)) (changed : C(G, ℝ))
    (changed_ne_exact : changed ≠
      ∫ s : ℝ in 0..1,
        twoDimensionalSelectedLoopHeatOperatorContinuousLinearMap bridge
          (Real.toNNReal s * t)
          (twoDimensionalSelectedLoopPairingGeneratorLinearMap
            (realLaplacian := realLaplacian) f))
    (claimed : twoDimensionalSelectedLoopHeatDifferenceQuotientLinearMap bridge t
      (smoothLieGroupScalarToContinuousLinearMap f) = changed) : False :=
  changed_ne_exact (claimed.symm.trans (data.duhamel t ht f))

omit [FiniteDimensional ℝ E] [MeasurableMul₂ G] [MeasurableInv G] in
/-- An actual coefficient graph-core witness yields all-smooth strong heat continuity through graph
density, independently of its separate uniform graph-bound field. -/
theorem exact_smoothMatrixCoefficientGraphCore_allSmooth_heatOperator_tendsto_zero
    (data : TwoDimensionalSelectedLoopSmoothMatrixCoefficientGraphCoreData bridge)
    (f : SmoothLieGroupScalarFunction (E := E) (G := G)) :
    Tendsto (fun t : NNReal =>
      twoDimensionalSelectedLoopHeatOperatorContinuousLinearMap bridge t
        (smoothLieGroupScalarToContinuousLinearMap f))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (smoothLieGroupScalarToContinuousLinearMap f)) :=
  data.allSmooth_heatOperator_tendsto_zero f

omit [FiniteDimensional ℝ E] [MeasurableMul₂ G] [MeasurableInv G] in
/-- The coefficient-specific reduction uses exactly the constructed matrix-coefficient range. -/
theorem exact_smoothMatrixCoefficientGraphCore_reduction_core
    (data : TwoDimensionalSelectedLoopSmoothMatrixCoefficientGraphCoreData bridge) :
    data.toPairingGraphCoreGeneratorData.core =
      smoothUnitaryMatrixCoefficientRealCoreCandidate (E := E) (G := G) :=
  rfl

omit [FiniteDimensional ℝ E] [IsTopologicalGroup G] [T2Space G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    [MeasurableMul₂ G] [MeasurableInv G] in
/-- Exact Fourier-facing graph-density probe: one finite synthesis must approximate both graph
coordinates simultaneously. -/
theorem exact_smoothMatrixCoefficient_graphDense_iff_finiteSynthesis_graphApproximation :
    IsLinearMapDomainGraphDenseCore
      smoothLieGroupScalarToContinuousLinearMap
      (twoDimensionalSelectedLoopPairingGeneratorLinearMap
        (realLaplacian := realLaplacian))
      (smoothUnitaryMatrixCoefficientRealCoreCandidate (E := E) (G := G)) ↔
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
                (smoothUnitaryMatrixCoefficientRealSynthesis coefficients)‖ < ε :=
  smoothMatrixCoefficient_graphDense_iff_finiteSynthesis_graphApproximation

omit [FiniteDimensional ℝ E] [MeasurableMul₂ G] [MeasurableInv G] in
/-- Hostile Fourier-facing debt probe: failure of simultaneous finite synthesis approximation blocks
the coefficient graph-core record. -/
theorem missing_finiteSynthesis_graphApproximation_blocks_reduction
    (missing : ¬ ∀ f : SmoothLieGroupScalarFunction (E := E) (G := G),
      ∀ ε : ℝ, 0 < ε →
        ∃ coefficients : SmoothUnitaryMatrixCoefficientRealCoefficients E G,
          ‖smoothLieGroupScalarToContinuousLinearMap f -
              smoothLieGroupScalarToContinuousLinearMap
                (smoothUnitaryMatrixCoefficientRealSynthesis coefficients)‖ < ε ∧
            ‖twoDimensionalSelectedLoopPairingGeneratorLinearMap
                (realLaplacian := realLaplacian) f -
              twoDimensionalSelectedLoopPairingGeneratorLinearMap
                (realLaplacian := realLaplacian)
                (smoothUnitaryMatrixCoefficientRealSynthesis coefficients)‖ < ε) :
    ¬ Nonempty (TwoDimensionalSelectedLoopSmoothMatrixCoefficientGraphCoreData bridge) := by
  rintro ⟨data⟩
  apply missing
  exact smoothMatrixCoefficient_graphDense_iff_finiteSynthesis_graphApproximation.mp
    data.graphDense

omit [FiniteDimensional ℝ E] [MeasurableMul₂ G] [MeasurableInv G] in
/-- Exact debt probe: every coefficient-specific reduction supplies graph density for the fixed
matrix-coefficient range. -/
theorem exact_smoothMatrixCoefficientGraphCore_graphDense
    (data : TwoDimensionalSelectedLoopSmoothMatrixCoefficientGraphCoreData bridge) :
    IsLinearMapDomainGraphDenseCore
      smoothLieGroupScalarToContinuousLinearMap
      (twoDimensionalSelectedLoopPairingGeneratorLinearMap
        (realLaplacian := realLaplacian))
      (smoothUnitaryMatrixCoefficientRealCoreCandidate (E := E) (G := G)) :=
  data.graphDense

omit [FiniteDimensional ℝ E] [MeasurableMul₂ G] [MeasurableInv G] in
/-- Hostile debt probe: absent graph density, the reduced coefficient graph-core record is
uninhabitable. -/
theorem missing_smoothMatrixCoefficientGraphDensity_blocks_reduction
    (missing : ¬ IsLinearMapDomainGraphDenseCore
      smoothLieGroupScalarToContinuousLinearMap
      (twoDimensionalSelectedLoopPairingGeneratorLinearMap
        (realLaplacian := realLaplacian))
      (smoothUnitaryMatrixCoefficientRealCoreCandidate (E := E) (G := G))) :
    ¬ Nonempty (TwoDimensionalSelectedLoopSmoothMatrixCoefficientGraphCoreData bridge) := by
  rintro ⟨data⟩
  exact missing data.graphDense

omit [FiniteDimensional ℝ E] [MeasurableMul₂ G] [MeasurableInv G] in
/-- Hostile heat-action probe: a changed real coefficient output is contradictory. -/
theorem changed_selectedLoopHeatOperator_smoothMatrixCoefficient_blocked
    (t : ℝ) (ht : 0 < t) (index : SmoothUnitaryMatrixCoefficientRealIndex E G)
    (changed : C(G, ℝ))
    (changed_ne_exact : changed ≠
      Real.exp (-(t / 2) * heatTraceData.casimirWeight
        (unitaryMatrixDualClass
          index.representation.toContinuousUnitaryIrreducibleMatrixRepresentation)) •
        smoothLieGroupScalarToContinuousLinearMap
          (smoothUnitaryMatrixCoefficientRealFunction index))
    (claimed : bridge.spectralHeatKernel.kernelOperator.heatOperator t
      (smoothLieGroupScalarToContinuousLinearMap
        (smoothUnitaryMatrixCoefficientRealFunction index)) = changed) : False :=
  changed_ne_exact (claimed.symm.trans
    (twoDimensionalSelectedLoopHeatOperator_smoothMatrixCoefficient bridge t ht index))

omit [FiniteDimensional ℝ E] [MeasurableMul₂ G] [MeasurableInv G] in
/-- Hostile generator probe: no changed target shares the uniform-norm right-hand limit. -/
theorem changed_selectedLoop_smoothMatrixCoefficient_generator_blocked
    (index : SmoothUnitaryMatrixCoefficientRealIndex E G) (changed : C(G, ℝ))
    (changed_ne_exact : changed ≠
      twoDimensionalSelectedLoopPairingGeneratorLinearMap
        (realLaplacian := realLaplacian)
        (smoothUnitaryMatrixCoefficientRealFunction index))
    (claimed : Tendsto (fun t : NNReal =>
      twoDimensionalSelectedLoopHeatDifferenceQuotientLinearMap bridge t
        (smoothLieGroupScalarToContinuousLinearMap
          (smoothUnitaryMatrixCoefficientRealFunction index)))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds changed)) : False :=
  changed_ne_exact (tendsto_nhds_unique claimed
    (tendsto_twoDimensionalSelectedLoop_smoothMatrixCoefficient_generator
      bridge index))

end

end Dimensions
end YangMills
