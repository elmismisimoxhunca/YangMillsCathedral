/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Dimensions.TwoDimensionalSelectedLoopFinitePastCylinderPiSystem
import Mathlib.Analysis.Calculus.FDeriv.Extend
import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# Selected-loop stochastic generator at time zero

Positive-time heat differentiation is already part of the spectral Brownian bridge. The genuine
stochastic generator additionally requires a right-hand difference-quotient limit at elapsed time
zero on smooth tests. This module states that remaining boundary regularity precisely and proves
that it is equivalent to the corresponding Brownian right-increment expectation limit.
-/

namespace YangMills.Dimensions

open Filter MeasureTheory ProbabilityTheory
open YangMills.Mathematics
open scoped Manifold ContDiff Topology

noncomputable section

universe uE uG uGauge uSample uConnection uΩ

variable
    {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
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

/-- A smooth scalar test packaged as the continuous test required by the heat operator. -/
def smoothLieGroupScalarContinuousMap
    (f : SmoothLieGroupScalarFunction (E := E) (G := G)) : C(G, ℝ) where
  toFun := f
  continuous_toFun := f.contMDiff.continuous

/-- Exact right-hand operator-generator semantics at elapsed time zero. The domain is `NNReal`, so
only physical nonnegative elapsed times occur; `Ioi 0` excludes the zero denominator. -/
def TwoDimensionalSelectedLoopSpectralBrownianGeneratorBridgeData.HasOperatorGeneratorAtZero
    {realLaplacian : RightInvariantPairingLaplacianData inner}
    {complexLaplacian : RightInvariantPairingComplexLaplacianData inner}
    {heatTraceData : UnitaryMatrixDualHeatTraceSummabilityData (G := G)}
    (bridge : TwoDimensionalSelectedLoopSpectralBrownianGeneratorBridgeData
      (law := law) (inner := inner) (realLaplacian := realLaplacian)
      (complexLaplacian := complexLaplacian) (heatTraceData := heatTraceData) (Ω := Ω)) : Prop :=
  ∀ (f : SmoothLieGroupScalarFunction (E := E) (G := G)) (g : G),
    Tendsto
      (fun t : NNReal =>
        (bridge.spectralHeatKernel.kernelOperator.heatOperator (t : ℝ)
            (smoothLieGroupScalarContinuousMap f) g - f g) / (t : ℝ))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds ((1 / 2 : ℝ) * realLaplacian.laplacian f g))

/-- Exact Brownian right-increment difference-quotient semantics. It quantifies over every
deterministic base time and group point and uses the unchanged process measure. -/
def TwoDimensionalSelectedLoopSpectralBrownianGeneratorBridgeData.HasStochasticRightIncrementGeneratorAtZero
    {realLaplacian : RightInvariantPairingLaplacianData inner}
    {complexLaplacian : RightInvariantPairingComplexLaplacianData inner}
    {heatTraceData : UnitaryMatrixDualHeatTraceSummabilityData (G := G)}
    (bridge : TwoDimensionalSelectedLoopSpectralBrownianGeneratorBridgeData
      (law := law) (inner := inner) (realLaplacian := realLaplacian)
      (complexLaplacian := complexLaplacian) (heatTraceData := heatTraceData) (Ω := Ω)) : Prop :=
  ∀ (s : NNReal) (f : SmoothLieGroupScalarFunction (E := E) (G := G)) (g : G),
    Tendsto
      (fun t : NNReal =>
        ((∫ samplePoint,
            f (g * ((bridge.brownian.process s samplePoint)⁻¹ *
              bridge.brownian.process (s + t) samplePoint))
            ∂bridge.brownian.probabilityMeasure) - f g) / (t : ℝ))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds ((1 / 2 : ℝ) * realLaplacian.laplacian f g))

/-- Scalar heat trajectory for one smooth test and one deterministic group point. -/
def twoDimensionalSelectedLoopHeatTrajectory
    {realLaplacian : RightInvariantPairingLaplacianData inner}
    {complexLaplacian : RightInvariantPairingComplexLaplacianData inner}
    {heatTraceData : UnitaryMatrixDualHeatTraceSummabilityData (G := G)}
    (bridge : TwoDimensionalSelectedLoopSpectralBrownianGeneratorBridgeData
      (law := law) (inner := inner) (realLaplacian := realLaplacian)
      (complexLaplacian := complexLaplacian) (heatTraceData := heatTraceData) (Ω := Ω))
    (f : SmoothLieGroupScalarFunction (E := E) (G := G)) (g : G) (t : ℝ) : ℝ :=
  bridge.spectralHeatKernel.kernelOperator.heatOperator t
    (smoothLieGroupScalarContinuousMap f) g

omit [FiniteDimensional ℝ E] [MeasurableMul₂ G] [MeasurableInv G] in
/-- Spectral weak convergence to the identity derives right continuity of every scalar heat
trajectory at zero. This is not an additional boundary assumption. -/
theorem TwoDimensionalSelectedLoopSpectralBrownianGeneratorBridgeData.heatTrajectory_tendsto_zero
    {realLaplacian : RightInvariantPairingLaplacianData inner}
    {complexLaplacian : RightInvariantPairingComplexLaplacianData inner}
    {heatTraceData : UnitaryMatrixDualHeatTraceSummabilityData (G := G)}
    (bridge : TwoDimensionalSelectedLoopSpectralBrownianGeneratorBridgeData
      (law := law) (inner := inner) (realLaplacian := realLaplacian)
      (complexLaplacian := complexLaplacian) (heatTraceData := heatTraceData) (Ω := Ω))
    (f : SmoothLieGroupScalarFunction (E := E) (G := G)) (g : G) :
    Tendsto (twoDimensionalSelectedLoopHeatTrajectory bridge f g)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (f g)) := by
  let translatedReal : C(G, ℝ) :=
    ⟨fun x => f (g * x), f.contMDiff.continuous.comp (continuous_const_mul g)⟩
  let translatedComplex : C(G, ℂ) :=
    ⟨fun x => (translatedReal x : ℂ),
      Complex.continuous_ofReal.comp translatedReal.continuous⟩
  have complexLimit :=
    tendsto_integral_casimirHeatProbabilityMeasure_nhdsWithin_zero heatTraceData
      bridge.spectralHeatKernel.heatEquationBridge.spectralDensityBridge.positivity
      bridge.spectralHeatKernel.heatEquationBridge.spectralDensityBridge.initialIdentity
      translatedComplex
  have realLimit : Tendsto
      (fun t => Complex.re
        (∫ x, translatedComplex x
          ∂unitaryMatrixDualCasimirHeatProbabilityMeasure heatTraceData t))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (f g)) := by
    have mapped := (Complex.continuous_re.tendsto (translatedComplex 1)).comp complexLimit
    change Tendsto
      (fun t => Complex.re
        (∫ x, translatedComplex x
          ∂unitaryMatrixDualCasimirHeatProbabilityMeasure heatTraceData t))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (Complex.re (translatedComplex 1))) at mapped
    convert mapped using 1
    simp [translatedComplex, translatedReal]
  apply realLimit.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  change Complex.re
      (∫ x, (translatedReal x : ℂ)
        ∂unitaryMatrixDualCasimirHeatProbabilityMeasure heatTraceData t) =
    bridge.spectralHeatKernel.kernelOperator.heatOperator t
      (smoothLieGroupScalarContinuousMap f) g
  rw [integral_complex_ofReal, Complex.ofReal_re]
  exact (bridge.generated_operator_eq_spectralMeasureIntegral t ht
    (smoothLieGroupScalarContinuousMap f) g).symm

/-- Positive-time derivative value, extended at nonpositive times by the desired boundary value.
Only its restriction to `Ioi 0` matters in the boundary limit. -/
def twoDimensionalSelectedLoopExtendedPairingGenerator
    {realLaplacian : RightInvariantPairingLaplacianData inner}
    {complexLaplacian : RightInvariantPairingComplexLaplacianData inner}
    {heatTraceData : UnitaryMatrixDualHeatTraceSummabilityData (G := G)}
    (bridge : TwoDimensionalSelectedLoopSpectralBrownianGeneratorBridgeData
      (law := law) (inner := inner) (realLaplacian := realLaplacian)
      (complexLaplacian := complexLaplacian) (heatTraceData := heatTraceData) (Ω := Ω))
    (f : SmoothLieGroupScalarFunction (E := E) (G := G)) (g : G) (t : ℝ) : ℝ :=
  if ht : 0 < t then
    (1 / 2 : ℝ) * realLaplacian.laplacian
      (bridge.spectralHeatKernel.kernelOperator.positiveTimeSmooth t ht
        (smoothLieGroupScalarContinuousMap f)) g
  else
    (1 / 2 : ℝ) * realLaplacian.laplacian f g

/-- Reduced boundary-regularity interface. It separates continuity of the heat trajectory from
continuity of its positive-time pairing-Laplacian derivative. Standard one-sided calculus then
constructs the actual zero-time generator. -/
structure TwoDimensionalSelectedLoopGeneratorBoundaryContinuityData
    {realLaplacian : RightInvariantPairingLaplacianData inner}
    {complexLaplacian : RightInvariantPairingComplexLaplacianData inner}
    {heatTraceData : UnitaryMatrixDualHeatTraceSummabilityData (G := G)}
    (bridge : TwoDimensionalSelectedLoopSpectralBrownianGeneratorBridgeData
      (law := law) (inner := inner) (realLaplacian := realLaplacian)
      (complexLaplacian := complexLaplacian) (heatTraceData := heatTraceData) (Ω := Ω)) where
  heatTrajectory_tendsto_zero :
    ∀ (f : SmoothLieGroupScalarFunction (E := E) (G := G)) (g : G),
      Tendsto (twoDimensionalSelectedLoopHeatTrajectory bridge f g)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds (f g))
  pairingGenerator_tendsto_zero :
    ∀ (f : SmoothLieGroupScalarFunction (E := E) (G := G)) (g : G),
      Tendsto (twoDimensionalSelectedLoopExtendedPairingGenerator bridge f g)
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds ((1 / 2 : ℝ) * realLaplacian.laplacian f g))

/-- Irreducible remaining boundary interface: convergence of the positive-time pairing-Laplacian
derivative. Heat-trajectory continuity is derived from the existing spectral initial identity. -/
structure TwoDimensionalSelectedLoopPairingGeneratorBoundaryContinuityData
    {realLaplacian : RightInvariantPairingLaplacianData inner}
    {complexLaplacian : RightInvariantPairingComplexLaplacianData inner}
    {heatTraceData : UnitaryMatrixDualHeatTraceSummabilityData (G := G)}
    (bridge : TwoDimensionalSelectedLoopSpectralBrownianGeneratorBridgeData
      (law := law) (inner := inner) (realLaplacian := realLaplacian)
      (complexLaplacian := complexLaplacian) (heatTraceData := heatTraceData) (Ω := Ω)) where
  pairingGenerator_tendsto_zero :
    ∀ (f : SmoothLieGroupScalarFunction (E := E) (G := G)) (g : G),
      Tendsto (twoDimensionalSelectedLoopExtendedPairingGenerator bridge f g)
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds ((1 / 2 : ℝ) * realLaplacian.laplacian f g))

omit [FiniteDimensional ℝ E] in
/-- The single pairing-generator boundary field constructs the two-field calculus interface because
spectral weak convergence already supplies heat-trajectory continuity. -/
noncomputable def TwoDimensionalSelectedLoopPairingGeneratorBoundaryContinuityData.toBoundaryContinuityData
    {realLaplacian : RightInvariantPairingLaplacianData inner}
    {complexLaplacian : RightInvariantPairingComplexLaplacianData inner}
    {heatTraceData : UnitaryMatrixDualHeatTraceSummabilityData (G := G)}
    {bridge : TwoDimensionalSelectedLoopSpectralBrownianGeneratorBridgeData
      (law := law) (inner := inner) (realLaplacian := realLaplacian)
      (complexLaplacian := complexLaplacian) (heatTraceData := heatTraceData) (Ω := Ω)}
    (data : TwoDimensionalSelectedLoopPairingGeneratorBoundaryContinuityData bridge) :
    TwoDimensionalSelectedLoopGeneratorBoundaryContinuityData bridge where
  heatTrajectory_tendsto_zero := bridge.heatTrajectory_tendsto_zero
  pairingGenerator_tendsto_zero := data.pairingGenerator_tendsto_zero

/-- Explicit remaining zero-time regularity obligation. Positive-time differentiation alone does
not supply this boundary limit, so no inhabitant is fabricated here. -/
structure TwoDimensionalSelectedLoopStochasticGeneratorAtZeroData
    {realLaplacian : RightInvariantPairingLaplacianData inner}
    {complexLaplacian : RightInvariantPairingComplexLaplacianData inner}
    {heatTraceData : UnitaryMatrixDualHeatTraceSummabilityData (G := G)}
    (bridge : TwoDimensionalSelectedLoopSpectralBrownianGeneratorBridgeData
      (law := law) (inner := inner) (realLaplacian := realLaplacian)
      (complexLaplacian := complexLaplacian) (heatTraceData := heatTraceData) (Ω := Ω)) where
  operatorGeneratorAtZero : bridge.HasOperatorGeneratorAtZero

omit [FiniteDimensional ℝ E] in
/-- One-sided extension of derivatives converts the two explicit boundary-continuity fields into
the genuine zero-time operator-generator difference quotient. -/
noncomputable def TwoDimensionalSelectedLoopGeneratorBoundaryContinuityData.toStochasticGeneratorAtZeroData
    {realLaplacian : RightInvariantPairingLaplacianData inner}
    {complexLaplacian : RightInvariantPairingComplexLaplacianData inner}
    {heatTraceData : UnitaryMatrixDualHeatTraceSummabilityData (G := G)}
    {bridge : TwoDimensionalSelectedLoopSpectralBrownianGeneratorBridgeData
      (law := law) (inner := inner) (realLaplacian := realLaplacian)
      (complexLaplacian := complexLaplacian) (heatTraceData := heatTraceData) (Ω := Ω)}
    (data : TwoDimensionalSelectedLoopGeneratorBoundaryContinuityData bridge) :
    TwoDimensionalSelectedLoopStochasticGeneratorAtZeroData bridge where
  operatorGeneratorAtZero := by
    intro f g
    let trajectory : ℝ → ℝ := twoDimensionalSelectedLoopHeatTrajectory bridge f g
    let generator : ℝ → ℝ :=
      twoDimensionalSelectedLoopExtendedPairingGenerator bridge f g
    have trajectory_diff : DifferentiableOn ℝ trajectory (Set.Ioi 0) := by
      intro t ht
      exact (bridge.generated_operator_hasDerivAt t ht
        (smoothLieGroupScalarContinuousMap f) g).differentiableAt.differentiableWithinAt
    have trajectory_cont : ContinuousWithinAt trajectory (Set.Ioi 0) 0 := by
      change Tendsto trajectory (nhdsWithin 0 (Set.Ioi 0)) (nhds (trajectory 0))
      have trajectory_zero : trajectory 0 = f g := by
        change bridge.spectralHeatKernel.kernelOperator.heatOperator 0
          (smoothLieGroupScalarContinuousMap f) g = f g
        rw [bridge.spectralHeatKernel.kernelOperator.heatOperator_zero]
        rfl
      rw [trajectory_zero]
      exact data.heatTrajectory_tendsto_zero f g
    have deriv_eq_generator :
        (fun t => deriv trajectory t) =ᶠ[nhdsWithin 0 (Set.Ioi 0)] generator := by
      filter_upwards [self_mem_nhdsWithin] with t ht
      have ht_pos : 0 < t := ht
      have derivative := bridge.generated_operator_hasDerivAt t ht_pos
        (smoothLieGroupScalarContinuousMap f) g
      change deriv (fun s => bridge.spectralHeatKernel.kernelOperator.heatOperator s
        (smoothLieGroupScalarContinuousMap f) g) t = generator t
      rw [derivative.deriv]
      dsimp only [generator]
      unfold twoDimensionalSelectedLoopExtendedPairingGenerator
      rw [dif_pos ht_pos]
    have deriv_tendsto : Tendsto (fun t => deriv trajectory t)
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds ((1 / 2 : ℝ) * realLaplacian.laplacian f g)) :=
      (data.pairingGenerator_tendsto_zero f g).congr' deriv_eq_generator.symm
    have atZero : HasDerivWithinAt trajectory
        ((1 / 2 : ℝ) * realLaplacian.laplacian f g) (Set.Ici 0) 0 :=
      hasDerivWithinAt_Ici_of_tendsto_deriv trajectory_diff trajectory_cont
        self_mem_nhdsWithin deriv_tendsto
    have slope_tendsto : Tendsto (slope trajectory 0)
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds ((1 / 2 : ℝ) * realLaplacian.laplacian f g)) :=
      (hasDerivWithinAt_iff_tendsto_slope' (show (0 : ℝ) ∉ Set.Ioi 0 by simp)).mp
        atZero.Ioi_of_Ici
    have coe_tendsto : Tendsto (fun t : NNReal => (t : ℝ))
        (nhdsWithin 0 (Set.Ioi 0)) (nhdsWithin 0 (Set.Ioi 0)) := by
      rw [tendsto_nhdsWithin_iff]
      constructor
      · exact (NNReal.continuous_coe.tendsto 0).mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with t ht
        exact_mod_cast ht
    have quotient_tendsto := slope_tendsto.comp coe_tendsto
    apply quotient_tendsto.congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht_ne : (t : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt ht
    dsimp only [Function.comp_apply, slope, trajectory,
      twoDimensionalSelectedLoopHeatTrajectory, smoothLieGroupScalarContinuousMap]
    rw [bridge.spectralHeatKernel.kernelOperator.heatOperator_zero]
    simp only [vsub_eq_sub, sub_zero, smul_eq_mul]
    rw [div_eq_mul_inv, mul_comm]
    rfl

omit [FiniteDimensional ℝ E] in
/-- The exact positive-time operator/increment expectation identity transports the supplied
zero-time operator generator to the genuine stochastic right-increment generator, for every base
time. -/
theorem TwoDimensionalSelectedLoopStochasticGeneratorAtZeroData.stochasticRightIncrementGeneratorAtZero
    {realLaplacian : RightInvariantPairingLaplacianData inner}
    {complexLaplacian : RightInvariantPairingComplexLaplacianData inner}
    {heatTraceData : UnitaryMatrixDualHeatTraceSummabilityData (G := G)}
    {bridge : TwoDimensionalSelectedLoopSpectralBrownianGeneratorBridgeData
      (law := law) (inner := inner) (realLaplacian := realLaplacian)
      (complexLaplacian := complexLaplacian) (heatTraceData := heatTraceData) (Ω := Ω)}
    (data : TwoDimensionalSelectedLoopStochasticGeneratorAtZeroData bridge) :
    bridge.HasStochasticRightIncrementGeneratorAtZero := by
  intro s f g
  apply (data.operatorGeneratorAtZero f g).congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht_pos : 0 < t := ht
  rw [bridge.generated_operator_eq_rightIncrementExpectation g s t ht_pos
    (smoothLieGroupScalarContinuousMap f)]
  rfl

omit [FiniteDimensional ℝ E] in
/-- Operator and stochastic right-increment zero-time generator semantics are equivalent. The
reverse implication uses one deterministic base time; stationary increments then recover all base
times through the forward implication. -/
theorem TwoDimensionalSelectedLoopSpectralBrownianGeneratorBridgeData.operatorGeneratorAtZero_iff_stochasticRightIncrementGeneratorAtZero
    {realLaplacian : RightInvariantPairingLaplacianData inner}
    {complexLaplacian : RightInvariantPairingComplexLaplacianData inner}
    {heatTraceData : UnitaryMatrixDualHeatTraceSummabilityData (G := G)}
    (bridge : TwoDimensionalSelectedLoopSpectralBrownianGeneratorBridgeData
      (law := law) (inner := inner) (realLaplacian := realLaplacian)
      (complexLaplacian := complexLaplacian) (heatTraceData := heatTraceData) (Ω := Ω)) :
    bridge.HasOperatorGeneratorAtZero ↔ bridge.HasStochasticRightIncrementGeneratorAtZero := by
  constructor
  · intro operatorGenerator
    exact (TwoDimensionalSelectedLoopStochasticGeneratorAtZeroData.mk operatorGenerator).stochasticRightIncrementGeneratorAtZero
  · intro stochasticGenerator f g
    have atBaseZero := stochasticGenerator 0 f g
    apply atBaseZero.congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht_pos : 0 < t := ht
    rw [bridge.generated_operator_eq_rightIncrementExpectation g 0 t ht_pos
      (smoothLieGroupScalarContinuousMap f)]
    rfl

end

end YangMills.Dimensions
