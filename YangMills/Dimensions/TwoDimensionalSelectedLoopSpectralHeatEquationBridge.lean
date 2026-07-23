/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Dimensions.TwoDimensionalSelectedLoopHeatEquation
import YangMills.Dimensions.TwoDimensionalSelectedLoopSpectralDensityBridge
import YangMills.Mathematics.LieGroupRightInvariantRealComplexLaplacianCoherence
import YangMills.Mathematics.UnitaryMatrixDualCasimirHeatEquation

/-!
# Bridge from the spectral heat equation to the selected-loop real heat core

This file extends the exact selected-loop spectral-density bridge through the existing real-valued
Driver heat-equation interface. It keeps the real and complex pairing Laplacians separate and
requires explicit same-pairing coherence under real parts. It also retains the uninhabited
infinite-series interchange datum.

From these exact fields it constructs `TwoDimensionalSelectedLoopHeatEquationCoreData` on the
unchanged selected-loop law and the semigroup certificate already derived from the spectral density.
Strict positivity, the `ENNReal` bridge, spatial smoothness, and `∂ₜQ=½ΔQ` are all inherited or
derived; none is duplicated as a new conclusion field.

No coherence/interchange inhabitant, density, Brownian motion, or Yang–Mills measure is constructed.
-/

namespace YangMills
namespace Dimensions

open YangMills.Mathematics
open scoped Manifold ContDiff

noncomputable section

universe uE uG uGauge uSample uConnection

variable
    {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G] [ChartedSpace E G]
    [LieGroup (modelWithCornersSelf ℝ E) ∞ G]
    {Gauge : Type uGauge} [Group Gauge]
    {Sample : Type uSample} [MeasurableSpace Sample]
    {Connection : Type uConnection}
    {base : TwoDimensionalGaugeFixedHolonomyMeasureData G Gauge Sample Connection}
    {law : TwoDimensionalSelectedLoopHaarDensityLawData base}
    {inner : Geometry.InvariantInnerProductData
      (I := modelWithCornersSelf ℝ E) (G := G)}
    {realLaplacian : RightInvariantPairingLaplacianData inner}
    {complexLaplacian : RightInvariantPairingComplexLaplacianData inner}
    {heatTraceData : UnitaryMatrixDualHeatTraceSummabilityData (G := G)}

/-- Exact remaining coherence needed to transport the complex spectral heat equation to the
unchanged real selected-loop heat interface. -/
structure TwoDimensionalSelectedLoopSpectralHeatEquationBridgeData where
  spectralDensityBridge : TwoDimensionalSelectedLoopSpectralDensityBridgeData
    (law := law) (inner := inner) (laplacianData := complexLaplacian)
    (heatTraceData := heatTraceData)
  laplacianCoherence : RightInvariantPairingRealComplexLaplacianCoherenceData
    inner realLaplacian complexLaplacian
  heatEquationInterchange : UnitaryMatrixDualCasimirHeatEquationInterchangeData
    spectralDensityBridge.casimirBridge

namespace TwoDimensionalSelectedLoopSpectralHeatEquationBridgeData

/-- The spectral heat bridge constructs the existing real selected-loop heat-equation core on the
unchanged law, derived spectral semigroup, and unchanged real pairing Laplacian. -/
noncomputable def toHeatEquationCoreData
    (bridge : TwoDimensionalSelectedLoopSpectralHeatEquationBridgeData
      (law := law) (inner := inner) (realLaplacian := realLaplacian)
      (complexLaplacian := complexLaplacian) (heatTraceData := heatTraceData)) :
    TwoDimensionalSelectedLoopHeatEquationCoreData inner law
      bridge.spectralDensityBridge.toConvolutionSemigroupData realLaplacian where
  densityReal := unitaryMatrixDualCasimirHeatDensityReal heatTraceData
  densityReal_spatialSmooth := by
    intro t ht
    exact (bridge.heatEquationInterchange.smoothHeatCharacterSeries t ht).realPart.contMDiff
  densityReal_pos := by
    intro t ht g
    exact unitaryMatrixDualCasimirHeatDensityReal_pos heatTraceData
      bridge.spectralDensityBridge.positivity ht g
  densityReal_toENNReal := by
    intro t ht g
    exact (bridge.spectralDensityBridge.selectedAreaDensity_eq t ht g).symm
  heatEquation := by
    intro t ht g
    have hc := bridge.heatEquationInterchange.hasDerivAt_heatCharacterSeries_eq_half_laplacian
      t ht g
    have hr : HasDerivAt
        (fun s => unitaryMatrixDualCasimirHeatDensityReal heatTraceData s g)
        (((1 / 2 : ℂ) * complexLaplacian.laplacian
          (bridge.heatEquationInterchange.smoothHeatCharacterSeries t ht) g).re) t := by
      have hconst : HasDerivAt (fun _ : ℝ => Complex.reCLM) 0 t := hasDerivAt_const t _
      have hmapped := hconst.clm_apply hc
      simpa [unitaryMatrixDualCasimirHeatDensityReal] using hmapped
    apply hr.congr_deriv
    have hcoh := bridge.laplacianCoherence.laplacian_realPart
      (bridge.heatEquationInterchange.smoothHeatCharacterSeries t ht) g
    change (((1 / 2 : ℂ) * complexLaplacian.laplacian
      (bridge.heatEquationInterchange.smoothHeatCharacterSeries t ht) g).re) =
      (1 / 2 : ℝ) * realLaplacian.laplacian
        (bridge.heatEquationInterchange.smoothHeatCharacterSeries t ht).realPart g
    rw [hcoh]
    norm_num

end TwoDimensionalSelectedLoopSpectralHeatEquationBridgeData

end

end Dimensions
end YangMills
