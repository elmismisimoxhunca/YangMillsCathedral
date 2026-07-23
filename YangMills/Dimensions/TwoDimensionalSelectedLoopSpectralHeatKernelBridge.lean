/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Dimensions.TwoDimensionalSelectedLoopHeatKernelOperator
import YangMills.Dimensions.TwoDimensionalSelectedLoopSpectralHeatEquationBridge

/-!
# Bridge from the selected-loop spectral heat equation to Driver's heat-kernel operator

The spectral construction now supplies the unchanged real selected-loop heat-equation core. Driver's
Remark 4.13 additionally identifies this density with the integral kernel of the operator generated
by `Δ / 2` on every continuous real test function. That stronger assertion does not follow merely
from the scalar density heat equation.

This file therefore packages the exact connection without hiding the remaining operator theorem:
`TwoDimensionalSelectedLoopSpectralHeatKernelBridgeData` stores the spectral heat-equation bridge and
an explicit `TwoDimensionalSelectedLoopHeatKernelOperatorData` for the heat core it constructs.
No operator, kernel theorem, Brownian process, or Yang–Mills measure is constructed.
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

/-- Exact connection between the conditional spectral heat core and Driver's stronger generated
operator/kernel formula. The operator theorem remains a supplied, uninhabited field. -/
structure TwoDimensionalSelectedLoopSpectralHeatKernelBridgeData where
  heatEquationBridge : TwoDimensionalSelectedLoopSpectralHeatEquationBridgeData
    (law := law) (inner := inner) (realLaplacian := realLaplacian)
    (complexLaplacian := complexLaplacian) (heatTraceData := heatTraceData)
  kernelOperator : TwoDimensionalSelectedLoopHeatKernelOperatorData
    heatEquationBridge.toHeatEquationCoreData

namespace TwoDimensionalSelectedLoopSpectralHeatKernelBridgeData

/-- The unchanged convolution-semigroup certificate derived from the spectral density. -/
abbrev convolutionSemigroup
    (bridge : TwoDimensionalSelectedLoopSpectralHeatKernelBridgeData
      (law := law) (inner := inner) (realLaplacian := realLaplacian)
      (complexLaplacian := complexLaplacian) (heatTraceData := heatTraceData)) :=
  bridge.heatEquationBridge.spectralDensityBridge.toConvolutionSemigroupData

/-- The exact real selected-loop heat core constructed before the stronger operator premise. -/
abbrev heatEquationCore
    (bridge : TwoDimensionalSelectedLoopSpectralHeatKernelBridgeData
      (law := law) (inner := inner) (realLaplacian := realLaplacian)
      (complexLaplacian := complexLaplacian) (heatTraceData := heatTraceData)) :=
  bridge.heatEquationBridge.toHeatEquationCoreData

end TwoDimensionalSelectedLoopSpectralHeatKernelBridgeData

end

end Dimensions
end YangMills
