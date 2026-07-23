/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Dimensions.TwoDimensionalSelectedLoopSpectralHeatKernelBridge
import YangMills.Dimensions.TwoDimensionalWilsonCommonHeatChain

/-!
# Common Wilson chain built from the conditional spectral heat bridge

Driver's continuum/lattice comparison requires one unchanged chain from a faithful smooth unitary
representation through its induced invariant pairing and Laplacian to the selected-loop heat kernel.
The spectral development now reaches the real heat equation and an explicit operator-kernel premise.

`TwoDimensionalWilsonSpectralHeatChainBridgeData` retains all representation, faithfulness,
normalization, and pairing-coherence obligations from `TwoDimensionalWilsonCommonHeatChainData`, and
connects them to the same invariant pairing used by the spectral real/complex Laplacians. It then
constructs the existing common heat-chain certificate with the exact semigroup derived from the
spectral density. No representation, operator theorem, continuum law, or Yang–Mills measure is
constructed.
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

/-- Exact representation-to-spectral-heat chain. Every source-facing representation and operator
premise remains explicit. -/
structure TwoDimensionalWilsonSpectralHeatChainBridgeData where
  spectralHeatKernel : TwoDimensionalSelectedLoopSpectralHeatKernelBridgeData
    (law := law) (inner := inner) (realLaplacian := realLaplacian)
    (complexLaplacian := complexLaplacian) (heatTraceData := heatTraceData)
  group_connected : IsConnected (Set.univ : Set G)
  representation : SmoothUnitaryRepresentationDifferentialData (E := E) (G := G)
  representation_faithful : Function.Injective representation.representation
  normalization : TwoDimensionalWilsonNormalizerData
    representation.toFiniteDimensionalUnitaryRepresentationCharacterData
  pairing_coherence :
    TwoDimensionalRepresentationInducedPairingCoherenceData representation inner

namespace TwoDimensionalWilsonSpectralHeatChainBridgeData

/-- Construct the unchanged common Wilson/heat chain with the semigroup derived from the spectral
selected-loop density. -/
noncomputable def toWilsonCommonHeatChainData
    (bridge : TwoDimensionalWilsonSpectralHeatChainBridgeData
      (law := law) (inner := inner) (realLaplacian := realLaplacian)
      (complexLaplacian := complexLaplacian) (heatTraceData := heatTraceData)) :
    TwoDimensionalWilsonCommonHeatChainData (E := E)
      bridge.spectralHeatKernel.convolutionSemigroup where
  group_connected := bridge.group_connected
  representation := bridge.representation
  representation_faithful := bridge.representation_faithful
  normalization := bridge.normalization
  inner := inner
  pairing_coherence := bridge.pairing_coherence
  laplacian := realLaplacian
  heat := bridge.spectralHeatKernel.heatEquationCore
  kernel := bridge.spectralHeatKernel.kernelOperator

end TwoDimensionalWilsonSpectralHeatChainBridgeData

end

end Dimensions
end YangMills
