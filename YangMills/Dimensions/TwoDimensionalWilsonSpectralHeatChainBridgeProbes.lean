/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Dimensions.TwoDimensionalWilsonSpectralHeatChainBridge

/-!
# Hostile probes for the Wilson/spectral heat-chain bridge
-/

namespace YangMills
namespace Dimensions
namespace TwoDimensionalWilsonSpectralHeatChainBridge
namespace Probes

open MeasureTheory
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

/-- The bridge yields exactly the existing common chain on the spectral convolution semigroup. -/
noncomputable def exact_common_chain
    (bridge : TwoDimensionalWilsonSpectralHeatChainBridgeData
      (law := law) (inner := inner) (realLaplacian := realLaplacian)
      (complexLaplacian := complexLaplacian) (heatTraceData := heatTraceData)) :
    TwoDimensionalWilsonCommonHeatChainData (E := E)
      bridge.spectralHeatKernel.convolutionSemigroup :=
  bridge.toWilsonCommonHeatChainData

omit [FiniteDimensional ℝ E] in
/-- The common chain retains the exact smooth unitary representation supplied by the bridge. -/
theorem exact_common_representation
    (bridge : TwoDimensionalWilsonSpectralHeatChainBridgeData
      (law := law) (inner := inner) (realLaplacian := realLaplacian)
      (complexLaplacian := complexLaplacian) (heatTraceData := heatTraceData)) :
    bridge.toWilsonCommonHeatChainData.representation = bridge.representation :=
  rfl

omit [FiniteDimensional ℝ E] in
/-- The Wilson action retains the exact representation and normalization connected to the spectral
heat chain. -/
theorem exact_common_wilson_action
    (bridge : TwoDimensionalWilsonSpectralHeatChainBridgeData
      (law := law) (inner := inner) (realLaplacian := realLaplacian)
      (complexLaplacian := complexLaplacian) (heatTraceData := heatTraceData))
    (spacing : PositiveLatticeSpacing) (g : G) :
    ((bridge.toWilsonCommonHeatChainData.wilsonFamily
      bridge.spectralHeatKernel.convolutionSemigroup).actionAt spacing).action g =
      (bridge.normalization.normalizer spacing)⁻¹ *
        Real.exp ((Matrix.trace (bridge.representation.representation g)).re) :=
  bridge.toWilsonCommonHeatChainData.actionAt_formula
    bridge.spectralHeatKernel.convolutionSemigroup spacing g

omit [FiniteDimensional ℝ E] in
/-- The common chain pairing is induced by that exact representation. -/
theorem exact_common_pairing
    (bridge : TwoDimensionalWilsonSpectralHeatChainBridgeData
      (law := law) (inner := inner) (realLaplacian := realLaplacian)
      (complexLaplacian := complexLaplacian) (heatTraceData := heatTraceData))
    (first second : GroupLieAlgebra (modelWithCornersSelf ℝ E) G) :
    bridge.toWilsonCommonHeatChainData.inner.pairing first second =
      twoDimensionalRepresentationTracePairing bridge.representation first second :=
  bridge.toWilsonCommonHeatChainData.inner_pairing_eq_trace
    bridge.spectralHeatKernel.convolutionSemigroup first second

omit [FiniteDimensional ℝ E] in
/-- The common chain kernel is literally the supplied operator for the spectral real density. -/
theorem exact_common_spectral_kernel
    (bridge : TwoDimensionalWilsonSpectralHeatChainBridgeData
      (law := law) (inner := inner) (realLaplacian := realLaplacian)
      (complexLaplacian := complexLaplacian) (heatTraceData := heatTraceData))
    (t : ℝ) (ht : 0 < t) (f : C(G, ℝ)) (g : G) :
    bridge.toWilsonCommonHeatChainData.kernel.heatOperator t f g =
      ∫ h, unitaryMatrixDualCasimirHeatDensityReal heatTraceData t (h⁻¹ * g) * f h
        ∂normalizedCompactHaarMeasure G := by
  simpa only [TwoDimensionalWilsonSpectralHeatChainBridgeData.toWilsonCommonHeatChainData,
    TwoDimensionalSelectedLoopSpectralHeatEquationBridgeData.toHeatEquationCoreData]
    using bridge.spectralHeatKernel.kernelOperator.heatOperator_eq_kernelIntegral t ht f g

omit [FiniteDimensional ℝ E] in
/-- Hostile common-chain probe: changing the representation-induced pairing is contradictory. -/
theorem changed_common_pairing_blocked
    (bridge : TwoDimensionalWilsonSpectralHeatChainBridgeData
      (law := law) (inner := inner) (realLaplacian := realLaplacian)
      (complexLaplacian := complexLaplacian) (heatTraceData := heatTraceData))
    (first second : GroupLieAlgebra (modelWithCornersSelf ℝ E) G) (changed : ℝ)
    (hchanged : changed ≠
      twoDimensionalRepresentationTracePairing bridge.representation first second)
    (changedPairing : bridge.toWilsonCommonHeatChainData.inner.pairing first second = changed) :
    False := by
  apply hchanged
  rw [← changedPairing]
  exact exact_common_pairing bridge first second

end

end Probes
end TwoDimensionalWilsonSpectralHeatChainBridge
end Dimensions
end YangMills
