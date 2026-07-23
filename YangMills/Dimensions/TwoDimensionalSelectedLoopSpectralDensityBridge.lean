/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Dimensions.TwoDimensionalSelectedLoopConvolutionSemigroup
import YangMills.Mathematics.UnitaryMatrixDualCasimirHeatPositiveSemigroup

/-!
# Bridge from the spectral density to the selected two-dimensional loop law

This file connects the reusable compact-group spectral track to the existing source-facing
Driver/Sengupta selected-loop law without replacing either side. The uninhabited
`TwoDimensionalSelectedLoopSpectralDensityBridgeData` requires the law's unchanged `ENNReal`
positive-time density to equal the candidate spectral density pointwise.

Together with the separately explicit geometric Casimir bridge, positivity data, and weak identity
data, that single equality constructs the existing
`TwoDimensionalSelectedLoopConvolutionSemigroupData`: normalization, exact `x⁻¹z` density
convolution, and weak convergence to identity are derived rather than duplicated as fields.

No loop law, spectral premise, bridge, positivity, weak limit, or Yang–Mills measure is constructed.
-/

namespace YangMills
namespace Dimensions

open MeasureTheory Filter
open YangMills.Mathematics
open scoped Manifold ContDiff

noncomputable section

universe uE uG uGauge uSample uConnection

variable
    {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
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
    {laplacianData : RightInvariantPairingComplexLaplacianData inner}
    {heatTraceData : UnitaryMatrixDualHeatTraceSummabilityData (G := G)}

/-- Exact source-facing identification of the unchanged selected-loop density with the conditional
positive spectral density, together with every reusable premise needed to derive its semigroup
certificate. -/
structure TwoDimensionalSelectedLoopSpectralDensityBridgeData where
  casimirBridge : UnitaryMatrixDualCasimirLaplacianBridgeData
    inner laplacianData heatTraceData
  positivity : UnitaryMatrixDualCasimirHeatPositivityData heatTraceData
  initialIdentity : UnitaryMatrixDualCasimirHeatInitialIdentityData heatTraceData
  selectedAreaDensity_eq : ∀ (t : ℝ), 0 < t → ∀ g : G,
    law.selectedAreaDensity t g =
      unitaryMatrixDualCasimirHeatDensityENNReal heatTraceData t g

namespace TwoDimensionalSelectedLoopSpectralDensityBridgeData

/-- The spectral bridge constructs the existing exact selected-loop convolution-semigroup
certificate on the unchanged law and density family. -/
noncomputable def toConvolutionSemigroupData
    (bridge : TwoDimensionalSelectedLoopSpectralDensityBridgeData
      (law := law) (inner := inner) (laplacianData := laplacianData)
      (heatTraceData := heatTraceData)) :
    TwoDimensionalSelectedLoopConvolutionSemigroupData law where
  density_lintegral_normalized := by
    intro t ht
    apply Eq.trans _ (normalizedCompactHaar_lintegral_casimirHeatDensityENNReal
      bridge.casimirBridge bridge.positivity ht)
    apply lintegral_congr
    intro g
    exact bridge.selectedAreaDensity_eq t ht g
  density_add := by
    intro s t hs ht g
    rw [bridge.selectedAreaDensity_eq (s + t) (add_pos hs ht) g]
    have hsf : law.selectedAreaDensity s =
        unitaryMatrixDualCasimirHeatDensityENNReal heatTraceData s := by
      funext x
      exact bridge.selectedAreaDensity_eq s hs x
    have htf : law.selectedAreaDensity t =
        unitaryMatrixDualCasimirHeatDensityENNReal heatTraceData t := by
      funext x
      exact bridge.selectedAreaDensity_eq t ht x
    rw [hsf, htf]
    exact unitaryMatrixDualCasimirHeatDensityENNReal_add
      heatTraceData bridge.positivity hs ht g
  weak_tendsto_identity := by
    intro f
    apply (tendsto_integral_casimirHeatProbabilityMeasure_nhdsWithin_zero
      heatTraceData bridge.positivity bridge.initialIdentity f).congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    rw [unitaryMatrixDualCasimirHeatProbabilityMeasure]
    have hf : unitaryMatrixDualCasimirHeatDensityENNReal heatTraceData t =
        law.selectedAreaDensity t := by
      funext g
      exact (bridge.selectedAreaDensity_eq t ht g).symm
    rw [hf]

end TwoDimensionalSelectedLoopSpectralDensityBridgeData

end

end Dimensions
end YangMills
