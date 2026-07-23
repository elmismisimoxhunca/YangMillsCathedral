/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Dimensions.TwoDimensionalSelectedLoopSpectralDensityBridge

/-!
# Hostile probes for the selected-loop spectral-density bridge
-/

namespace YangMills
namespace Dimensions
namespace TwoDimensionalSelectedLoopSpectralDensityBridge
namespace Probes

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

omit [T2Space G] [SecondCountableTopology G] in
/-- The bridge identifies the unchanged selected-loop density pointwise with the spectral density. -/
theorem exact_selected_density
    (bridge : TwoDimensionalSelectedLoopSpectralDensityBridgeData
      (law := law) (inner := inner) (laplacianData := laplacianData)
      (heatTraceData := heatTraceData))
    (t : ℝ) (ht : 0 < t) (g : G) :
    law.selectedAreaDensity t g =
      unitaryMatrixDualCasimirHeatDensityENNReal heatTraceData t g :=
  bridge.selectedAreaDensity_eq t ht g

/-- The constructed certificate is indexed by the exact unchanged loop law. -/
theorem exact_semigroup_certificate
    (bridge : TwoDimensionalSelectedLoopSpectralDensityBridgeData
      (law := law) (inner := inner) (laplacianData := laplacianData)
      (heatTraceData := heatTraceData)) :
    TwoDimensionalSelectedLoopConvolutionSemigroupData law :=
  bridge.toConvolutionSemigroupData

/-- Normalization of the selected-loop density is derived from the spectral bridge. -/
theorem exact_selected_density_normalization
    (bridge : TwoDimensionalSelectedLoopSpectralDensityBridgeData
      (law := law) (inner := inner) (laplacianData := laplacianData)
      (heatTraceData := heatTraceData))
    (t : ℝ) (ht : 0 < t) :
    (∫⁻ g, law.selectedAreaDensity t g ∂normalizedCompactHaarMeasure G) = 1 :=
  bridge.toConvolutionSemigroupData.density_lintegral_normalized t ht

/-- The exact Driver/Sengupta density-addition orientation is derived on the unchanged law. -/
theorem exact_selected_density_add
    (bridge : TwoDimensionalSelectedLoopSpectralDensityBridgeData
      (law := law) (inner := inner) (laplacianData := laplacianData)
      (heatTraceData := heatTraceData))
    (s t : ℝ) (hs : 0 < s) (ht : 0 < t) (g : G) :
    law.selectedAreaDensity (s + t) g =
      normalizedCompactHaarDensityConvolution G
        (law.selectedAreaDensity s) (law.selectedAreaDensity t) g :=
  bridge.toConvolutionSemigroupData.density_add s t hs ht g

/-- Weak identity convergence is derived for the exact selected-loop with-density measures. -/
theorem exact_selected_density_weak_identity
    (bridge : TwoDimensionalSelectedLoopSpectralDensityBridgeData
      (law := law) (inner := inner) (laplacianData := laplacianData)
      (heatTraceData := heatTraceData))
    (f : C(G, ℂ)) :
    Tendsto
      (fun t : ℝ => ∫ g, f g
        ∂((normalizedCompactHaarMeasure G).withDensity (law.selectedAreaDensity t)))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (f 1)) :=
  bridge.toConvolutionSemigroupData.weak_tendsto_identity f

omit [T2Space G] [SecondCountableTopology G] in
/-- Hostile bridge probe: a changed selected density value contradicts exact spectral coherence. -/
theorem changed_selected_density_blocked
    (bridge : TwoDimensionalSelectedLoopSpectralDensityBridgeData
      (law := law) (inner := inner) (laplacianData := laplacianData)
      (heatTraceData := heatTraceData))
    (t : ℝ) (ht : 0 < t) (g : G) (changed : ENNReal)
    (hchanged : changed ≠ unitaryMatrixDualCasimirHeatDensityENNReal heatTraceData t g)
    (changedDensity : law.selectedAreaDensity t g = changed) : False := by
  apply hchanged
  rw [← changedDensity]
  exact bridge.selectedAreaDensity_eq t ht g

end

end Probes
end TwoDimensionalSelectedLoopSpectralDensityBridge
end Dimensions
end YangMills
