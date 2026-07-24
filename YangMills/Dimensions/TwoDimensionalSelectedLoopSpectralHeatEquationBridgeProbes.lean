/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Dimensions.TwoDimensionalSelectedLoopSpectralHeatEquationBridge

/-!
# Hostile probes for the selected-loop spectral heat-equation bridge
-/

namespace YangMills
namespace Dimensions
namespace TwoDimensionalSelectedLoopSpectralHeatEquationBridge
namespace Probes

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

omit [FiniteDimensional ℝ E] [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] in
/-- The bridge exposes exact same-pairing real/complex Laplacian coherence. -/
theorem exact_laplacian_coherence
    (f : SmoothLieGroupComplexFunction (E := E) (G := G)) (g : G) :
    realLaplacian.laplacian f.realPart g =
      (complexLaplacian.laplacian f g).re :=
  (rightInvariantPairingRealComplexLaplacianCoherenceData
    realLaplacian complexLaplacian).laplacian_realPart f g

/-- The resulting heat core is attached to the unchanged selected-loop law and derived spectral
semigroup certificate. -/
noncomputable def exact_heat_core
    (bridge : TwoDimensionalSelectedLoopSpectralHeatEquationBridgeData
      (law := law) (inner := inner) (realLaplacian := realLaplacian)
      (complexLaplacian := complexLaplacian) (heatTraceData := heatTraceData)) :
    TwoDimensionalSelectedLoopHeatEquationCoreData inner law
      bridge.spectralDensityBridge.toConvolutionSemigroupData realLaplacian :=
  bridge.toHeatEquationCoreData

omit [FiniteDimensional ℝ E] in
/-- The constructed real density is literally the spectral real density. -/
theorem exact_heat_core_density
    (bridge : TwoDimensionalSelectedLoopSpectralHeatEquationBridgeData
      (law := law) (inner := inner) (realLaplacian := realLaplacian)
      (complexLaplacian := complexLaplacian) (heatTraceData := heatTraceData))
    (t : ℝ) (g : G) :
    bridge.toHeatEquationCoreData.densityReal t g =
      unitaryMatrixDualCasimirHeatDensityReal heatTraceData t g :=
  rfl

omit [FiniteDimensional ℝ E] in
/-- Strict positivity is inherited from the exact spectral positivity datum. -/
theorem exact_heat_core_positive
    (bridge : TwoDimensionalSelectedLoopSpectralHeatEquationBridgeData
      (law := law) (inner := inner) (realLaplacian := realLaplacian)
      (complexLaplacian := complexLaplacian) (heatTraceData := heatTraceData))
    (t : ℝ) (ht : 0 < t) (g : G) :
    0 < bridge.toHeatEquationCoreData.densityReal t g :=
  bridge.toHeatEquationCoreData.densityReal_pos t ht g

omit [FiniteDimensional ℝ E] in
/-- The constructed real density maps to the unchanged selected-loop `ENNReal` density. -/
theorem exact_heat_core_ennreal_bridge
    (bridge : TwoDimensionalSelectedLoopSpectralHeatEquationBridgeData
      (law := law) (inner := inner) (realLaplacian := realLaplacian)
      (complexLaplacian := complexLaplacian) (heatTraceData := heatTraceData))
    (t : ℝ) (ht : 0 < t) (g : G) :
    ENNReal.ofReal (bridge.toHeatEquationCoreData.densityReal t g) =
      law.selectedAreaDensity t g :=
  bridge.toHeatEquationCoreData.densityReal_toENNReal t ht g

omit [FiniteDimensional ℝ E] in
/-- The real Driver heat equation is derived on the unchanged pairing Laplacian. -/
theorem exact_real_heat_equation
    (bridge : TwoDimensionalSelectedLoopSpectralHeatEquationBridgeData
      (law := law) (inner := inner) (realLaplacian := realLaplacian)
      (complexLaplacian := complexLaplacian) (heatTraceData := heatTraceData))
    (t : ℝ) (ht : 0 < t) (g : G) :
    HasDerivAt (fun s => bridge.toHeatEquationCoreData.densityReal s g)
      ((1 / 2 : ℝ) * realLaplacian.laplacian
        (bridge.toHeatEquationCoreData.smoothDensityAt t ht) g) t :=
  bridge.toHeatEquationCoreData.hasDerivAt_densityReal t ht g

omit [FiniteDimensional ℝ E] in
/-- Hostile heat-equation probe: a changed derivative value is contradictory. -/
theorem changed_real_heat_equation_blocked
    (bridge : TwoDimensionalSelectedLoopSpectralHeatEquationBridgeData
      (law := law) (inner := inner) (realLaplacian := realLaplacian)
      (complexLaplacian := complexLaplacian) (heatTraceData := heatTraceData))
    (t : ℝ) (ht : 0 < t) (g : G) (changed : ℝ)
    (hchanged : changed ≠ (1 / 2 : ℝ) * realLaplacian.laplacian
      (bridge.toHeatEquationCoreData.smoothDensityAt t ht) g)
    (changedDerivative : HasDerivAt
      (fun s => bridge.toHeatEquationCoreData.densityReal s g) changed t) : False := by
  apply hchanged
  exact HasDerivAt.unique changedDerivative
    (bridge.toHeatEquationCoreData.hasDerivAt_densityReal t ht g)

end

end Probes
end TwoDimensionalSelectedLoopSpectralHeatEquationBridge
end Dimensions
end YangMills
