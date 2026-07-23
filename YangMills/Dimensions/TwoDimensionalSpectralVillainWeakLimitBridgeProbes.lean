/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Dimensions.FourDimensionalContractSeparation
import YangMills.Dimensions.TwoDimensionalSpectralVillainWeakLimitBridge

/-!
# Hostile probes for the spectral Villain weak-limit bridge
-/

namespace YangMills
namespace Dimensions
namespace TwoDimensionalSpectralVillainWeakLimitBridge
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
    [MeasurableSpace G] [BorelSpace G] [MeasurableMul₂ G] [MeasurableInv G]
    [ChartedSpace E G] [LieGroup (modelWithCornersSelf ℝ E) ∞ G]
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
    {spacing : PositiveLatticeSpacing}

/-- The weak-limit action is literally the Villain action from the spectral heat core. -/
theorem exact_spectral_villain_action
    (bridge : TwoDimensionalSpectralVillainWeakLimitBridgeData
      (law := law) (inner := inner) (realLaplacian := realLaplacian)
      (complexLaplacian := complexLaplacian) (heatTraceData := heatTraceData)
      (spacing := spacing)) (g : G) :
    bridge.villainAction.action g =
      unitaryMatrixDualCasimirHeatDensityReal heatTraceData
        (twoDimensionalVillainTime spacing) g :=
  rfl

/-- Forgetting Wilson-only data preserves the exact spectral heat core and kernel. -/
theorem exact_spectral_villain_common_chain
    (bridge : TwoDimensionalSpectralVillainWeakLimitBridgeData
      (law := law) (inner := inner) (realLaplacian := realLaplacian)
      (complexLaplacian := complexLaplacian) (heatTraceData := heatTraceData)
      (spacing := spacing)) :
    bridge.villainCommonHeatChain.heat =
        bridge.spectralWilson.spectralHeatKernel.heatEquationCore ∧
      bridge.villainCommonHeatChain.kernel =
        bridge.spectralWilson.spectralHeatKernel.kernelOperator :=
  ⟨rfl, rfl⟩

/-- The supplied Driver Theorem 7.2 contract derives a normalized common limit. -/
theorem exact_normalized_limit
    (bridge : TwoDimensionalSpectralVillainWeakLimitBridgeData
      (law := law) (inner := inner) (realLaplacian := realLaplacian)
      (complexLaplacian := complexLaplacian) (heatTraceData := heatTraceData)
      (spacing := spacing)) :
    bridge.weakLimit.limitMeasure Set.univ = 1 :=
  bridge.limitMeasure_normalized

/-- Hostile weak-limit probe: the designated limit cannot be the zero measure. -/
theorem zero_limit_blocked
    (bridge : TwoDimensionalSpectralVillainWeakLimitBridgeData
      (law := law) (inner := inner) (realLaplacian := realLaplacian)
      (complexLaplacian := complexLaplacian) (heatTraceData := heatTraceData)
      (spacing := spacing))
    (zeroLimit : bridge.weakLimit.limitMeasure = 0) : False := by
  have normalized := bridge.limitMeasure_normalized
  rw [zeroLimit] at normalized
  simp at normalized

/-- The all-spacing family restricts to the exact fixed-spacing bridge without changing its weak
limit or spectral action. -/
theorem exact_family_at_spacing
    (family : TwoDimensionalSpectralVillainWeakLimitFamilyBridgeData
      (law := law) (inner := inner) (realLaplacian := realLaplacian)
      (complexLaplacian := complexLaplacian) (heatTraceData := heatTraceData))
    (spacing : PositiveLatticeSpacing) :
    (family.atSpacing spacing).weakLimit = family.weakLimit spacing ∧
      (family.atSpacing spacing).villainAction =
        TwoDimensionalLatticeActionData.villain
          family.spectralWilson.spectralHeatKernel.heatEquationCore
          family.spectralWilson.spectralHeatKernel.kernelOperator spacing :=
  ⟨rfl, rfl⟩

/-- Every supplied member of the all-spacing family has a derived normalized limit. -/
theorem exact_family_normalized
    (family : TwoDimensionalSpectralVillainWeakLimitFamilyBridgeData
      (law := law) (inner := inner) (realLaplacian := realLaplacian)
      (complexLaplacian := complexLaplacian) (heatTraceData := heatTraceData))
    (spacing : PositiveLatticeSpacing) :
    (family.weakLimit spacing).limitMeasure Set.univ = 1 :=
  family.limitMeasure_normalized spacing

/-- This spectral Villain weak-limit bridge is intrinsically two-dimensional and cannot satisfy the
four-dimensional endpoint index. -/
theorem not_four_dimensional :
    ¬ IsFourDimensionalClayEndpoint EuclideanDimension.two :=
  lowerDimension_not_clayEndpoint EuclideanDimension.two (Or.inr (Or.inl rfl))

end

end Probes
end TwoDimensionalSpectralVillainWeakLimitBridge
end Dimensions
end YangMills
