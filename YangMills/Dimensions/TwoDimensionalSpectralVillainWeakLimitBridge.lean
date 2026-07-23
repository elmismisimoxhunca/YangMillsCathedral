/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Dimensions.TwoDimensionalDriverAxialWeakLimit
import YangMills.Dimensions.TwoDimensionalLatticeAction
import YangMills.Dimensions.TwoDimensionalWilsonSpectralHeatChainBridge

/-!
# Spectral Villain bridge to Driver's axial weak limit

The conditional spectral heat construction now reaches the common Wilson chain. Forgetting the
Wilson-only global faithfulness and normalization fields gives exactly Driver's Villain common heat
chain, and its unchanged heat core/kernel define the Villain lattice action `Q_{ε²}`.

This file connects that exact action to the still-uninhabited Driver Theorem 7.2 weak-limit contract.
It does not derive the weak limit: `TwoDimensionalSpectralVillainWeakLimitBridgeData` explicitly
stores the missing theorem for the spectral Villain action at one positive lattice spacing. Derived
normalization, boundary-independent weak convergence, and the exact action formula are then exposed
without duplicating them as assumptions.
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

/-- Exact connection from the common spectral heat chain to Driver's uninhabited axial weak-limit
obligation for the Villain action at `spacing`. -/
structure TwoDimensionalSpectralVillainWeakLimitBridgeData where
  spectralWilson : TwoDimensionalWilsonSpectralHeatChainBridgeData
    (law := law) (inner := inner) (realLaplacian := realLaplacian)
    (complexLaplacian := complexLaplacian) (heatTraceData := heatTraceData)
  weakLimit : TwoDimensionalDriverAxialWeakLimitData spacing
    (TwoDimensionalLatticeActionData.villain
      spectralWilson.spectralHeatKernel.heatEquationCore
      spectralWilson.spectralHeatKernel.kernelOperator spacing)

/-- Exact all-spacing family required before Driver's `ε → 0` Theorem 8.5 comparison can consume
the Theorem 7.2 weak limits. Each spacing remains an explicit supplied weak-limit theorem. -/
structure TwoDimensionalSpectralVillainWeakLimitFamilyBridgeData where
  spectralWilson : TwoDimensionalWilsonSpectralHeatChainBridgeData
    (law := law) (inner := inner) (realLaplacian := realLaplacian)
    (complexLaplacian := complexLaplacian) (heatTraceData := heatTraceData)
  weakLimit : ∀ spacing : PositiveLatticeSpacing,
    TwoDimensionalDriverAxialWeakLimitData spacing
      (TwoDimensionalLatticeActionData.villain
        spectralWilson.spectralHeatKernel.heatEquationCore
        spectralWilson.spectralHeatKernel.kernelOperator spacing)

namespace TwoDimensionalSpectralVillainWeakLimitBridgeData

/-- The exact spectral Villain lattice action used by the weak-limit contract. -/
abbrev villainAction
    (bridge : TwoDimensionalSpectralVillainWeakLimitBridgeData
      (law := law) (inner := inner) (realLaplacian := realLaplacian)
      (complexLaplacian := complexLaplacian) (heatTraceData := heatTraceData)
      (spacing := spacing)) : TwoDimensionalLatticeActionData G :=
  TwoDimensionalLatticeActionData.villain
    bridge.spectralWilson.spectralHeatKernel.heatEquationCore
    bridge.spectralWilson.spectralHeatKernel.kernelOperator spacing

/-- The exact Driver 8.5 common Villain chain obtained by forgetting only Wilson-specific data. -/
noncomputable def villainCommonHeatChain
    (bridge : TwoDimensionalSpectralVillainWeakLimitBridgeData
      (law := law) (inner := inner) (realLaplacian := realLaplacian)
      (complexLaplacian := complexLaplacian) (heatTraceData := heatTraceData)
      (spacing := spacing)) :
    TwoDimensionalVillainCommonHeatChainCoreData (E := E)
      bridge.spectralWilson.spectralHeatKernel.convolutionSemigroup :=
  bridge.spectralWilson.toVillainCommonHeatChainCoreData

/-- Driver's designated common axial limit is normalized, derived from its convergence contract. -/
theorem limitMeasure_normalized
    (bridge : TwoDimensionalSpectralVillainWeakLimitBridgeData
      (law := law) (inner := inner) (realLaplacian := realLaplacian)
      (complexLaplacian := complexLaplacian) (heatTraceData := heatTraceData)
      (spacing := spacing)) :
    bridge.weakLimit.limitMeasure Set.univ = 1 :=
  bridge.weakLimit.limit_normalized

/-- Every axial boundary condition converges weakly to that same normalized spectral-Villain limit. -/
theorem weak_limit_independent_of_boundary
    (bridge : TwoDimensionalSpectralVillainWeakLimitBridgeData
      (law := law) (inner := inner) (realLaplacian := realLaplacian)
      (complexLaplacian := complexLaplacian) (heatTraceData := heatTraceData)
      (spacing := spacing))
    (boundary : EpsilonSquareLatticeAxialConfiguration G spacing) :
    WeaklyConvergesFiniteMeasures
      (fun stage => twoDimensionalSquareLatticeConditionedAxialMeasure spacing
        (driverFiniteVolumeRadius stage) bridge.villainAction boundary)
      bridge.weakLimit.limitMeasure :=
  bridge.weakLimit.weak_limit_independent_of_boundary boundary

end TwoDimensionalSpectralVillainWeakLimitBridgeData

namespace TwoDimensionalSpectralVillainWeakLimitFamilyBridgeData

/-- Exact all-spacing inhabitation debt: one spectral Wilson chain and a Driver Theorem 7.2 weak
limit for its literal Villain action at every positive spacing. -/
theorem nonempty_iff_spectralWilson_weakLimits :
    Nonempty (TwoDimensionalSpectralVillainWeakLimitFamilyBridgeData
      (law := law) (inner := inner) (realLaplacian := realLaplacian)
      (complexLaplacian := complexLaplacian) (heatTraceData := heatTraceData)) ↔
      ∃ spectralWilson : TwoDimensionalWilsonSpectralHeatChainBridgeData
        (law := law) (inner := inner) (realLaplacian := realLaplacian)
        (complexLaplacian := complexLaplacian) (heatTraceData := heatTraceData),
      ∀ spacing : PositiveLatticeSpacing,
        TwoDimensionalDriverAxialWeakLimitObligation spacing
          (TwoDimensionalLatticeActionData.villain
            spectralWilson.spectralHeatKernel.heatEquationCore
            spectralWilson.spectralHeatKernel.kernelOperator spacing) := by
  constructor
  · rintro ⟨family⟩
    refine ⟨family.spectralWilson, fun spacing => ?_⟩
    exact ⟨(family.weakLimit spacing).limitMeasure,
      (family.weakLimit spacing).bounded_continuous_convergence,
      (family.weakLimit spacing).free_finite_volume_identification⟩
  · rintro ⟨spectralWilson, weakLimits⟩
    exact ⟨⟨spectralWilson, fun spacing =>
      let witness := Classical.choose (weakLimits spacing)
      ⟨witness, (Classical.choose_spec (weakLimits spacing)).1,
        (Classical.choose_spec (weakLimits spacing)).2⟩⟩⟩

/-- Restrict the all-spacing family to the exact fixed-spacing bridge. -/
noncomputable def atSpacing
    (family : TwoDimensionalSpectralVillainWeakLimitFamilyBridgeData
      (law := law) (inner := inner) (realLaplacian := realLaplacian)
      (complexLaplacian := complexLaplacian) (heatTraceData := heatTraceData))
    (spacing : PositiveLatticeSpacing) :
    TwoDimensionalSpectralVillainWeakLimitBridgeData
      (law := law) (inner := inner) (realLaplacian := realLaplacian)
      (complexLaplacian := complexLaplacian) (heatTraceData := heatTraceData)
      (spacing := spacing) where
  spectralWilson := family.spectralWilson
  weakLimit := family.weakLimit spacing

/-- Every member of the all-spacing family has a normalized common limit. -/
theorem limitMeasure_normalized
    (family : TwoDimensionalSpectralVillainWeakLimitFamilyBridgeData
      (law := law) (inner := inner) (realLaplacian := realLaplacian)
      (complexLaplacian := complexLaplacian) (heatTraceData := heatTraceData))
    (spacing : PositiveLatticeSpacing) :
    (family.weakLimit spacing).limitMeasure Set.univ = 1 :=
  (family.atSpacing spacing).limitMeasure_normalized

end TwoDimensionalSpectralVillainWeakLimitFamilyBridgeData

end

end Dimensions
end YangMills
