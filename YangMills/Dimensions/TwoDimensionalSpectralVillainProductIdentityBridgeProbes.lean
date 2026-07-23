/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Dimensions.TwoDimensionalSpectralVillainProductIdentityBridge

/-!
# Hostile probes for the spectral Villain product-identity bridge
-/

namespace YangMills
namespace Dimensions
namespace TwoDimensionalSpectralVillainProductIdentityBridge
namespace Probes

open MeasureTheory
open YangMills.Mathematics
open scoped Manifold ContDiff

noncomputable section

universe uE uG uGauge uSample uConnection
  uVertex uEdge uFace uXAxisCell
  uLargeVertex uLargeEdge uLargeFace uLargeXAxisCell
  uFineVertex uFineEdge uFineFace uFineXAxisCell
  uFineLargeVertex uFineLargeEdge uFineLargeFace uFineLargeXAxisCell

attribute [local instance]
  TwoDimensionalLatticeApproximatingSequenceData.fineEdgeDecidableEq

variable
    {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
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
    {coarse : TwoDimensionalEmbeddedPlanarGraphData.{uVertex, uEdge, uFace, uXAxisCell} base}
    {enlarged : TwoDimensionalEmbeddedPlanarGraphData.{uLargeVertex, uLargeEdge,
      uLargeFace, uLargeXAxisCell} base}
    [DecidableEq coarse.Edge] [DecidableEq enlarged.Edge]
    {axial : TwoDimensionalDriverAxialEnlargementData
      (G := G) (coarse := coarse) (enlarged := enlarged)}
    {coarseApproximation : TwoDimensionalLatticeApproximatingHolonomyData.{uVertex, uEdge,
      uFace, uXAxisCell, uFineVertex, uFineEdge, uFineFace, uFineXAxisCell}
      (base := base) (coarse := coarse)}
    {enlargedApproximation : TwoDimensionalLatticeApproximatingHolonomyData.{uLargeVertex,
      uLargeEdge, uLargeFace, uLargeXAxisCell, uFineLargeVertex, uFineLargeEdge,
      uFineLargeFace, uFineLargeXAxisCell} (base := base) (coarse := enlarged)}
    {faceGeometry : TwoDimensionalDriverAxialLatticeFaceGeometryData
      (axial := axial) (coarseApproximation := coarseApproximation)
      (enlargedApproximation := enlargedApproximation)}

/-- The inhabitance audit exposes the exact all-spacing family and Driver's remaining expectation
identity as separate supplied witnesses. -/
theorem exact_product_inhabitation_audit :
    Nonempty (TwoDimensionalSpectralVillainProductIdentityBridgeData
      (law := law) (inner := inner) (realLaplacian := realLaplacian)
      (complexLaplacian := complexLaplacian) (heatTraceData := heatTraceData)
      (faceGeometry := faceGeometry)) ↔
      ∃ weakLimitFamily : TwoDimensionalSpectralVillainWeakLimitFamilyBridgeData
        (law := law) (inner := inner) (realLaplacian := realLaplacian)
        (complexLaplacian := complexLaplacian) (heatTraceData := heatTraceData),
      TwoDimensionalSpectralVillainProductIdentityObligation
        (faceGeometry := faceGeometry) weakLimitFamily :=
  TwoDimensionalSpectralVillainProductIdentityBridgeData.nonempty_iff_weakLimitFamily_productIdentity

/-- The constructed Driver certificate retains the exact all-spacing spectral weak-limit family. -/
theorem exact_lattice_limit_family
    (bridge : TwoDimensionalSpectralVillainProductIdentityBridgeData
      (law := law) (inner := inner) (realLaplacian := realLaplacian)
      (complexLaplacian := complexLaplacian) (heatTraceData := heatTraceData)
      (faceGeometry := faceGeometry))
    (spacing : PositiveLatticeSpacing) :
    (bridge.toDriverAxialLatticeProductIdentityData.latticeLimit spacing) =
      bridge.weakLimitFamily.weakLimit spacing :=
  rfl

/-- The exact spectral action family is retained without substitution. -/
theorem exact_action_family
    (bridge : TwoDimensionalSpectralVillainProductIdentityBridgeData
      (law := law) (inner := inner) (realLaplacian := realLaplacian)
      (complexLaplacian := complexLaplacian) (heatTraceData := heatTraceData)
      (faceGeometry := faceGeometry))
    (spacing : PositiveLatticeSpacing) (g : G) :
    (spectralVillainActionAt bridge.weakLimitFamily spacing).action g =
      unitaryMatrixDualCasimirHeatDensityReal heatTraceData
        (twoDimensionalVillainTime spacing) g :=
  rfl

/-- The exact product identity derives normalized fine enlarged measures at every spacing. -/
theorem exact_fine_measure_normalized
    (bridge : TwoDimensionalSpectralVillainProductIdentityBridgeData
      (law := law) (inner := inner) (realLaplacian := realLaplacian)
      (complexLaplacian := complexLaplacian) (heatTraceData := heatTraceData)
      (faceGeometry := faceGeometry))
    (spacing : PositiveLatticeSpacing) :
    twoDimensionalFineEnlargedActionMeasure faceGeometry
      (spectralVillainActionAt bridge.weakLimitFamily) spacing Set.univ = 1 :=
  bridge.fineMeasure_univ spacing

/-- Hostile product-identity probe: the exact fine enlarged measure cannot be zero. -/
theorem zero_fine_measure_blocked
    (bridge : TwoDimensionalSpectralVillainProductIdentityBridgeData
      (law := law) (inner := inner) (realLaplacian := realLaplacian)
      (complexLaplacian := complexLaplacian) (heatTraceData := heatTraceData)
      (faceGeometry := faceGeometry))
    (spacing : PositiveLatticeSpacing)
    (zeroMeasure : twoDimensionalFineEnlargedActionMeasure faceGeometry
      (spectralVillainActionAt bridge.weakLimitFamily) spacing = 0) : False := by
  have normalized := bridge.fineMeasure_univ spacing
  rw [zeroMeasure] at normalized
  simp at normalized

end

end Probes
end TwoDimensionalSpectralVillainProductIdentityBridge
end Dimensions
end YangMills
