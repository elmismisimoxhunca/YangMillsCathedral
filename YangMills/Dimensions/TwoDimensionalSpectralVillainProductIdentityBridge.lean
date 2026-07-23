/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Dimensions.TwoDimensionalDriverAxialLatticeProductIdentity
import YangMills.Dimensions.TwoDimensionalSpectralVillainWeakLimitBridge

/-!
# Spectral Villain bridge to Driver's enlarged product identity

Driver's Theorem 8.5 proof requires Theorem 7.2 weak limits at every positive lattice spacing and an
exact rewrite of their coarse expectations as the `VB(ε)` tree-frozen product integral. The spectral
weak-limit family supplies the first ingredient for the literal Villain action `Q_{ε²}`.

This file leaves only the second, source-facing product identity as a field and constructs the
existing `TwoDimensionalDriverAxialLatticeProductIdentityData`. No graph family, weak limit, product
identity, or continuum convergence theorem is constructed.
-/

namespace YangMills
namespace Dimensions

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

/-- The exact spectral Villain action family. -/
abbrev spectralVillainActionAt
    (family : TwoDimensionalSpectralVillainWeakLimitFamilyBridgeData
      (law := law) (inner := inner) (realLaplacian := realLaplacian)
      (complexLaplacian := complexLaplacian) (heatTraceData := heatTraceData))
    (spacing : PositiveLatticeSpacing) : TwoDimensionalLatticeActionData G :=
  TwoDimensionalLatticeActionData.villain
    family.spectralWilson.spectralHeatKernel.heatEquationCore
    family.spectralWilson.spectralHeatKernel.kernelOperator spacing

/-- The unresolved source-facing part of Driver's enlarged-product step for an already supplied
all-spacing spectral Villain weak-limit family. Naming this proposition prevents the inhabitance
audit from hiding the remaining theorem inside a record projection. -/
def TwoDimensionalSpectralVillainProductIdentityObligation
    (weakLimitFamily : TwoDimensionalSpectralVillainWeakLimitFamilyBridgeData
      (law := law) (inner := inner) (realLaplacian := realLaplacian)
      (complexLaplacian := complexLaplacian) (heatTraceData := heatTraceData)) : Prop :=
  ∀ spacing (observable : (coarse.Edge → G) → ℝ),
    Measurable observable →
    (∃ bound : ℝ, ∀ configuration, |observable configuration| ≤ bound) →
    (∫ configuration,
      observable (coarseApproximation.coarseRestriction spacing configuration)
        ∂(weakLimitFamily.weakLimit spacing).limitMeasure) =
      ∫ configuration,
        observable (twoDimensionalFineEnlargedCoarseRestriction faceGeometry spacing configuration)
          ∂twoDimensionalFineEnlargedActionMeasure faceGeometry
            (spectralVillainActionAt weakLimitFamily) spacing

/-- Exact missing enlarged-product identity, with all-spacing weak limits already supplied by the
spectral Villain family. -/
structure TwoDimensionalSpectralVillainProductIdentityBridgeData where
  weakLimitFamily : TwoDimensionalSpectralVillainWeakLimitFamilyBridgeData
    (law := law) (inner := inner) (realLaplacian := realLaplacian)
    (complexLaplacian := complexLaplacian) (heatTraceData := heatTraceData)
  expectation_eq_fineEnlargedIntegral :
    TwoDimensionalSpectralVillainProductIdentityObligation
      (faceGeometry := faceGeometry) weakLimitFamily

namespace TwoDimensionalSpectralVillainProductIdentityBridgeData

/-- Exact enlarged-product inhabitation debt: an all-spacing spectral weak-limit family together with
Driver's remaining source-facing expectation identity for that same family. -/
theorem nonempty_iff_weakLimitFamily_productIdentity :
    Nonempty (TwoDimensionalSpectralVillainProductIdentityBridgeData
      (law := law) (inner := inner) (realLaplacian := realLaplacian)
      (complexLaplacian := complexLaplacian) (heatTraceData := heatTraceData)
      (faceGeometry := faceGeometry)) ↔
      ∃ weakLimitFamily : TwoDimensionalSpectralVillainWeakLimitFamilyBridgeData
        (law := law) (inner := inner) (realLaplacian := realLaplacian)
        (complexLaplacian := complexLaplacian) (heatTraceData := heatTraceData),
      TwoDimensionalSpectralVillainProductIdentityObligation
        (faceGeometry := faceGeometry) weakLimitFamily := by
  constructor
  · rintro ⟨bridge⟩
    exact ⟨bridge.weakLimitFamily, bridge.expectation_eq_fineEnlargedIntegral⟩
  · rintro ⟨weakLimitFamily, productIdentity⟩
    exact ⟨⟨weakLimitFamily, productIdentity⟩⟩

/-- Construct Driver's existing product-identity certificate for the exact spectral Villain family. -/
noncomputable def toDriverAxialLatticeProductIdentityData
    (bridge : TwoDimensionalSpectralVillainProductIdentityBridgeData
      (law := law) (inner := inner) (realLaplacian := realLaplacian)
      (complexLaplacian := complexLaplacian) (heatTraceData := heatTraceData)
      (faceGeometry := faceGeometry)) :
    TwoDimensionalDriverAxialLatticeProductIdentityData faceGeometry
      (spectralVillainActionAt bridge.weakLimitFamily) where
  latticeLimit := bridge.weakLimitFamily.weakLimit
  expectation_eq_fineEnlargedIntegral := bridge.expectation_eq_fineEnlargedIntegral

/-- Every fine enlarged product measure is normalized, derived from the exact product identity. -/
theorem fineMeasure_univ
    (bridge : TwoDimensionalSpectralVillainProductIdentityBridgeData
      (law := law) (inner := inner) (realLaplacian := realLaplacian)
      (complexLaplacian := complexLaplacian) (heatTraceData := heatTraceData)
      (faceGeometry := faceGeometry))
    (spacing : PositiveLatticeSpacing) :
    twoDimensionalFineEnlargedActionMeasure faceGeometry
      (spectralVillainActionAt bridge.weakLimitFamily) spacing Set.univ = 1 :=
  TwoDimensionalDriverAxialLatticeProductIdentityData.fineMeasure_univ
    faceGeometry (spectralVillainActionAt bridge.weakLimitFamily)
    bridge.toDriverAxialLatticeProductIdentityData spacing

end TwoDimensionalSpectralVillainProductIdentityBridgeData

end

end Dimensions
end YangMills
