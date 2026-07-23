/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Dimensions.TwoDimensionalCurrentStrengthLiteratureAcceptance

/-!
# Hostile probes for current-strength 2D literature acceptance
-/

namespace YangMills
namespace Dimensions
namespace TwoDimensionalCurrentStrengthLiteratureAcceptance
namespace Probes

open Filter MeasureTheory ProbabilityTheory
open YangMills.Mathematics
open scoped Manifold ContDiff Topology

noncomputable section

universe uE uG uGauge uSample uConnection uΩ
  uVertex uEdge uFace uXAxisCell uLargeVertex uLargeEdge uLargeFace uLargeXAxisCell
  uFineVertex uFineEdge uFineFace uFineXAxisCell
  uFineLargeVertex uFineLargeEdge uFineLargeFace uFineLargeXAxisCell
  uEL uHL uSL uER uHR uSR uEG uHG
  uLeftBase uRightBase uWholeBase uLeftLoop uRightLoop uWholeLoop
  uLeftSample uRightSample uWholeSample

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
    {Connection : Type uConnection} {Ω : Type uΩ} [MeasurableSpace Ω]
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
    {continuum : TwoDimensionalDriverAxialEnlargedHeatExpectationData (law := law) axial}
    {coarseApproximation : TwoDimensionalLatticeApproximatingHolonomyData.{uVertex, uEdge,
      uFace, uXAxisCell, uFineVertex, uFineEdge, uFineFace, uFineXAxisCell}
      (base := base) (coarse := coarse)}
    {enlargedApproximation : TwoDimensionalLatticeApproximatingHolonomyData.{uLargeVertex,
      uLargeEdge, uLargeFace, uLargeXAxisCell, uFineLargeVertex, uFineLargeEdge,
      uFineLargeFace, uFineLargeXAxisCell} (base := base) (coarse := enlarged)}
    {faceGeometry : TwoDimensionalDriverAxialLatticeFaceGeometryData
      (axial := axial) (coarseApproximation := coarseApproximation)
      (enlargedApproximation := enlargedApproximation)}
    {EL : Type uEL} [NormedAddCommGroup EL] [NormedSpace ℝ EL] [FiniteDimensional ℝ EL]
    [MeasurableSpace EL] [BorelSpace EL]
    {HL : Type uHL} [TopologicalSpace HL]
    {SL : Type uSL} [TopologicalSpace SL] [MeasurableSpace SL] [BorelSpace SL]
    {IL : ModelWithCorners ℝ EL HL} [ChartedSpace HL SL] [IsManifold IL ∞ SL]
    [CompactSpace SL] [T2Space SL] [SecondCountableTopology SL]
    {ER : Type uER} [NormedAddCommGroup ER] [NormedSpace ℝ ER] [FiniteDimensional ℝ ER]
    [MeasurableSpace ER] [BorelSpace ER]
    {HR : Type uHR} [TopologicalSpace HR]
    {SR : Type uSR} [TopologicalSpace SR] [MeasurableSpace SR] [BorelSpace SR]
    {IR : ModelWithCorners ℝ ER HR} [ChartedSpace HR SR] [IsManifold IR ∞ SR]
    [CompactSpace SR] [T2Space SR] [SecondCountableTopology SR]
    {leftSurface : Geometry.CompactOrientedMeasuredSurfaceData IL SL}
    {leftPresentation : Geometry.CompactSurfaceBoundaryCirclePresentationData leftSurface}
    {leftOrientation : Geometry.CompactSurfaceBoundaryOrientationData
      leftSurface leftPresentation}
    {rightSurface : Geometry.CompactOrientedMeasuredSurfaceData IR SR}
    {rightPresentation : Geometry.CompactSurfaceBoundaryCirclePresentationData rightSurface}
    {rightOrientation : Geometry.CompactSurfaceBoundaryOrientationData
      rightSurface rightPresentation}
    {identification : Geometry.CompactSurfaceBoundaryIdentification
      leftSurface leftPresentation leftOrientation rightSurface rightPresentation rightOrientation}
    {EG : Type uEG} [NormedAddCommGroup EG] [NormedSpace ℝ EG] [FiniteDimensional ℝ EG]
    [MeasurableSpace EG] [BorelSpace EG]
    {HG : Type uHG} [TopologicalSpace HG] {IG : ModelWithCorners ℝ EG HG}
    [ChartedSpace HG (Geometry.CompactSurfaceBoundaryGluingQuotient identification)]
    [IsManifold IG ∞ (Geometry.CompactSurfaceBoundaryGluingQuotient identification)]
    {LeftBase : Type uLeftBase} {RightBase : Type uRightBase} {WholeBase : Type uWholeBase}
    {LeftLoop : LeftBase → Type uLeftLoop} {RightLoop : RightBase → Type uRightLoop}
    {WholeLoop : WholeBase → Type uWholeLoop}
    {LeftSample : Type uLeftSample} [MeasurableSpace LeftSample]
    {RightSample : Type uRightSample} [MeasurableSpace RightSample]
    {WholeSample : Type uWholeSample} [MeasurableSpace WholeSample]

/-- The inhabitance attempt is exactly the conjunction of the planar and compact-surface bridge
obligations; no witness is synthesized. -/
theorem exact_inhabitation_audit :
    Nonempty (TwoDimensionalCurrentStrengthLiteratureAcceptanceData
      (law := law) (inner := inner) (realLaplacian := realLaplacian)
      (complexLaplacian := complexLaplacian) (heatTraceData := heatTraceData)
      (continuum := continuum) (faceGeometry := faceGeometry) (Ω := Ω)
      (identification := identification) (IG := IG)
      (LeftLoop := LeftLoop) (RightLoop := RightLoop) (WholeLoop := WholeLoop)
      (LeftSample := LeftSample) (RightSample := RightSample) (WholeSample := WholeSample)) ↔
      Nonempty (TwoDimensionalSpectralPlanarLiteratureBridgeData
        (law := law) (inner := inner) (realLaplacian := realLaplacian)
        (complexLaplacian := complexLaplacian) (heatTraceData := heatTraceData)
        (continuum := continuum) (faceGeometry := faceGeometry) (Ω := Ω)) ∧
      Nonempty (TwoDimensionalLevySmoothSewingBridgeData
        (identification := identification) (IG := IG) (G := G)
        (LeftLoop := LeftLoop) (RightLoop := RightLoop) (WholeLoop := WholeLoop)
        (LeftSample := LeftSample) (RightSample := RightSample) (WholeSample := WholeSample)) :=
  TwoDimensionalCurrentStrengthLiteratureAcceptanceData.nonempty_iff_bridges

/-- Hostile inhabitance probe: without smooth quotient descent, the joined acceptance record cannot
be packaged. -/
theorem missing_descent_blocks_acceptance
    (missing : ¬ Nonempty (Geometry.CompactSurfaceBoundaryGluingSmoothDescentData
      (identification := identification) (IG := IG))) :
    ¬ Nonempty (TwoDimensionalCurrentStrengthLiteratureAcceptanceData
      (law := law) (inner := inner) (realLaplacian := realLaplacian)
      (complexLaplacian := complexLaplacian) (heatTraceData := heatTraceData)
      (continuum := continuum) (faceGeometry := faceGeometry) (Ω := Ω)
      (identification := identification) (IG := IG)
      (LeftLoop := LeftLoop) (RightLoop := RightLoop) (WholeLoop := WholeLoop)
      (LeftSample := LeftSample) (RightSample := RightSample) (WholeSample := WholeSample)) := by
  intro current
  have bridges := exact_inhabitation_audit.mp current
  have surfaceDebts :=
    TwoDimensionalCurrentStrengthLiteratureAcceptanceData.nonempty_compactSurface_iff_descent_sewing.mp
      bridges.2
  exact missing surfaceDebts.1

variable (data : TwoDimensionalCurrentStrengthLiteratureAcceptanceData
  (law := law) (inner := inner) (realLaplacian := realLaplacian)
  (complexLaplacian := complexLaplacian) (heatTraceData := heatTraceData)
  (continuum := continuum) (faceGeometry := faceGeometry) (Ω := Ω)
  (identification := identification) (IG := IG)
  (LeftLoop := LeftLoop) (RightLoop := RightLoop) (WholeLoop := WholeLoop)
  (LeftSample := LeftSample) (RightSample := RightSample) (WholeSample := WholeSample))

include data in
/-- Both major literature tracks are present on the same exact gauge group. -/
theorem exact_joined_tracks :
    Nonempty (TwoDimensionalSpectralPlanarLiteratureBridgeData
      (law := law) (inner := inner) (realLaplacian := realLaplacian)
      (complexLaplacian := complexLaplacian) (heatTraceData := heatTraceData)
      (continuum := continuum) (faceGeometry := faceGeometry) (Ω := Ω)) ∧
    Nonempty (TwoDimensionalLevySmoothSewingBridgeData
      (identification := identification) (IG := IG) (G := G)
      (LeftLoop := LeftLoop) (RightLoop := RightLoop) (WholeLoop := WholeLoop)
      (LeftSample := LeftSample) (RightSample := RightSample) (WholeSample := WholeSample)) :=
  ⟨⟨data.planar⟩, ⟨data.compactSurface⟩⟩

include data in
/-- The actual descended compact-surface model is rank two. -/
theorem exact_surface_dimension_two : Module.finrank ℝ EG = 2 :=
  data.compactSurface_model_finrank_two

include data in
/-- Witness-level separation uses the actual descended surface model, not only a dimension tag. -/
theorem surface_model_not_linearEquiv_four :
    ¬ Nonempty (EG ≃ₗ[ℝ] EuclideanDimension.four.Spacetime) := by
  rintro ⟨equiv⟩
  have ranks := LinearEquiv.finrank_eq equiv
  rw [data.compactSurface_model_finrank_two] at ranks
  norm_num [EuclideanDimension.finrank_spacetime] at ranks

include data in
/-- Hostile joined-law probe: neither supplied probability law may collapse to zero. -/
theorem joined_probability_measures_nonzero :
    data.planar.brownian.probabilityMeasure ≠ 0 ∧
      data.compactSurface.sewing.disintegration.wholeMeasure ≠ 0 := by
  constructor
  · exact data.planar.brownian.probabilityMeasure_ne_zero
  · intro zeroMeasure
    have normalized := data.compactSurface.sewing.wholeMeasure_univ
    rw [zeroMeasure] at normalized
    simp at normalized

end

end Probes
end TwoDimensionalCurrentStrengthLiteratureAcceptance
end Dimensions
end YangMills
