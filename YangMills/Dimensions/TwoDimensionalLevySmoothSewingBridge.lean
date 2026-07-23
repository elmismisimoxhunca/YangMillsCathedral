/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Dimensions.TwoDimensionalLevyCompactSurfaceSewing
import YangMills.Geometry.CompactSurfaceBoundaryGluingSmoothDescent

/-!
# Bridge from smooth compact-surface descent to Lévy sewing

The topological quotient and canonical glued area are constructed, but smooth/oriented/measured
descent remains an explicit obligation. Lévy's probabilistic sewing contract is separately
uninhabited. This file forces both records to use the same boundary identification and quotient
carrier.

The combined bridge derives that every designated sewn seam-loop point is an interior point of the
smooth glued surface while retaining the exact inverse-boundary conditional product law and canonical
sum-of-pushforwards area. No descent witness, probability law, or Yang–Mills measure is constructed.
-/

namespace YangMills
namespace Dimensions

open MeasureTheory
open scoped Manifold ContDiff

noncomputable section

universe uEL uHL uSL uER uHR uSR uEG uHG uG
  uLeftBase uRightBase uWholeBase uLeftLoop uRightLoop uWholeLoop
  uLeftSample uRightSample uWholeSample

variable
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
    {HG : Type uHG} [TopologicalSpace HG]
    {IG : ModelWithCorners ℝ EG HG}
    [ChartedSpace HG (Geometry.CompactSurfaceBoundaryGluingQuotient identification)]
    [IsManifold IG ∞ (Geometry.CompactSurfaceBoundaryGluingQuotient identification)]
    {G : Type uG} [Group G] [MeasurableSpace G]
    {LeftBase : Type uLeftBase} {RightBase : Type uRightBase} {WholeBase : Type uWholeBase}
    {LeftLoop : LeftBase → Type uLeftLoop} {RightLoop : RightBase → Type uRightLoop}
    {WholeLoop : WholeBase → Type uWholeLoop}
    {LeftSample : Type uLeftSample} [MeasurableSpace LeftSample]
    {RightSample : Type uRightSample} [MeasurableSpace RightSample]
    {WholeSample : Type uWholeSample} [MeasurableSpace WholeSample]

/-- Exact common quotient carrier for smooth geometric descent and Lévy conditional sewing. -/
structure TwoDimensionalLevySmoothSewingBridgeData where
  descent : Geometry.CompactSurfaceBoundaryGluingSmoothDescentData
    (identification := identification) (IG := IG)
  sewing : TwoDimensionalLevyCompactSurfaceSewingData
    (identification := identification) (G := G)
    (LeftLoop := LeftLoop) (RightLoop := RightLoop) (WholeLoop := WholeLoop)
    (LeftSample := LeftSample) (RightSample := RightSample) (WholeSample := WholeSample)

namespace TwoDimensionalLevySmoothSewingBridgeData

/-- Every point of every designated sewn seam loop lies in the smooth glued interior. -/
theorem seamLoopTrace_mem_interior
    (bridge : TwoDimensionalLevySmoothSewingBridgeData
      (identification := identification) (IG := IG) (G := G)
      (LeftLoop := LeftLoop) (RightLoop := RightLoop) (WholeLoop := WholeLoop)
      (LeftSample := LeftSample) (RightSample := RightSample) (WholeSample := WholeSample))
    (pair : Fin identification.pairCount) (circlePoint : Circle) :
    bridge.sewing.wholeLoopTrace (bridge.sewing.seamBase pair)
        (bridge.sewing.seamLoop pair) circlePoint ∈
      IG.interior (Geometry.CompactSurfaceBoundaryGluingQuotient identification) := by
  rw [bridge.sewing.seamLoop_trace pair circlePoint]
  exact bridge.descent.seam_mem_interior pair circlePoint

/-- The descended area is exactly the canonical sum of the two side pushforwards. -/
theorem areaMeasure_eq_sum_pushforward
    (bridge : TwoDimensionalLevySmoothSewingBridgeData
      (identification := identification) (IG := IG) (G := G)
      (LeftLoop := LeftLoop) (RightLoop := RightLoop) (WholeLoop := WholeLoop)
      (LeftSample := LeftSample) (RightSample := RightSample) (WholeSample := WholeSample)) :
    bridge.descent.gluedSurface.areaMeasure =
      Measure.map (Geometry.CompactSurfaceBoundaryGluingQuotient.leftInclusion identification)
          leftSurface.areaMeasure +
        Measure.map (Geometry.CompactSurfaceBoundaryGluingQuotient.rightInclusion identification)
          rightSurface.areaMeasure :=
  bridge.descent.areaMeasure_eq_sum_pushforward

/-- Lévy's conditioned restriction remains the exact product with inverse right boundary class on
the same smoothly descended quotient. -/
theorem conditioned_restriction_product_inverse
    (bridge : TwoDimensionalLevySmoothSewingBridgeData
      (identification := identification) (IG := IG) (G := G)
      (LeftLoop := LeftLoop) (RightLoop := RightLoop) (WholeLoop := WholeLoop)
      (LeftSample := LeftSample) (RightSample := RightSample) (WholeSample := WholeSample))
    (boundary : LevyBoundaryConjugacyValue identification.pairCount G) :
    Measure.map bridge.sewing.disintegration.restriction
        (bridge.sewing.disintegration.conditionedWhole boundary) =
      (bridge.sewing.disintegration.conditionedLeft boundary).prod
        (bridge.sewing.disintegration.conditionedRight
          (levyBoundaryConjugacyReverse boundary)) :=
  bridge.sewing.conditioned_restriction_product_inverse boundary

end TwoDimensionalLevySmoothSewingBridgeData

end

end Dimensions
end YangMills
