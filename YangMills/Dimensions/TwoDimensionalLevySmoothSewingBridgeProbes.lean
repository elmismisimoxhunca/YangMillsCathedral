/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Dimensions.TwoDimensionalLevySmoothSewingBridge
import YangMills.Dimensions.FourDimensionalContractSeparation

/-!
# Hostile probes for smooth Lévy sewing coherence
-/

namespace YangMills
namespace Dimensions
namespace TwoDimensionalLevySmoothSewingBridge
namespace Probes

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

/-- The descended sewn manifold model has literal real dimension two. -/
theorem exact_glued_dimension_two
    (bridge : TwoDimensionalLevySmoothSewingBridgeData
      (identification := identification) (IG := IG) (G := G)
      (LeftLoop := LeftLoop) (RightLoop := RightLoop) (WholeLoop := WholeLoop)
      (LeftSample := LeftSample) (RightSample := RightSample) (WholeSample := WholeSample)) :
    Module.finrank ℝ EG = 2 :=
  bridge.descent.glued_model_finrank_two

/-- The probabilistically designated seam is literally interior after smooth descent. -/
theorem exact_seam_loop_interior
    (bridge : TwoDimensionalLevySmoothSewingBridgeData
      (identification := identification) (IG := IG) (G := G)
      (LeftLoop := LeftLoop) (RightLoop := RightLoop) (WholeLoop := WholeLoop)
      (LeftSample := LeftSample) (RightSample := RightSample) (WholeSample := WholeSample))
    (pair : Fin identification.pairCount) (circlePoint : Circle) :
    bridge.sewing.wholeLoopTrace (bridge.sewing.seamBase pair)
        (bridge.sewing.seamLoop pair) circlePoint ∈
      IG.interior (Geometry.CompactSurfaceBoundaryGluingQuotient identification) :=
  bridge.seamLoopTrace_mem_interior pair circlePoint

/-- The exact inverse-boundary conditioned product law survives smooth descent. -/
theorem exact_conditioned_product
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
  bridge.conditioned_restriction_product_inverse boundary

/-- Hostile sewing probe: the descended whole probability law cannot be zero. -/
theorem zero_whole_measure_blocked
    (bridge : TwoDimensionalLevySmoothSewingBridgeData
      (identification := identification) (IG := IG) (G := G)
      (LeftLoop := LeftLoop) (RightLoop := RightLoop) (WholeLoop := WholeLoop)
      (LeftSample := LeftSample) (RightSample := RightSample) (WholeSample := WholeSample))
    (zeroMeasure : bridge.sewing.disintegration.wholeMeasure = 0) : False := by
  have normalized := bridge.sewing.wholeMeasure_univ
  rw [zeroMeasure] at normalized
  simp at normalized

/-- Witness-level geometric separation: the actual descended two-dimensional model cannot be the
four-dimensional Euclidean coordinate carrier. -/
theorem glued_model_not_linearEquiv_four
    (bridge : TwoDimensionalLevySmoothSewingBridgeData
      (identification := identification) (IG := IG) (G := G)
      (LeftLoop := LeftLoop) (RightLoop := RightLoop) (WholeLoop := WholeLoop)
      (LeftSample := LeftSample) (RightSample := RightSample) (WholeSample := WholeSample)) :
    ¬ Nonempty (EG ≃ₗ[ℝ] EuclideanDimension.four.Spacetime) := by
  rintro ⟨equiv⟩
  have ranks := LinearEquiv.finrank_eq equiv
  rw [bridge.descent.glued_model_finrank_two] at ranks
  norm_num [EuclideanDimension.finrank_spacetime] at ranks

end

end Probes
end TwoDimensionalLevySmoothSewingBridge
end Dimensions
end YangMills
