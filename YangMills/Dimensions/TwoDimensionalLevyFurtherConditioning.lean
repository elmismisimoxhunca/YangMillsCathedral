/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Dimensions.TwoDimensionalLevyCompactSurfaceSewing

/-!
# Lévy sewing under further holonomy conditioning

The final clause of Lévy Theorem 5.1.1 says that the sewing properties remain true after further
conditioning on holonomies of boundary components or interior loops on either piece. This file
packages that stronger source-facing obligation.

Each side chooses either no extra observation or one genuinely positive finite joint-conjugacy
observation inside one exact geometric basepoint fiber. The optional form permits conditioning on
only one side. A second genuine conditional-kernel disintegration must reconstruct the same sewn law,
use the same restriction map, condition on the exact seam value plus the two optional observations,
and factor through side kernels that do not depend on the other side's extra value.

No such kernel or Yang--Mills law is constructed.
-/

namespace YangMills.Dimensions

open MeasureTheory ProbabilityTheory
open scoped Manifold ContDiff

noncomputable section

universe uG

universe uEL uHL uSL uER uHR uSR uLeftBase uRightBase uWholeBase
  uLeftLoop uRightLoop uWholeLoop uLeftSample uRightSample uWholeSample

variable
    {EL : Type uEL} [NormedAddCommGroup EL] [NormedSpace ℝ EL] [FiniteDimensional ℝ EL]
    [MeasurableSpace EL] [BorelSpace EL] {HL : Type uHL} [TopologicalSpace HL]
    {SL : Type uSL} [TopologicalSpace SL] [MeasurableSpace SL] [BorelSpace SL]
    {IL : ModelWithCorners ℝ EL HL} [ChartedSpace HL SL] [IsManifold IL ∞ SL]
    [CompactSpace SL] [T2Space SL] [SecondCountableTopology SL]
    {ER : Type uER} [NormedAddCommGroup ER] [NormedSpace ℝ ER] [FiniteDimensional ℝ ER]
    [MeasurableSpace ER] [BorelSpace ER] {HR : Type uHR} [TopologicalSpace HR]
    {SR : Type uSR} [TopologicalSpace SR] [MeasurableSpace SR] [BorelSpace SR]
    {IR : ModelWithCorners ℝ ER HR} [ChartedSpace HR SR] [IsManifold IR ∞ SR]
    [CompactSpace SR] [T2Space SR] [SecondCountableTopology SR]
    {leftSurface : YangMills.Geometry.CompactOrientedMeasuredSurfaceData IL SL}
    {leftPresentation : YangMills.Geometry.CompactSurfaceBoundaryCirclePresentationData leftSurface}
    {leftOrientation : YangMills.Geometry.CompactSurfaceBoundaryOrientationData
      leftSurface leftPresentation}
    {rightSurface : YangMills.Geometry.CompactOrientedMeasuredSurfaceData IR SR}
    {rightPresentation : YangMills.Geometry.CompactSurfaceBoundaryCirclePresentationData rightSurface}
    {rightOrientation : YangMills.Geometry.CompactSurfaceBoundaryOrientationData
      rightSurface rightPresentation}
    {identification : YangMills.Geometry.CompactSurfaceBoundaryIdentification
      leftSurface leftPresentation leftOrientation rightSurface rightPresentation rightOrientation}
    {G : Type uG} [Group G] [MeasurableSpace G]
    {LeftBase : Type uLeftBase} {RightBase : Type uRightBase} {WholeBase : Type uWholeBase}
    {LeftLoop : LeftBase → Type uLeftLoop} {RightLoop : RightBase → Type uRightLoop}
    {WholeLoop : WholeBase → Type uWholeLoop}
    {LeftSample : Type uLeftSample} [MeasurableSpace LeftSample]
    {RightSample : Type uRightSample} [MeasurableSpace RightSample]
    {WholeSample : Type uWholeSample} [MeasurableSpace WholeSample]
    {data : TwoDimensionalLevyCompactSurfaceSewingData
      (identification := identification) (G := G) (LeftLoop := LeftLoop)
      (RightLoop := RightLoop) (WholeLoop := WholeLoop)
      (LeftSample := LeftSample) (RightSample := RightSample) (WholeSample := WholeSample)}

/-- Full conditioning target: seam classes and one separate joint class for every distinct
fixed-base block selected on either side. Zero blocks mean no extra condition on that side. -/
abbrev LevyFurtherConditioningValue
    (leftBlocks : YangMills.Mathematics.FiniteFixedBaseBlockCollection LeftLoop)
    (rightBlocks : YangMills.Mathematics.FiniteFixedBaseBlockCollection RightLoop) :=
  LevyBoundaryConjugacyValue identification.pairCount G ×
    YangMills.Mathematics.finiteFixedBaseBlockObservationValue (G := G) leftBlocks ×
    YangMills.Mathematics.finiteFixedBaseBlockObservationValue (G := G) rightBlocks

/-- Only the seam orientation reverses; all side-specific fixed-base blocks retain their own piece
orientations. -/
def levyFurtherConditioningReverse
    {leftBlocks : YangMills.Mathematics.FiniteFixedBaseBlockCollection LeftLoop}
    {rightBlocks : YangMills.Mathematics.FiniteFixedBaseBlockCollection RightLoop} :
    LevyFurtherConditioningValue (identification := identification) (G := G)
        leftBlocks rightBlocks →
      LevyFurtherConditioningValue (identification := identification) (G := G)
        leftBlocks rightBlocks :=
  fun value => (levyBoundaryConjugacyReverse value.1, value.2.1, value.2.2)

/-- Uninhabited acceptance data for the final further-conditioning clause of Theorem 5.1.1. -/
structure TwoDimensionalLevyFurtherConditioningData
    (leftBlocks : YangMills.Mathematics.FiniteFixedBaseBlockCollection LeftLoop)
    (rightBlocks : YangMills.Mathematics.FiniteFixedBaseBlockCollection RightLoop) where
  disintegration : YangMills.Mathematics.BoundaryConditionedProductDisintegrationData
    (LevyFurtherConditioningValue (identification := identification) (G := G)
      leftBlocks rightBlocks)
    LeftSample RightSample WholeSample
  /-- The same unconditional sewn law and geometric restriction map are retained. -/
  wholeMeasure_eq : disintegration.wholeMeasure = data.disintegration.wholeMeasure
  restriction_eq : disintegration.restriction = data.disintegration.restriction
  boundaryValue_eq : ∀ whole,
    disintegration.boundaryValue whole =
      (data.disintegration.boundaryValue whole,
        YangMills.Mathematics.finiteFixedBaseBlockObservation
          data.leftHolonomy leftBlocks (data.disintegration.restriction whole).1,
        YangMills.Mathematics.finiteFixedBaseBlockObservation
          data.rightHolonomy rightBlocks (data.disintegration.restriction whole).2)
  boundaryReverse_eq : disintegration.boundaryReverse =
    levyFurtherConditioningReverse (identification := identification) (G := G)
  conditionedLeft : Kernel
    (LevyBoundaryConjugacyValue identification.pairCount G ×
      YangMills.Mathematics.finiteFixedBaseBlockObservationValue (G := G) leftBlocks) LeftSample
  conditionedLeft_markov : IsMarkovKernel conditionedLeft
  conditionedRight : Kernel
    (LevyBoundaryConjugacyValue identification.pairCount G ×
      YangMills.Mathematics.finiteFixedBaseBlockObservationValue (G := G) rightBlocks) RightSample
  conditionedRight_markov : IsMarkovKernel conditionedRight
  /-- Each full side kernel ignores every extra block value from the other side. -/
  conditionedLeft_eq : ∀ boundary leftValue rightValue,
    disintegration.conditionedLeft (boundary, leftValue, rightValue) =
      conditionedLeft (boundary, leftValue)
  conditionedRight_eq : ∀ boundary leftValue rightValue,
    disintegration.conditionedRight
        (levyFurtherConditioningReverse (identification := identification) (G := G)
          (boundary, leftValue, rightValue)) =
      conditionedRight (levyBoundaryConjugacyReverse boundary, rightValue)

namespace TwoDimensionalLevyFurtherConditioningData

/-- Exact further-conditioned product law with no dependence on the other side's block values. -/
theorem conditioned_restriction_product
    {leftBlocks : YangMills.Mathematics.FiniteFixedBaseBlockCollection LeftLoop}
    {rightBlocks : YangMills.Mathematics.FiniteFixedBaseBlockCollection RightLoop}
    (further : TwoDimensionalLevyFurtherConditioningData (data := data)
      leftBlocks rightBlocks)
    (boundary : LevyBoundaryConjugacyValue identification.pairCount G)
    (leftValue : YangMills.Mathematics.finiteFixedBaseBlockObservationValue (G := G) leftBlocks)
    (rightValue : YangMills.Mathematics.finiteFixedBaseBlockObservationValue (G := G) rightBlocks) :
    Measure.map data.disintegration.restriction
        (further.disintegration.conditionedWhole (boundary, leftValue, rightValue)) =
      (further.conditionedLeft (boundary, leftValue)).prod
        (further.conditionedRight (levyBoundaryConjugacyReverse boundary, rightValue)) := by
  rw [← further.restriction_eq]
  rw [further.disintegration.conditioned_restriction_product]
  rw [further.conditionedLeft_eq, further.boundaryReverse_eq,
    further.conditionedRight_eq]

/-- The enlarged disintegration reconstructs literally the same sewn whole law. -/
theorem same_whole_law
    {leftBlocks : YangMills.Mathematics.FiniteFixedBaseBlockCollection LeftLoop}
    {rightBlocks : YangMills.Mathematics.FiniteFixedBaseBlockCollection RightLoop}
    (further : TwoDimensionalLevyFurtherConditioningData (data := data)
      leftBlocks rightBlocks) :
    further.disintegration.wholeMeasure = data.disintegration.wholeMeasure :=
  further.wholeMeasure_eq

end TwoDimensionalLevyFurtherConditioningData

end

end YangMills.Dimensions
