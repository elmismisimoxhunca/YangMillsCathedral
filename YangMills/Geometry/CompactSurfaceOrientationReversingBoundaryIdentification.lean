/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Geometry.CompactSurfaceBoundaryOrientation
import Mathlib.Geometry.Manifold.Diffeomorph

/-!
# Orientation-reversing identifications of compact-surface boundary circles

Lévy's sewing theorem starts with two oriented compact surfaces, chooses the same positive number of
distinct boundary components on each side, and identifies paired components by orientation-reversing
diffeomorphisms. This file formalizes exactly that pre-gluing identification datum over the committed
exact circle presentations and induced boundary orientations.

Orientation reversal is differential, not merely a Boolean label: the derivative sends the selected
positive tangent on the left circle to a strictly negative multiple of the selected positive tangent
on the paired right circle. The maps are genuine Mathlib smooth diffeomorphisms. This file does not
construct the quotient surface, its smooth structure or measure, and does not state a probability or
Yang--Mills sewing law.
-/

namespace YangMills.Geometry

open scoped Manifold ContDiff

noncomputable section

universe uELeft uHLeft uSurfaceLeft uERight uHRight uSurfaceRight

variable
    {ELeft : Type uELeft} [NormedAddCommGroup ELeft] [NormedSpace ℝ ELeft]
    [FiniteDimensional ℝ ELeft] [MeasurableSpace ELeft] [BorelSpace ELeft]
    {HLeft : Type uHLeft} [TopologicalSpace HLeft]
    {SurfaceLeft : Type uSurfaceLeft} [TopologicalSpace SurfaceLeft]
    [MeasurableSpace SurfaceLeft] [BorelSpace SurfaceLeft]
    {ILeft : ModelWithCorners ℝ ELeft HLeft} [ChartedSpace HLeft SurfaceLeft]
    [IsManifold ILeft ∞ SurfaceLeft] [CompactSpace SurfaceLeft] [T2Space SurfaceLeft]
    [SecondCountableTopology SurfaceLeft]
    {ERight : Type uERight} [NormedAddCommGroup ERight] [NormedSpace ℝ ERight]
    [FiniteDimensional ℝ ERight] [MeasurableSpace ERight] [BorelSpace ERight]
    {HRight : Type uHRight} [TopologicalSpace HRight]
    {SurfaceRight : Type uSurfaceRight} [TopologicalSpace SurfaceRight]
    [MeasurableSpace SurfaceRight] [BorelSpace SurfaceRight]
    {IRight : ModelWithCorners ℝ ERight HRight} [ChartedSpace HRight SurfaceRight]
    [IsManifold IRight ∞ SurfaceRight] [CompactSpace SurfaceRight] [T2Space SurfaceRight]
    [SecondCountableTopology SurfaceRight]

/-- Exact positive-arity orientation-reversing pairings of distinct boundary components of two
oriented compact surfaces. -/
structure CompactSurfaceOrientationReversingBoundaryIdentificationData
    (leftSurface : CompactOrientedMeasuredSurfaceData ILeft SurfaceLeft)
    (leftPresentation : CompactSurfaceBoundaryCirclePresentationData leftSurface)
    (leftOrientation : CompactSurfaceBoundaryOrientationData leftSurface leftPresentation)
    (rightSurface : CompactOrientedMeasuredSurfaceData IRight SurfaceRight)
    (rightPresentation : CompactSurfaceBoundaryCirclePresentationData rightSurface)
    (rightOrientation : CompactSurfaceBoundaryOrientationData rightSurface rightPresentation) where
  /-- Lévy's `p > 0`; zero-pair vacuity is constructor-blocked. -/
  pairCount : ℕ
  pairCount_pos : 0 < pairCount
  /-- The selected components on both sides. -/
  leftComponent : Fin pairCount → leftSurface.BoundaryComponent
  rightComponent : Fin pairCount → rightSurface.BoundaryComponent
  /-- No boundary component is silently used in two distinct sewing pairs. -/
  leftComponent_injective : Function.Injective leftComponent
  rightComponent_injective : Function.Injective rightComponent
  /-- Genuine smooth circle diffeomorphism representing each boundary identification. -/
  circleDiffeomorphism : ∀ _pair,
    Circle ≃ₘ⟮𝓡 1, 𝓡 1⟯ Circle
  /-- Exact orientation reversal: positive left tangent maps to a negative positive multiple of the
  positive right tangent. Variable positive speed is retained. -/
  orientationReversing : ∀ pair circlePoint,
    ∃ speed : ℝ, 0 < speed ∧
      mfderiv (𝓡 1) (𝓡 1) (circleDiffeomorphism pair) circlePoint
          (leftOrientation.positiveCircleTangent (leftComponent pair) circlePoint) =
        (-speed) • rightOrientation.positiveCircleTangent (rightComponent pair)
          (circleDiffeomorphism pair circlePoint)

namespace CompactSurfaceOrientationReversingBoundaryIdentificationData

variable
    {leftSurface : CompactOrientedMeasuredSurfaceData ILeft SurfaceLeft}
    {leftPresentation : CompactSurfaceBoundaryCirclePresentationData leftSurface}
    {leftOrientation : CompactSurfaceBoundaryOrientationData leftSurface leftPresentation}
    {rightSurface : CompactOrientedMeasuredSurfaceData IRight SurfaceRight}
    {rightPresentation : CompactSurfaceBoundaryCirclePresentationData rightSurface}
    {rightOrientation : CompactSurfaceBoundaryOrientationData rightSurface rightPresentation}

/-- The actual point on the selected left boundary component. -/
def leftBoundaryPoint
    (identification : CompactSurfaceOrientationReversingBoundaryIdentificationData
      leftSurface leftPresentation leftOrientation rightSurface rightPresentation rightOrientation)
    (pair : Fin identification.pairCount) (circlePoint : Circle) : SurfaceLeft :=
  leftPresentation.parameterization (identification.leftComponent pair) circlePoint

/-- The actual paired point on the selected right boundary component after applying the exact circle
diffeomorphism. -/
def rightBoundaryPoint
    (identification : CompactSurfaceOrientationReversingBoundaryIdentificationData
      leftSurface leftPresentation leftOrientation rightSurface rightPresentation rightOrientation)
    (pair : Fin identification.pairCount) (circlePoint : Circle) : SurfaceRight :=
  rightPresentation.parameterization (identification.rightComponent pair)
    (identification.circleDiffeomorphism pair circlePoint)

/-- There is an actual sewing-pair index. -/
theorem pairIndex_nonempty
    (identification : CompactSurfaceOrientationReversingBoundaryIdentificationData
      leftSurface leftPresentation leftOrientation rightSurface rightPresentation rightOrientation) :
    Nonempty (Fin identification.pairCount) :=
  Fin.pos_iff_nonempty.mp identification.pairCount_pos

/-- Every selected left point lies on its exact selected boundary component. -/
theorem leftBoundaryPoint_mem_component
    (identification : CompactSurfaceOrientationReversingBoundaryIdentificationData
      leftSurface leftPresentation leftOrientation rightSurface rightPresentation rightOrientation)
    (pair : Fin identification.pairCount) (circlePoint : Circle) :
    ∃ boundaryMembership : identification.leftBoundaryPoint pair circlePoint ∈
        ILeft.boundary SurfaceLeft,
      ConnectedComponents.mk
        ⟨identification.leftBoundaryPoint pair circlePoint, boundaryMembership⟩ =
        identification.leftComponent pair :=
  leftPresentation.parameterization_mem_boundary_component
    (identification.leftComponent pair) circlePoint

/-- Every paired right point lies on its exact selected boundary component. -/
theorem rightBoundaryPoint_mem_component
    (identification : CompactSurfaceOrientationReversingBoundaryIdentificationData
      leftSurface leftPresentation leftOrientation rightSurface rightPresentation rightOrientation)
    (pair : Fin identification.pairCount) (circlePoint : Circle) :
    ∃ boundaryMembership : identification.rightBoundaryPoint pair circlePoint ∈
        IRight.boundary SurfaceRight,
      ConnectedComponents.mk
        ⟨identification.rightBoundaryPoint pair circlePoint, boundaryMembership⟩ =
        identification.rightComponent pair :=
  rightPresentation.parameterization_mem_boundary_component
    (identification.rightComponent pair)
    (identification.circleDiffeomorphism pair circlePoint)

/-- The exact derivative-level orientation-reversal witness. -/
theorem derivative_positive_to_negative_ray
    (identification : CompactSurfaceOrientationReversingBoundaryIdentificationData
      leftSurface leftPresentation leftOrientation rightSurface rightPresentation rightOrientation)
    (pair : Fin identification.pairCount) (circlePoint : Circle) :
    ∃ speed : ℝ, 0 < speed ∧
      mfderiv (𝓡 1) (𝓡 1) (identification.circleDiffeomorphism pair) circlePoint
          (leftOrientation.positiveCircleTangent
            (identification.leftComponent pair) circlePoint) =
        (-speed) • rightOrientation.positiveCircleTangent
          (identification.rightComponent pair)
          (identification.circleDiffeomorphism pair circlePoint) :=
  identification.orientationReversing pair circlePoint

/-- Pair labels are recoverable from their selected left components. -/
theorem pair_eq_of_leftComponent_eq
    (identification : CompactSurfaceOrientationReversingBoundaryIdentificationData
      leftSurface leftPresentation leftOrientation rightSurface rightPresentation rightOrientation)
    {first second : Fin identification.pairCount}
    (componentEquality : identification.leftComponent first =
      identification.leftComponent second) : first = second :=
  identification.leftComponent_injective componentEquality

/-- Pair labels are recoverable from their selected right components. -/
theorem pair_eq_of_rightComponent_eq
    (identification : CompactSurfaceOrientationReversingBoundaryIdentificationData
      leftSurface leftPresentation leftOrientation rightSurface rightPresentation rightOrientation)
    {first second : Fin identification.pairCount}
    (componentEquality : identification.rightComponent first =
      identification.rightComponent second) : first = second :=
  identification.rightComponent_injective componentEquality

end CompactSurfaceOrientationReversingBoundaryIdentificationData

end

end YangMills.Geometry
