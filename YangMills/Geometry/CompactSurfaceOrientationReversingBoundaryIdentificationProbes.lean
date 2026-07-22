/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Geometry.CompactSurfaceOrientationReversingBoundaryIdentification

/-!
# Hostile probes for orientation-reversing compact-surface boundary identifications
-/

namespace YangMills.Geometry.CompactSurfaceOrientationReversingBoundaryIdentification.Probes

open scoped Manifold ContDiff

noncomputable section

universe uEL uHL uSL uER uHR uSR

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
    {leftSurface : CompactOrientedMeasuredSurfaceData IL SL}
    {leftPresentation : CompactSurfaceBoundaryCirclePresentationData leftSurface}
    {leftOrientation : CompactSurfaceBoundaryOrientationData leftSurface leftPresentation}
    {rightSurface : CompactOrientedMeasuredSurfaceData IR SR}
    {rightPresentation : CompactSurfaceBoundaryCirclePresentationData rightSurface}
    {rightOrientation : CompactSurfaceBoundaryOrientationData rightSurface rightPresentation}

abbrev Identification
    (leftSurface : CompactOrientedMeasuredSurfaceData IL SL)
    (leftPresentation : CompactSurfaceBoundaryCirclePresentationData leftSurface)
    (leftOrientation : CompactSurfaceBoundaryOrientationData leftSurface leftPresentation)
    (rightSurface : CompactOrientedMeasuredSurfaceData IR SR)
    (rightPresentation : CompactSurfaceBoundaryCirclePresentationData rightSurface)
    (rightOrientation : CompactSurfaceBoundaryOrientationData rightSurface rightPresentation) :=
  CompactSurfaceOrientationReversingBoundaryIdentificationData
    leftSurface leftPresentation leftOrientation rightSurface rightPresentation rightOrientation

/-- Empty sewing families are constructor-blocked. -/
theorem zero_pair_family_blocked
    (identification : Identification leftSurface leftPresentation leftOrientation
      rightSurface rightPresentation rightOrientation) :
    identification.pairCount ≠ 0 :=
  Nat.ne_of_gt identification.pairCount_pos

/-- Positive arity supplies an actual selected pair. -/
theorem exact_pair_index_nonempty
    (identification : Identification leftSurface leftPresentation leftOrientation
      rightSurface rightPresentation rightOrientation) :
    Nonempty (Fin identification.pairCount) :=
  identification.pairIndex_nonempty

/-- Every pairing map is a genuine smooth circle diffeomorphism, not a bare bijection. -/
def exact_circle_diffeomorphism
    (identification : Identification leftSurface leftPresentation leftOrientation
      rightSurface rightPresentation rightOrientation)
    (pair : Fin identification.pairCount) :
    Circle ≃ₘ⟮𝓡 1, 𝓡 1⟯ Circle :=
  identification.circleDiffeomorphism pair

/-- Orientation reversal is derivative-level and has strictly negative target direction. -/
theorem exact_negative_derivative_ray
    (identification : Identification leftSurface leftPresentation leftOrientation
      rightSurface rightPresentation rightOrientation)
    (pair : Fin identification.pairCount) (circlePoint : Circle) :
    ∃ speed : ℝ, 0 < speed ∧
      mfderiv (𝓡 1) (𝓡 1) (identification.circleDiffeomorphism pair) circlePoint
          (leftOrientation.positiveCircleTangent
            (identification.leftComponent pair) circlePoint) =
        (-speed) • rightOrientation.positiveCircleTangent
          (identification.rightComponent pair)
          (identification.circleDiffeomorphism pair circlePoint) :=
  identification.derivative_positive_to_negative_ray pair circlePoint

/-- Selected left and right points lie on the exact paired boundary components. -/
theorem exact_boundary_component_membership
    (identification : Identification leftSurface leftPresentation leftOrientation
      rightSurface rightPresentation rightOrientation)
    (pair : Fin identification.pairCount) (circlePoint : Circle) :
    (∃ membership : identification.leftBoundaryPoint pair circlePoint ∈ IL.boundary SL,
      ConnectedComponents.mk
        ⟨identification.leftBoundaryPoint pair circlePoint, membership⟩ =
        identification.leftComponent pair) ∧
    (∃ membership : identification.rightBoundaryPoint pair circlePoint ∈ IR.boundary SR,
      ConnectedComponents.mk
        ⟨identification.rightBoundaryPoint pair circlePoint, membership⟩ =
        identification.rightComponent pair) :=
  ⟨identification.leftBoundaryPoint_mem_component pair circlePoint,
    identification.rightBoundaryPoint_mem_component pair circlePoint⟩

/-- Distinct pair labels cannot reuse a left boundary component. -/
theorem duplicate_left_component_blocked
    (identification : Identification leftSurface leftPresentation leftOrientation
      rightSurface rightPresentation rightOrientation)
    {first second : Fin identification.pairCount} (different : first ≠ second)
    (duplicate : identification.leftComponent first = identification.leftComponent second) : False :=
  different (identification.pair_eq_of_leftComponent_eq duplicate)

/-- Distinct pair labels cannot reuse a right boundary component. -/
theorem duplicate_right_component_blocked
    (identification : Identification leftSurface leftPresentation leftOrientation
      rightSurface rightPresentation rightOrientation)
    {first second : Fin identification.pairCount} (different : first ≠ second)
    (duplicate : identification.rightComponent first = identification.rightComponent second) : False :=
  different (identification.pair_eq_of_rightComponent_eq duplicate)

/-- A zero-speed surrogate cannot satisfy the strictly positive reversal witness. -/
theorem zero_reversal_speed_blocked {speed : ℝ} (positive : 0 < speed)
    (zero : speed = 0) : False := by
  rw [zero] at positive
  exact (lt_irrefl 0 positive)

end

end YangMills.Geometry.CompactSurfaceOrientationReversingBoundaryIdentification.Probes
