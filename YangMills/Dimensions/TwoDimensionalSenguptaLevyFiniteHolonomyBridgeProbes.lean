/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Dimensions.TwoDimensionalSenguptaLevyFiniteHolonomyBridge

/-! Hostile probes for the gauge-invariant Sengupta--Lévy finite-law bridge. -/

namespace YangMills.Dimensions.TwoDimensionalSenguptaLevyFiniteHolonomyBridge.Probes

open MeasureTheory
open YangMills.Mathematics
open scoped Manifold ContDiff

noncomputable section

universe uEL uHL uSL uER uHR uSR uG uCover uLeftBase uRightBase uWholeBase
  uLeftLoop uRightLoop uWholeLoop uLeftSample uRightSample uWholeSample
  uCurve uEdge uRegion uSenguptaSample

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
    {leftOrientation : Geometry.CompactSurfaceBoundaryOrientationData leftSurface leftPresentation}
    {rightSurface : Geometry.CompactOrientedMeasuredSurfaceData IR SR}
    {rightPresentation : Geometry.CompactSurfaceBoundaryCirclePresentationData rightSurface}
    {rightOrientation : Geometry.CompactSurfaceBoundaryOrientationData rightSurface rightPresentation}
    {identification : Geometry.CompactSurfaceBoundaryIdentification
      leftSurface leftPresentation leftOrientation rightSurface rightPresentation rightOrientation}
    {G : Type uG} [Group G] [TopologicalSpace G] [MeasurableSpace G]
    {CoverGroup : Type uCover} [Group CoverGroup]
    [TopologicalSpace CoverGroup] [IsTopologicalGroup CoverGroup]
    [CompactSpace CoverGroup] [T2Space CoverGroup]
    [MeasurableSpace CoverGroup] [BorelSpace CoverGroup]
    {LeftBase : Type uLeftBase} {RightBase : Type uRightBase} {WholeBase : Type uWholeBase}
    {LeftLoop : LeftBase → Type uLeftLoop} {RightLoop : RightBase → Type uRightLoop}
    {WholeLoop : WholeBase → Type uWholeLoop}
    {LeftSample : Type uLeftSample} [MeasurableSpace LeftSample]
    {RightSample : Type uRightSample} [MeasurableSpace RightSample]
    {WholeSample : Type uWholeSample} [MeasurableSpace WholeSample]
    {Curve : Type uCurve} [Fintype Curve] [Nonempty Curve]
    {Edge : Type uEdge} [Fintype Edge] [DecidableEq Edge]
    {Region : Type uRegion} [Fintype Region] [DecidableEq Region]
    {SenguptaSample : Type uSenguptaSample} [MeasurableSpace SenguptaSample]
    {finiteLaw : TwoDimensionalSenguptaCompactSurfaceFiniteHolonomyLawData
      (G := G) (CoverGroup := CoverGroup) (Curve := Curve) (Edge := Edge)
      (Region := Region) (Sample := SenguptaSample)}
    {sewing : TwoDimensionalLevyCompactSurfaceSewingData
      (identification := identification) (G := G)
      (LeftLoop := LeftLoop) (RightLoop := RightLoop) (WholeLoop := WholeLoop)
      (LeftSample := LeftSample) (RightSample := RightSample) (WholeSample := WholeSample)}
    (bridge : TwoDimensionalSenguptaLevyFiniteHolonomyBridgeData finiteLaw sewing)

omit [T2Space CoverGroup] [Fintype Curve] [Nonempty Curve] [DecidableEq Edge] in
/-- The bridge compares exact gauge-invariant finite laws on the two distinct source carriers. -/
theorem exact_gaugeInvariant_joint_law :
    Measure.map (senguptaFiniteJointConjugacyObservation finiteLaw) finiteLaw.sampleMeasure =
      Measure.map
        (levyWholeFiniteJointConjugacyObservation sewing bridge.wholeBase bridge.wholeCurve)
        sewing.disintegration.wholeMeasure :=
  bridge.jointConjugacyLaw

omit [T2Space CoverGroup] [Fintype Curve] [Nonempty Curve] [DecidableEq Edge] in
/-- Hostile coherence probe: a changed Lévy finite conjugacy-class law is rejected. -/
theorem changed_joint_law_blocked
    (changed : Measure.map (senguptaFiniteJointConjugacyObservation finiteLaw)
        finiteLaw.sampleMeasure ≠
      Measure.map
        (levyWholeFiniteJointConjugacyObservation sewing bridge.wholeBase bridge.wholeCurve)
        sewing.disintegration.wholeMeasure) : False :=
  changed bridge.jointConjugacyLaw

omit [T2Space CoverGroup] [Fintype Curve] [DecidableEq Edge] in
/-- The finite family is nonempty and selects an actual loop in one exact whole-surface base fiber;
it does not compare unbased or independently based raw holonomies. -/
theorem exact_nonempty_common_base_fiber :
    Nonempty Curve ∧ Nonempty (WholeLoop bridge.wholeBase) :=
  ⟨inferInstance, ⟨bridge.wholeCurve (Classical.choice inferInstance)⟩⟩

end

end YangMills.Dimensions.TwoDimensionalSenguptaLevyFiniteHolonomyBridge.Probes
