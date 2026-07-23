/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Dimensions.TwoDimensionalLevyCompactSurfaceSewing
import YangMills.Dimensions.TwoDimensionalSenguptaCompactSurfaceFiniteHolonomyLaw

/-!
# Gauge-invariant finite-law bridge from Sengupta to Lévy sewing

Sengupta Theorem 8.4 and Lévy Theorem 5.1.1 use source-appropriate, generally different sample
carriers. This file does not identify those carriers or demand equality of raw based holonomies.
Instead it isolates the exact same-theory coherence that is meaningful on both quotient models: the
law of the simultaneous conjugacy class of a finite family of loops at one geometric base point.

No finite curve family is embedded into a Lévy loop carrier and no equality in law is constructed.
Both are explicit fields of an uninhabited bridge.
-/

namespace YangMills.Dimensions

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

/-- Gauge-invariant finite observation on Sengupta's source-specific sample carrier. -/
def senguptaFiniteJointConjugacyObservation
    (finiteLaw : TwoDimensionalSenguptaCompactSurfaceFiniteHolonomyLawData
      (G := G) (CoverGroup := CoverGroup) (Curve := Curve) (Edge := Edge)
      (Region := Region) (Sample := SenguptaSample)) :
    SenguptaSample → SimultaneousConjugacyQuotient Curve G :=
  fun sample => simultaneousConjugacyClass (finiteLaw.sampleHolonomy sample)

/-- The corresponding gauge-invariant finite observation on Lévy's sewn whole-surface carrier. -/
def levyWholeFiniteJointConjugacyObservation
    (sewing : TwoDimensionalLevyCompactSurfaceSewingData
      (identification := identification) (G := G)
      (LeftLoop := LeftLoop) (RightLoop := RightLoop) (WholeLoop := WholeLoop)
      (LeftSample := LeftSample) (RightSample := RightSample) (WholeSample := WholeSample))
    (wholeBase : WholeBase) (wholeCurve : Curve → WholeLoop wholeBase) :
    WholeSample → SimultaneousConjugacyQuotient Curve G :=
  fun sample => simultaneousConjugacyClass
    (fun curve => sewing.wholeHolonomy wholeBase (wholeCurve curve) sample)

/-- Uninhabited same-theory bridge between Sengupta's finite-dimensional compact-surface law and
Lévy's sewn quotient law. It compares only the exact gauge-invariant simultaneous-conjugacy
observation, never the unrelated sample carriers or raw holonomies. -/
structure TwoDimensionalSenguptaLevyFiniteHolonomyBridgeData
    (finiteLaw : TwoDimensionalSenguptaCompactSurfaceFiniteHolonomyLawData
      (G := G) (CoverGroup := CoverGroup) (Curve := Curve) (Edge := Edge)
      (Region := Region) (Sample := SenguptaSample))
    (sewing : TwoDimensionalLevyCompactSurfaceSewingData
      (identification := identification) (G := G)
      (LeftLoop := LeftLoop) (RightLoop := RightLoop) (WholeLoop := WholeLoop)
      (LeftSample := LeftSample) (RightSample := RightSample) (WholeSample := WholeSample)) where
  wholeBase : WholeBase
  wholeCurve : Curve → WholeLoop wholeBase
  wholeObservation_measurable : Measurable
    (levyWholeFiniteJointConjugacyObservation sewing wholeBase wholeCurve)
  jointConjugacyLaw :
    Measure.map (senguptaFiniteJointConjugacyObservation finiteLaw) finiteLaw.sampleMeasure =
      Measure.map (levyWholeFiniteJointConjugacyObservation sewing wholeBase wholeCurve)
        sewing.disintegration.wholeMeasure

namespace TwoDimensionalSenguptaLevyFiniteHolonomyBridgeData

omit [T2Space CoverGroup] [Fintype Curve] [Nonempty Curve] [DecidableEq Edge] in
/-- Sengupta's finite simultaneous-conjugacy observation is measurable, derived from the stronger
raw finite-holonomy measurability stored on its based carrier. -/
theorem senguptaObservation_measurable
    (finiteLaw : TwoDimensionalSenguptaCompactSurfaceFiniteHolonomyLawData
      (G := G) (CoverGroup := CoverGroup) (Curve := Curve) (Edge := Edge)
      (Region := Region) (Sample := SenguptaSample)) :
    Measurable (senguptaFiniteJointConjugacyObservation finiteLaw) :=
  simultaneousConjugacyClass_measurable.comp finiteLaw.sampleHolonomy_measurable

omit [T2Space CoverGroup] [Fintype Curve] [Nonempty Curve] [DecidableEq Edge] in
/-- The exact same-theory content retained by the bridge. -/
theorem exact_jointConjugacyLaw
    {finiteLaw : TwoDimensionalSenguptaCompactSurfaceFiniteHolonomyLawData
      (G := G) (CoverGroup := CoverGroup) (Curve := Curve) (Edge := Edge)
      (Region := Region) (Sample := SenguptaSample)}
    {sewing : TwoDimensionalLevyCompactSurfaceSewingData
      (identification := identification) (G := G)
      (LeftLoop := LeftLoop) (RightLoop := RightLoop) (WholeLoop := WholeLoop)
      (LeftSample := LeftSample) (RightSample := RightSample) (WholeSample := WholeSample)}
    (bridge : TwoDimensionalSenguptaLevyFiniteHolonomyBridgeData finiteLaw sewing) :
    Measure.map (senguptaFiniteJointConjugacyObservation finiteLaw) finiteLaw.sampleMeasure =
      Measure.map (levyWholeFiniteJointConjugacyObservation sewing bridge.wholeBase bridge.wholeCurve)
        sewing.disintegration.wholeMeasure :=
  bridge.jointConjugacyLaw

end TwoDimensionalSenguptaLevyFiniteHolonomyBridgeData

end

end YangMills.Dimensions
