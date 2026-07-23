/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Dimensions.TwoDimensionalSenguptaCoveringHeatSemigroupBridge

/-! Hostile probes for the Sengupta covering heat-semigroup bridge. -/

namespace YangMills.Dimensions.TwoDimensionalSenguptaCoveringHeatSemigroupBridge.Probes

open MeasureTheory
open YangMills.Mathematics
open scoped ENNReal

noncomputable section

universe uG uCover uGauge uSample uConnection uCurve uEdge uRegion uSenguptaSample

variable
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    {Gauge : Type uGauge} [Group Gauge]
    {Sample : Type uSample} [MeasurableSpace Sample]
    {Connection : Type uConnection}
    {base : TwoDimensionalGaugeFixedHolonomyMeasureData G Gauge Sample Connection}
    {law : TwoDimensionalSelectedLoopHaarDensityLawData base}
    {planarSemigroup : TwoDimensionalSelectedLoopConvolutionSemigroupData law}
    {CoverGroup : Type uCover} [Group CoverGroup]
    [TopologicalSpace CoverGroup] [IsTopologicalGroup CoverGroup]
    [CompactSpace CoverGroup] [T2Space CoverGroup]
    [MeasurableSpace CoverGroup] [BorelSpace CoverGroup]
    {Curve : Type uCurve} [Fintype Curve] [Nonempty Curve]
    {Edge : Type uEdge} [Fintype Edge] [DecidableEq Edge]
    {Region : Type uRegion} [Fintype Region] [DecidableEq Region]
    {SenguptaSample : Type uSenguptaSample} [MeasurableSpace SenguptaSample]
    {finiteLaw : TwoDimensionalSenguptaCompactSurfaceFiniteHolonomyLawData
      (G := G) (CoverGroup := CoverGroup) (Curve := Curve) (Edge := Edge)
      (Region := Region) (Sample := SenguptaSample)}
    {coverDensity : ℝ → CoverGroup → ℝ≥0∞}
    (bridge : TwoDimensionalSenguptaCoveringHeatSemigroupBridgeData
      (planarSemigroup := planarSemigroup) (finiteLaw := finiteLaw)
      (coverDensity := coverDensity))

omit [T2Space CoverGroup] [Fintype Curve] [Nonempty Curve] [DecidableEq Edge] in
/-- The covering bridge inhabitance audit exposes both exact dependent witnesses. -/
theorem exact_covering_inhabitation_audit :
    Nonempty (TwoDimensionalSenguptaCoveringHeatSemigroupBridgeData
      (planarSemigroup := planarSemigroup) (finiteLaw := finiteLaw)
      (coverDensity := coverDensity)) ↔
    ∃ coverSemigroup : NormalizedCompactHaarDensitySemigroupData coverDensity,
      Nonempty (NormalizedCompactHaarDensitySemigroupHomData coverSemigroup
        planarSemigroup.toNormalizedCompactHaarDensitySemigroupData finiteLaw.projection) :=
  TwoDimensionalSenguptaCoveringHeatSemigroupBridgeData.nonempty_iff_coverSemigroup_projectionHeat

include bridge in
omit [T2Space CoverGroup] [Fintype Curve] [Nonempty Curve] [DecidableEq Edge] in
/-- The exact finite-law projection transports the cover density measure at every positive time. -/
theorem exact_cover_measure_pushforward {t : ℝ} (ht : 0 < t) :
    Measure.map finiteLaw.projection
        (normalizedCompactHaarDensitySemigroupMeasure coverDensity t) =
      normalizedCompactHaarDensitySemigroupMeasure law.selectedAreaDensity t :=
  bridge.map_coverMeasure ht

include bridge in
omit [T2Space CoverGroup] [Fintype Curve] [Nonempty Curve] [DecidableEq Edge] in
/-- Hostile covering-heat probe: a changed projected law is rejected. -/
theorem changed_cover_measure_blocked
    {t : ℝ} (ht : 0 < t)
    (changed : Measure.map finiteLaw.projection
        (normalizedCompactHaarDensitySemigroupMeasure coverDensity t) ≠
      normalizedCompactHaarDensitySemigroupMeasure law.selectedAreaDensity t) : False :=
  changed (bridge.map_coverMeasure ht)

include bridge in
omit [T2Space CoverGroup] [Fintype Curve] [Nonempty Curve] [DecidableEq Edge] in
/-- Positive-time cover and planar measures are both normalized and nonzero. -/
theorem exact_both_positive_time_probability {t : ℝ} (ht : 0 < t) :
    normalizedCompactHaarDensitySemigroupMeasure coverDensity t Set.univ = 1 ∧
    normalizedCompactHaarDensitySemigroupMeasure coverDensity t ≠ 0 ∧
    normalizedCompactHaarDensitySemigroupMeasure law.selectedAreaDensity t Set.univ = 1 ∧
    normalizedCompactHaarDensitySemigroupMeasure law.selectedAreaDensity t ≠ 0 :=
  ⟨bridge.coverSemigroup.measure_univ ht, bridge.coverSemigroup.measure_ne_zero ht,
    planarSemigroup.toNormalizedCompactHaarDensitySemigroupData.measure_univ ht,
    planarSemigroup.toNormalizedCompactHaarDensitySemigroupData.measure_ne_zero ht⟩

end

end YangMills.Dimensions.TwoDimensionalSenguptaCoveringHeatSemigroupBridge.Probes
