/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Dimensions.TwoDimensionalSelectedLoopConvolutionSemigroup
import YangMills.Dimensions.TwoDimensionalSenguptaCompactSurfaceFiniteHolonomyLaw

/-!
# Covering-group heat-semigroup bridge for Sengupta

Sengupta's compact-surface formula uses heat densities on the compact covering group `G'`, whereas
the planar selected-loop chain stores densities on the physical gauge group `G`. Pointwise equality
across covering fibers is not the correct requirement. This file records the exact measure-level
compatibility: the covering-group density semigroup pushes forward through the same surjective
covering homomorphism used by the finite compact-surface law to the unchanged planar density
semigroup at every positive time.

No covering-group density or compatibility theorem is constructed, and no Definition 7.6 region
factor is inferred from this bridge.
-/

namespace YangMills.Dimensions

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

/-- Uninhabited heat-semigroup compatibility across Sengupta's exact covering projection. -/
structure TwoDimensionalSenguptaCoveringHeatSemigroupBridgeData where
  coverSemigroup : NormalizedCompactHaarDensitySemigroupData coverDensity
  projectionHeat : NormalizedCompactHaarDensitySemigroupHomData
    coverSemigroup planarSemigroup.toNormalizedCompactHaarDensitySemigroupData finiteLaw.projection

namespace TwoDimensionalSenguptaCoveringHeatSemigroupBridgeData

omit [T2Space CoverGroup] [Fintype Curve] [Nonempty Curve] [DecidableEq Edge] in
/-- Exact inhabitance audit: one covering-group density semigroup and a measure-level homomorphism
to the unchanged planar semigroup through the finite law's exact projection. -/
theorem nonempty_iff_coverSemigroup_projectionHeat :
    Nonempty (TwoDimensionalSenguptaCoveringHeatSemigroupBridgeData
      (planarSemigroup := planarSemigroup) (finiteLaw := finiteLaw)
      (coverDensity := coverDensity)) ↔
    ∃ coverSemigroup : NormalizedCompactHaarDensitySemigroupData coverDensity,
      Nonempty (NormalizedCompactHaarDensitySemigroupHomData coverSemigroup
        planarSemigroup.toNormalizedCompactHaarDensitySemigroupData finiteLaw.projection) := by
  constructor
  · rintro ⟨bridge⟩
    exact ⟨bridge.coverSemigroup, ⟨bridge.projectionHeat⟩⟩
  · rintro ⟨coverSemigroup, ⟨projectionHeat⟩⟩
    exact ⟨⟨coverSemigroup, projectionHeat⟩⟩

omit [T2Space CoverGroup] [Fintype Curve] [Nonempty Curve] [DecidableEq Edge] in
/-- The same projection used by the finite compact-surface law transports every positive-time heat
measure to the unchanged planar selected-loop measure. -/
theorem map_coverMeasure
    (bridge : TwoDimensionalSenguptaCoveringHeatSemigroupBridgeData
      (planarSemigroup := planarSemigroup) (finiteLaw := finiteLaw)
      (coverDensity := coverDensity))
    {t : ℝ} (ht : 0 < t) :
    Measure.map finiteLaw.projection
        (normalizedCompactHaarDensitySemigroupMeasure coverDensity t) =
      normalizedCompactHaarDensitySemigroupMeasure law.selectedAreaDensity t :=
  bridge.projectionHeat.map_measure t ht

omit [T2Space CoverGroup] [Fintype Curve] [Nonempty Curve] [DecidableEq Edge] in
/-- Continuous planar tests have the exact covering-group pullback expectation. -/
theorem integral_comp_projection
    (bridge : TwoDimensionalSenguptaCoveringHeatSemigroupBridgeData
      (planarSemigroup := planarSemigroup) (finiteLaw := finiteLaw)
      (coverDensity := coverDensity))
    {t : ℝ} (ht : 0 < t) (test : C(G, ℂ)) :
    (∫ g', test (finiteLaw.projection g')
        ∂normalizedCompactHaarDensitySemigroupMeasure coverDensity t) =
      ∫ g, test g
        ∂normalizedCompactHaarDensitySemigroupMeasure law.selectedAreaDensity t :=
  bridge.projectionHeat.integral_comp_projection ht test

end TwoDimensionalSenguptaCoveringHeatSemigroupBridgeData

end

end YangMills.Dimensions
