/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Dimensions.TwoDimensionalSenguptaTriangulatedHeatFactors

/-! Hostile probes for Sengupta's triangulated covering-heat factors. -/

namespace YangMills.Dimensions.TwoDimensionalSenguptaTriangulatedHeatFactors.Probes

open MeasureTheory
open YangMills.Mathematics
open scoped ENNReal BigOperators

noncomputable section

universe uG uCover uGauge uSample uConnection uCurve uEdge uInternalEdge uFace uRegion
  uSenguptaSample

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
    {InternalEdge : Type uInternalEdge} [Fintype InternalEdge]
    {Face : Type uFace} [Fintype Face] [DecidableEq Face]
    {Region : Type uRegion} [Fintype Region] [DecidableEq Region]
    {SenguptaSample : Type uSenguptaSample} [MeasurableSpace SenguptaSample]
    {finiteLaw : TwoDimensionalSenguptaCompactSurfaceFiniteHolonomyLawData
      (G := G) (CoverGroup := CoverGroup) (Curve := Curve) (Edge := Edge)
      (Region := Region) (Sample := SenguptaSample)}
    {coverDensity : ℝ → CoverGroup → ℝ≥0∞}
    (bridge : TwoDimensionalSenguptaTriangulatedHeatFactorBridgeData
      (G := G) (Gauge := Gauge) (Sample := Sample) (Connection := Connection)
      (base := base) (law := law) (planarSemigroup := planarSemigroup)
      (CoverGroup := CoverGroup) (Curve := Curve) (Edge := Edge)
      (InternalEdge := InternalEdge) (Face := Face) (Region := Region)
      (SenguptaSample := SenguptaSample) (finiteLaw := finiteLaw)
      (coverDensity := coverDensity))

omit [T2Space CoverGroup] [Fintype Curve] [Nonempty Curve] [DecidableEq Edge] in
/-- Every face area in the chosen presentation is strictly positive. -/
theorem exact_face_area_positive (face : Face) :
    0 < bridge.triangulation.faceArea face :=
  bridge.triangulation.faceArea_pos face

omit [T2Space CoverGroup] [Fintype Curve] [Nonempty Curve] [DecidableEq Edge] in
/-- Every face is represented by exactly three oriented edge traversals. -/
theorem exact_three_traversal_face (face : Face) :
    (bridge.triangulation.boundaryWord face).length = 3 :=
  bridge.triangulation.boundaryWord_length_three face

omit [T2Space CoverGroup] [Fintype Curve] [Nonempty Curve] [DecidableEq Edge] in
/-- Every region area is the positive sum of its exact face areas. -/
theorem exact_region_area (region : Region) :
    bridge.triangulation.regionArea region =
      ∑ face ∈ Finset.univ.filter
        (fun face => bridge.triangulation.faceRegion face = region),
        bridge.triangulation.faceArea face ∧
      0 < bridge.triangulation.regionArea region :=
  ⟨bridge.triangulation.regionArea_eq_faceArea_sum region,
    bridge.triangulation.regionArea_pos region⟩

omit [T2Space CoverGroup] [Fintype Curve] [Nonempty Curve] [DecidableEq Edge] in
/-- Every region has a distinguished candidate face assigned to that same region. -/
theorem exact_distinguished_face (region : Region) :
    bridge.triangulation.faceRegion (bridge.triangulation.distinguishedFace region) = region :=
  bridge.triangulation.distinguishedFace_region region

include bridge in
omit [T2Space CoverGroup] [Fintype Curve] [Nonempty Curve] [DecidableEq Edge] in
/-- The covering heat bridge is retained, so the factors cannot use an unrelated density family. -/
theorem exact_covering_heat :
    TwoDimensionalSenguptaCoveringHeatSemigroupBridgeData
      (planarSemigroup := planarSemigroup) (finiteLaw := finiteLaw)
      (coverDensity := coverDensity) :=
  bridge.coveringHeat

omit [T2Space CoverGroup] [Fintype Curve] [Nonempty Curve] [DecidableEq Edge] in
/-- Hostile ordinary-factor probe: changing the exact triangulated integral is rejected. -/
theorem changed_ordinary_factor_blocked
    (region : Region) (external : Edge → CoverGroup)
    (changed : finiteLaw.ordinaryRegionWeight region external ≠
      senguptaTriangulatedRegionFactor bridge.triangulation coverDensity region external) : False :=
  changed (bridge.ordinaryRegionWeight_eq region external)

omit [T2Space CoverGroup] [Fintype Curve] [Nonempty Curve] [DecidableEq Edge] in
/-- Hostile twisted-factor probe: changing the exact fixed central-kernel-class integral is rejected. -/
theorem changed_twisted_factor_blocked
    (region : Region) (external : Edge → CoverGroup)
    (changed : finiteLaw.twistedRegionWeight finiteLaw.bundleClass region external ≠
      senguptaTriangulatedTwistedRegionFactor bridge.triangulation coverDensity
        finiteLaw.bundleClass region external) : False :=
  changed (bridge.twistedRegionWeight_eq region external)

omit [T2Space CoverGroup] [Fintype Curve] [Nonempty Curve] [DecidableEq Edge] in
/-- Internal edges occurring in a face word are certified to belong to that face's region. -/
theorem exact_internal_edge_region
    (face : Face) (orientedEdge : OrientedEdge (Sum Edge InternalEdge))
    (mem : orientedEdge ∈ bridge.triangulation.boundaryWord face)
    (internalEdge : InternalEdge)
    (underlying : OrientedEdge.underlying orientedEdge = Sum.inr internalEdge) :
    bridge.triangulation.internalEdgeRegion internalEdge =
      bridge.triangulation.faceRegion face :=
  bridge.triangulation.boundaryWord_internal_sameRegion
    face orientedEdge mem internalEdge underlying

omit [T2Space CoverGroup] [Fintype Curve] [Nonempty Curve] [DecidableEq Edge] in
/-- Unfolding the implementation locks the distinguished branch to left multiplication by `h`; this
probe would fail after right multiplication or conjugation. -/
theorem exact_twisted_density_product_definition
    (bundleClass : CoverGroup) (region : Region)
    (external : Edge → CoverGroup) (internal : InternalEdge → CoverGroup) :
    senguptaTriangulatedTwistedRegionDensityProduct bridge.triangulation coverDensity
      bundleClass region external internal =
    ∏ face ∈ Finset.univ.filter
      (fun face => bridge.triangulation.faceRegion face = region),
      coverDensity (bridge.triangulation.faceArea face)
        (if face = bridge.triangulation.distinguishedFace region then
          bundleClass * finiteOrientedWordHolonomy
            (senguptaCombinedEdgeField external internal)
            (bridge.triangulation.boundaryWord face)
        else
          finiteOrientedWordHolonomy (senguptaCombinedEdgeField external internal)
            (bridge.triangulation.boundaryWord face)) :=
  rfl

end

end YangMills.Dimensions.TwoDimensionalSenguptaTriangulatedHeatFactors.Probes
