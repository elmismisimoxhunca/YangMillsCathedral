/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Dimensions.TwoDimensionalSenguptaCoveringHeatSemigroupBridge
import YangMills.Mathematics.FiniteOrientedEdgeFaceWeight

/-!
# Triangulated heat factors in Sengupta's Definition 7.6

This file gives the boundary-conditioned finite-face integral used in the proof of Sengupta Theorem
8.4 after Definition 7.6's delta constraints have fixed the boundary values. External graph-edge
values are fixed, internal edge values are integrated
against normalized Haar, and each positive-area face contributes the same covering-group density.
For the twisted factor, the finite law's fixed central kernel bundle class multiplies the
distinguished face holonomy on the left, matching `Q_a(h x(∂A_*))` in Definition 7.6.

The three-traversal face words are not asserted closed, composable, or underlying-edge-distinct. The
resulting bridge is intentionally uninhabited. It does not prove triangulation/area-splitting
independence, topological invariance, admissibility, or the existence of the required finite
presentation.
-/

namespace YangMills.Dimensions

open MeasureTheory
open YangMills.Mathematics
open scoped ENNReal BigOperators

noncomputable section

universe uG uCover uGauge uSample uConnection uCurve uEdge uInternalEdge uFace uRegion
  uSenguptaSample

/-- One explicit finite-face candidate presentation for all complementary regions. It does not by
itself certify an embedded topological triangulation. -/
structure TwoDimensionalSenguptaTriangulatedRegionData
    (Edge : Type uEdge) (InternalEdge : Type uInternalEdge)
    (Face : Type uFace) (Region : Type uRegion)
    [Fintype Face] [DecidableEq Face] [DecidableEq Region] where
  faceRegion : Face → Region
  internalEdgeRegion : InternalEdge → Region
  faceArea : Face → ℝ
  faceArea_pos : ∀ face, 0 < faceArea face
  regionArea : Region → ℝ
  regionArea_eq_faceArea_sum : ∀ region,
    regionArea region = ∑ face ∈ Finset.univ.filter (fun face => faceRegion face = region),
      faceArea face
  regionArea_pos : ∀ region, 0 < regionArea region
  boundaryWord : Face → List (OrientedEdge (Sum Edge InternalEdge))
  boundaryWord_length_three : ∀ face, (boundaryWord face).length = 3
  /-- Internal edges used by a face belong to that same complementary region. -/
  boundaryWord_internal_sameRegion : ∀ face orientedEdge,
    orientedEdge ∈ boundaryWord face →
    ∀ internalEdge, OrientedEdge.underlying orientedEdge = Sum.inr internalEdge →
      internalEdgeRegion internalEdge = faceRegion face
  /-- One distinguished face in every nonempty region presentation. -/
  distinguishedFace : Region → Face
  distinguishedFace_region : ∀ region, faceRegion (distinguishedFace region) = region

/-- Combine fixed external graph values and integrated internal values. -/
def senguptaCombinedEdgeField
    {Edge : Type uEdge} {InternalEdge : Type uInternalEdge} {G : Type uG}
    (external : Edge → G) (internal : InternalEdge → G) : Sum Edge InternalEdge → G :=
  Sum.elim external internal

/-- Product of covering heat-density factors over exactly the candidate faces assigned to one
region. -/
def senguptaTriangulatedRegionDensityProduct
    {CoverGroup : Type uCover} [Group CoverGroup]
    {Edge : Type uEdge} {InternalEdge : Type uInternalEdge}
    {Face : Type uFace} [Fintype Face] [DecidableEq Face]
    {Region : Type uRegion} [DecidableEq Region]
    (triangulation : TwoDimensionalSenguptaTriangulatedRegionData
      Edge InternalEdge Face Region)
    (coverDensity : ℝ → CoverGroup → ℝ≥0∞)
    (region : Region) (external : Edge → CoverGroup)
    (internal : InternalEdge → CoverGroup) : ℝ≥0∞ :=
  ∏ face ∈ Finset.univ.filter (fun face => triangulation.faceRegion face = region),
    coverDensity (triangulation.faceArea face)
      (finiteOrientedWordHolonomy (senguptaCombinedEdgeField external internal)
        (triangulation.boundaryWord face))

/-- The Definition 7.6 twist: only the chosen face receives left multiplication by `h`. -/
def senguptaTriangulatedTwistedRegionDensityProduct
    {CoverGroup : Type uCover} [Group CoverGroup]
    {Edge : Type uEdge} {InternalEdge : Type uInternalEdge}
    {Face : Type uFace} [Fintype Face] [DecidableEq Face]
    {Region : Type uRegion} [DecidableEq Region]
    (triangulation : TwoDimensionalSenguptaTriangulatedRegionData
      Edge InternalEdge Face Region)
    (coverDensity : ℝ → CoverGroup → ℝ≥0∞)
    (bundleClass : CoverGroup) (region : Region)
    (external : Edge → CoverGroup) (internal : InternalEdge → CoverGroup) : ℝ≥0∞ :=
  ∏ face ∈ Finset.univ.filter (fun face => triangulation.faceRegion face = region),
    coverDensity (triangulation.faceArea face)
      (if face = triangulation.distinguishedFace region then
        bundleClass * finiteOrientedWordHolonomy
          (senguptaCombinedEdgeField external internal) (triangulation.boundaryWord face)
      else
        finiteOrientedWordHolonomy
          (senguptaCombinedEdgeField external internal) (triangulation.boundaryWord face))

/-- Ordinary boundary-conditioned factor from one finite-face candidate presentation. -/
def senguptaTriangulatedRegionFactor
    {CoverGroup : Type uCover} [Group CoverGroup]
    [TopologicalSpace CoverGroup] [IsTopologicalGroup CoverGroup]
    [CompactSpace CoverGroup] [MeasurableSpace CoverGroup] [BorelSpace CoverGroup]
    {Edge : Type uEdge} {InternalEdge : Type uInternalEdge} [Fintype InternalEdge]
    {Face : Type uFace} [Fintype Face] [DecidableEq Face]
    {Region : Type uRegion} [DecidableEq Region]
    (triangulation : TwoDimensionalSenguptaTriangulatedRegionData
      Edge InternalEdge Face Region)
    (coverDensity : ℝ → CoverGroup → ℝ≥0∞)
    (region : Region) (external : Edge → CoverGroup) : ℝ≥0∞ :=
  ∫⁻ internal, senguptaTriangulatedRegionDensityProduct triangulation coverDensity
    region external internal
    ∂normalizedCompactHaarFiniteProductMeasure (Edge := InternalEdge) (G := CoverGroup)

/-- Twisted boundary-conditioned factor from the same candidate presentation. -/
def senguptaTriangulatedTwistedRegionFactor
    {CoverGroup : Type uCover} [Group CoverGroup]
    [TopologicalSpace CoverGroup] [IsTopologicalGroup CoverGroup]
    [CompactSpace CoverGroup] [MeasurableSpace CoverGroup] [BorelSpace CoverGroup]
    {Edge : Type uEdge} {InternalEdge : Type uInternalEdge} [Fintype InternalEdge]
    {Face : Type uFace} [Fintype Face] [DecidableEq Face]
    {Region : Type uRegion} [DecidableEq Region]
    (triangulation : TwoDimensionalSenguptaTriangulatedRegionData
      Edge InternalEdge Face Region)
    (coverDensity : ℝ → CoverGroup → ℝ≥0∞)
    (bundleClass : CoverGroup) (region : Region) (external : Edge → CoverGroup) : ℝ≥0∞ :=
  ∫⁻ internal, senguptaTriangulatedTwistedRegionDensityProduct triangulation coverDensity
    bundleClass region external internal
    ∂normalizedCompactHaarFiniteProductMeasure (Edge := InternalEdge) (G := CoverGroup)

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

/-- Exact missing link from the covering heat semigroup to one chosen finite-face candidate
realization of all region factors used by the finite compact-surface law. -/
structure TwoDimensionalSenguptaTriangulatedHeatFactorBridgeData where
  coveringHeat : TwoDimensionalSenguptaCoveringHeatSemigroupBridgeData
    (planarSemigroup := planarSemigroup) (finiteLaw := finiteLaw)
    (coverDensity := coverDensity)
  triangulation : TwoDimensionalSenguptaTriangulatedRegionData
    Edge InternalEdge Face Region
  ordinaryRegionWeight_eq : ∀ region external,
    finiteLaw.ordinaryRegionWeight region external =
      senguptaTriangulatedRegionFactor triangulation coverDensity region external
  twistedRegionWeight_eq : ∀ region external,
    finiteLaw.twistedRegionWeight finiteLaw.bundleClass region external =
      senguptaTriangulatedTwistedRegionFactor triangulation coverDensity
        finiteLaw.bundleClass region external

end

end YangMills.Dimensions
