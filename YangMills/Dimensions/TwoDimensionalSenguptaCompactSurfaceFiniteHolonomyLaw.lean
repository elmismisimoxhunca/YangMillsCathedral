/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import Mathlib.Topology.Covering.Basic
import YangMills.Mathematics.FiniteOrientedEdgeWord
import YangMills.Mathematics.NormalizedCompactHaarFiniteProduct

/-!
# Sengupta compact-surface finite holonomy law

This file isolates the measure-theoretic conclusion of Sengupta 1997, Theorem 8.4, equation (8.3).
For an admissible finite family of commonly based closed curves on a compact surface, the joint
Yang--Mills holonomy law is the pushforward of normalized Haar fields on the etched finite graph,
weighted by one bundle-class-twisted complementary-region factor and the remaining untwisted
region factors.

The topology of the surface, admissibility of the curves, construction of Sengupta's `Z` factors
from the heat kernel, and construction of the stochastic Yang--Mills measure are deliberately not
inferred here. The source's semisimple/boundary/nonorientable disjunction is likewise not replaced by
a content-free tag: compactness of the covering group is required directly, and a future geometric
construction must discharge the actual source alternatives. They are the witnesses required by this uninhabited source-facing interface. In
particular, this file does not identify these region factors with the existing planar spectral heat
kernel and does not construct a compact-surface Yang--Mills law.
-/

namespace YangMills.Dimensions

open MeasureTheory
open YangMills.Mathematics
open scoped ENNReal BigOperators

noncomputable section

universe uG uCover uCurve uEdge uRegion uSample

variable
    {G : Type uG} [Group G] [TopologicalSpace G] [MeasurableSpace G]
    {CoverGroup : Type uCover} [Group CoverGroup]
    [TopologicalSpace CoverGroup] [IsTopologicalGroup CoverGroup]
    [CompactSpace CoverGroup] [T2Space CoverGroup]
    [MeasurableSpace CoverGroup] [BorelSpace CoverGroup]
    {Curve : Type uCurve} [Fintype Curve] [Nonempty Curve]
    {Edge : Type uEdge} {Region : Type uRegion}
    [Fintype Edge] [DecidableEq Edge] [Fintype Region] [DecidableEq Region]
    {Sample : Type uSample} [MeasurableSpace Sample]

/-- Graph holonomies on the covering group, projected to the physical gauge group. -/
def senguptaFiniteGraphHolonomy
    (projection : CoverGroup →* G)
    (curveWord : Curve → List (OrientedEdge Edge))
    (field : Edge → CoverGroup) : Curve → G :=
  fun curve => projection (finiteOrientedWordHolonomy field (curveWord curve))

/-- Equation (8.3)'s product of one bundle-class-twisted region factor and every remaining ordinary
region factor. -/
def senguptaCompactSurfaceGraphWeight
    (bundleClass : CoverGroup) (distinguishedRegion : Region)
    (ordinaryRegionWeight : Region → (Edge → CoverGroup) → ℝ≥0∞)
    (twistedRegionWeight : CoverGroup → Region → (Edge → CoverGroup) → ℝ≥0∞)
    (field : Edge → CoverGroup) : ℝ≥0∞ :=
  twistedRegionWeight bundleClass distinguishedRegion field *
    ∏ region ∈ Finset.univ.erase distinguishedRegion, ordinaryRegionWeight region field

/-- The globally normalized weighted Haar finite-graph measure on the right of Sengupta Theorem
8.4, equation (8.3), including the required inverse partition function. -/
def senguptaCompactSurfaceGraphMeasure
    (partitionFunction : ℝ≥0∞)
    (bundleClass : CoverGroup) (distinguishedRegion : Region)
    (ordinaryRegionWeight : Region → (Edge → CoverGroup) → ℝ≥0∞)
    (twistedRegionWeight : CoverGroup → Region → (Edge → CoverGroup) → ℝ≥0∞) :
    Measure (Edge → CoverGroup) :=
  (normalizedCompactHaarFiniteProductMeasure (Edge := Edge) (G := CoverGroup)).withDensity
    (fun field => partitionFunction⁻¹ *
      senguptaCompactSurfaceGraphWeight bundleClass distinguishedRegion
        ordinaryRegionWeight twistedRegionWeight field)

/-- Source-facing finite-dimensional compact-surface law from Sengupta Theorem 8.4.

`finiteDimensionalLaw` is the literal equality in law behind equation (8.3). The record does not
postulate that arbitrary factors are heat-kernel factors: a future construction must separately tie
`ordinaryRegionWeight` and `twistedRegionWeight` to Definition 7.6 and hence to the same heat kernel
used by the planar chain. -/
structure TwoDimensionalSenguptaCompactSurfaceFiniteHolonomyLawData where
  projection : CoverGroup →* G
  projection_isCoveringMap : IsCoveringMap projection
  projection_surjective : Function.Surjective projection
  bundleClass : CoverGroup
  bundleClass_mem_kernel : projection bundleClass = 1
  bundleClass_central : ∀ element, bundleClass * element = element * bundleClass
  curveWord : Curve → List (OrientedEdge Edge)
  distinguishedRegion : Region
  ordinaryRegionWeight : Region → (Edge → CoverGroup) → ℝ≥0∞
  twistedRegionWeight : CoverGroup → Region → (Edge → CoverGroup) → ℝ≥0∞
  graphWeight_measurable : Measurable
    (senguptaCompactSurfaceGraphWeight bundleClass distinguishedRegion
      ordinaryRegionWeight twistedRegionWeight)
  partitionFunction : ℝ≥0∞
  partitionFunction_eq_lintegral : partitionFunction =
    ∫⁻ field, senguptaCompactSurfaceGraphWeight bundleClass distinguishedRegion
      ordinaryRegionWeight twistedRegionWeight field
      ∂normalizedCompactHaarFiniteProductMeasure (Edge := Edge) (G := CoverGroup)
  partitionFunction_ne_zero : partitionFunction ≠ 0
  partitionFunction_ne_top : partitionFunction ≠ ⊤
  holonomyLaw_independent_distinguishedRegion : ∀ otherRegion,
    Measure.map (senguptaFiniteGraphHolonomy projection curveWord)
      (senguptaCompactSurfaceGraphMeasure partitionFunction bundleClass otherRegion
        ordinaryRegionWeight twistedRegionWeight) =
    Measure.map (senguptaFiniteGraphHolonomy projection curveWord)
      (senguptaCompactSurfaceGraphMeasure partitionFunction bundleClass distinguishedRegion
        ordinaryRegionWeight twistedRegionWeight)
  sampleMeasure : Measure Sample
  sampleMeasure_univ : sampleMeasure Set.univ = 1
  sampleHolonomy : Sample → Curve → G
  sampleHolonomy_measurable : Measurable sampleHolonomy
  graphHolonomy_measurable : Measurable
    (senguptaFiniteGraphHolonomy projection curveWord)
  finiteDimensionalLaw :
    Measure.map sampleHolonomy sampleMeasure =
      Measure.map (senguptaFiniteGraphHolonomy projection curveWord)
        (senguptaCompactSurfaceGraphMeasure partitionFunction bundleClass distinguishedRegion
          ordinaryRegionWeight twistedRegionWeight)

namespace TwoDimensionalSenguptaCompactSurfaceFiniteHolonomyLawData

omit [T2Space CoverGroup] [Fintype Curve] [Nonempty Curve] [DecidableEq Edge] in
/-- Bounded measurable real-test form of Sengupta equation (8.3), derived from the exact equality in
law rather than stored as a duplicate field. -/
theorem integral_eq_graphIntegral
    (data : TwoDimensionalSenguptaCompactSurfaceFiniteHolonomyLawData
      (G := G) (CoverGroup := CoverGroup) (Curve := Curve) (Edge := Edge)
      (Region := Region) (Sample := Sample))
    (test : (Curve → G) → ℝ) (test_measurable : Measurable test)
    (_bounded : ∃ bound : ℝ, ∀ holonomies, |test holonomies| ≤ bound) :
    (∫ sample, test (data.sampleHolonomy sample) ∂data.sampleMeasure) =
      ∫ field, test (senguptaFiniteGraphHolonomy data.projection data.curveWord field)
        ∂senguptaCompactSurfaceGraphMeasure data.partitionFunction data.bundleClass
          data.distinguishedRegion data.ordinaryRegionWeight data.twistedRegionWeight := by
  rw [← integral_map data.sampleHolonomy_measurable.aemeasurable
    test_measurable.aestronglyMeasurable, data.finiteDimensionalLaw]
  exact integral_map data.graphHolonomy_measurable.aemeasurable
    test_measurable.aestronglyMeasurable

omit [T2Space CoverGroup] [Fintype Curve] [Nonempty Curve] [DecidableEq Edge] in
/-- Nonnegative measurable-test form of the same equation (8.3). -/
theorem lintegral_eq_graphLIntegral
    (data : TwoDimensionalSenguptaCompactSurfaceFiniteHolonomyLawData
      (G := G) (CoverGroup := CoverGroup) (Curve := Curve) (Edge := Edge)
      (Region := Region) (Sample := Sample))
    (test : (Curve → G) → ℝ≥0∞) (test_measurable : Measurable test) :
    (∫⁻ sample, test (data.sampleHolonomy sample) ∂data.sampleMeasure) =
      ∫⁻ field, test (senguptaFiniteGraphHolonomy data.projection data.curveWord field)
        ∂senguptaCompactSurfaceGraphMeasure data.partitionFunction data.bundleClass
          data.distinguishedRegion data.ordinaryRegionWeight data.twistedRegionWeight := by
  calc
    _ = ∫⁻ holonomies, test holonomies
        ∂Measure.map data.sampleHolonomy data.sampleMeasure :=
      (lintegral_map test_measurable data.sampleHolonomy_measurable).symm
    _ = ∫⁻ holonomies, test holonomies
        ∂Measure.map (senguptaFiniteGraphHolonomy data.projection data.curveWord)
          (senguptaCompactSurfaceGraphMeasure data.partitionFunction data.bundleClass
            data.distinguishedRegion data.ordinaryRegionWeight data.twistedRegionWeight) := by
      rw [data.finiteDimensionalLaw]
    _ = _ := lintegral_map test_measurable data.graphHolonomy_measurable

omit [T2Space CoverGroup] [Fintype Curve] [Nonempty Curve] [DecidableEq Edge] in
/-- The finite-dimensional law retains the exact bundle class rather than silently replacing it by
the trivial bundle. -/
theorem exact_bundle_class
    (data : TwoDimensionalSenguptaCompactSurfaceFiniteHolonomyLawData
      (G := G) (CoverGroup := CoverGroup) (Curve := Curve) (Edge := Edge)
      (Region := Region) (Sample := Sample)) :
    data.projection data.bundleClass = 1 :=
  data.bundleClass_mem_kernel

omit [T2Space CoverGroup] [Fintype Curve] [Nonempty Curve] [DecidableEq Edge] in
/-- The designated stochastic compact-surface law is nonzero, derived from source normalization. -/
theorem sampleMeasure_ne_zero
    (data : TwoDimensionalSenguptaCompactSurfaceFiniteHolonomyLawData
      (G := G) (CoverGroup := CoverGroup) (Curve := Curve) (Edge := Edge)
      (Region := Region) (Sample := Sample)) :
    data.sampleMeasure ≠ 0 := by
  intro zeroMeasure
  have normalized := data.sampleMeasure_univ
  rw [zeroMeasure] at normalized
  simp at normalized

end TwoDimensionalSenguptaCompactSurfaceFiniteHolonomyLawData

end

end YangMills.Dimensions
