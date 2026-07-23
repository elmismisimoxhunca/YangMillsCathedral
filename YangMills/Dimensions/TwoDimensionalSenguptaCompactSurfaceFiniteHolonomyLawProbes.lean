/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Dimensions.TwoDimensionalSenguptaCompactSurfaceFiniteHolonomyLaw

/-! Hostile probes for the Sengupta compact-surface finite holonomy law. -/

namespace YangMills.Dimensions.TwoDimensionalSenguptaCompactSurfaceFiniteHolonomyLaw.Probes

open MeasureTheory
open YangMills.Mathematics
open scoped ENNReal

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
    (data : TwoDimensionalSenguptaCompactSurfaceFiniteHolonomyLawData
      (G := G) (CoverGroup := CoverGroup) (Curve := Curve) (Edge := Edge)
      (Region := Region) (Sample := Sample))

omit [TopologicalSpace G] [MeasurableSpace G] [TopologicalSpace CoverGroup]
    [IsTopologicalGroup CoverGroup] [CompactSpace CoverGroup] [T2Space CoverGroup]
    [MeasurableSpace CoverGroup] [BorelSpace CoverGroup] [Fintype Curve] [Nonempty Curve]
    [Fintype Edge] [DecidableEq Edge] in
/-- Reverse oriented graph edges use inversion before the covering projection. -/
theorem exact_reverse_edge_holonomy
    (projection : CoverGroup →* G) (field : Edge → CoverGroup)
    (curve : Curve) (edge : Edge) :
    senguptaFiniteGraphHolonomy projection (fun _ => [OrientedEdge.reverse edge]) field curve =
      projection (field edge)⁻¹ := by
  simp [senguptaFiniteGraphHolonomy, finiteOrientedWordHolonomy]

omit [T2Space CoverGroup] [Fintype Curve] [Nonempty Curve] [DecidableEq Edge] in
/-- The bounded measurable-test equation (8.3) is derived from the pushforward law. -/
theorem exact_bounded_test_equation
    (test : (Curve → G) → ℝ) (test_measurable : Measurable test)
    (bounded : ∃ bound : ℝ, ∀ holonomies, |test holonomies| ≤ bound) :
    (∫ sample, test (data.sampleHolonomy sample) ∂data.sampleMeasure) =
      ∫ field, test (senguptaFiniteGraphHolonomy data.projection data.curveWord field)
        ∂senguptaCompactSurfaceGraphMeasure data.partitionFunction data.bundleClass
          data.distinguishedRegion data.ordinaryRegionWeight data.twistedRegionWeight :=
  data.integral_eq_graphIntegral test test_measurable bounded

omit [T2Space CoverGroup] [Fintype Curve] [Nonempty Curve] [DecidableEq Edge] in
/-- Hostile equation probe: a changed bounded-test expectation is rejected. -/
theorem changed_bounded_test_equation_blocked
    (test : (Curve → G) → ℝ) (test_measurable : Measurable test)
    (bounded : ∃ bound : ℝ, ∀ holonomies, |test holonomies| ≤ bound)
    (changed : (∫ sample, test (data.sampleHolonomy sample) ∂data.sampleMeasure) ≠
      ∫ field, test (senguptaFiniteGraphHolonomy data.projection data.curveWord field)
        ∂senguptaCompactSurfaceGraphMeasure data.partitionFunction data.bundleClass
          data.distinguishedRegion data.ordinaryRegionWeight data.twistedRegionWeight) : False :=
  changed (data.integral_eq_graphIntegral test test_measurable bounded)

omit [T2Space CoverGroup] [Fintype Curve] [Nonempty Curve] [DecidableEq Edge] in
/-- Equation (8.3) is retained as an exact pushforward identity on the named graph weight. -/
theorem exact_finite_dimensional_law :
    Measure.map data.sampleHolonomy data.sampleMeasure =
      Measure.map (senguptaFiniteGraphHolonomy data.projection data.curveWord)
        (senguptaCompactSurfaceGraphMeasure data.partitionFunction data.bundleClass
          data.distinguishedRegion data.ordinaryRegionWeight data.twistedRegionWeight) :=
  data.finiteDimensionalLaw

omit [T2Space CoverGroup] [Fintype Curve] [Nonempty Curve] [DecidableEq Edge] in
/-- The physical projection is a genuine topological covering map, not merely a homomorphism. -/
theorem exact_covering_projection :
    IsCoveringMap data.projection ∧ Function.Surjective data.projection :=
  ⟨data.projection_isCoveringMap, data.projection_surjective⟩

/-- The finite curve-family hypothesis is actual typeclass evidence. -/
theorem exact_finite_nonempty_curve_family : Finite Curve ∧ Nonempty Curve :=
  ⟨inferInstance, inferInstance⟩

omit [T2Space CoverGroup] [Fintype Curve] [Nonempty Curve] [DecidableEq Edge] in
/-- The global factor is exactly the unnormalized graph partition function from equation (8.3). -/
theorem exact_partition_function : data.partitionFunction =
    ∫⁻ field, senguptaCompactSurfaceGraphWeight data.bundleClass data.distinguishedRegion
      data.ordinaryRegionWeight data.twistedRegionWeight field
      ∂normalizedCompactHaarFiniteProductMeasure (Edge := Edge) (G := CoverGroup) :=
  data.partitionFunction_eq_lintegral

omit [T2Space CoverGroup] [Fintype Curve] [Nonempty Curve] [DecidableEq Edge] in
/-- The source permits any distinguished complementary region; the normalized graph law is
independent of that choice. -/
theorem exact_distinguished_region_independence (otherRegion : Region) :
    Measure.map (senguptaFiniteGraphHolonomy data.projection data.curveWord)
      (senguptaCompactSurfaceGraphMeasure data.partitionFunction data.bundleClass otherRegion
        data.ordinaryRegionWeight data.twistedRegionWeight) =
    Measure.map (senguptaFiniteGraphHolonomy data.projection data.curveWord)
      (senguptaCompactSurfaceGraphMeasure data.partitionFunction data.bundleClass
        data.distinguishedRegion data.ordinaryRegionWeight data.twistedRegionWeight) :=
  data.holonomyLaw_independent_distinguishedRegion otherRegion

omit [T2Space CoverGroup] [Fintype Curve] [Nonempty Curve] [DecidableEq Edge] in
/-- Hostile bundle-topology probe: a proposed class outside the projection kernel is rejected. -/
theorem outside_kernel_blocked
    (outside : data.projection data.bundleClass ≠ 1) : False :=
  outside data.bundleClass_mem_kernel

omit [T2Space CoverGroup] [Fintype Curve] [Nonempty Curve] [DecidableEq Edge] in
/-- Hostile centrality probe: a noncentral proposed bundle class is rejected. -/
theorem noncentral_bundle_class_blocked
    (element : CoverGroup)
    (noncentral : data.bundleClass * element ≠ element * data.bundleClass) : False :=
  noncentral (data.bundleClass_central element)

omit [T2Space CoverGroup] [Fintype Curve] [Nonempty Curve] [DecidableEq Edge] in
/-- Hostile normalization probe: neither zero nor infinite may serve as equation (8.3)'s global
partition function. -/
theorem degenerate_partition_function_blocked
    (degenerate : data.partitionFunction = 0 ∨ data.partitionFunction = ⊤) : False := by
  rcases degenerate with zero | top
  · exact data.partitionFunction_ne_zero zero
  · exact data.partitionFunction_ne_top top

omit [T2Space CoverGroup] [Fintype Curve] [Nonempty Curve] [DecidableEq Edge] in
/-- Hostile probability probe: the stochastic compact-surface law cannot be the zero measure. -/
theorem zero_sample_law_blocked (zeroMeasure : data.sampleMeasure = 0) : False :=
  data.sampleMeasure_ne_zero zeroMeasure

end

end YangMills.Dimensions.TwoDimensionalSenguptaCompactSurfaceFiniteHolonomyLaw.Probes
