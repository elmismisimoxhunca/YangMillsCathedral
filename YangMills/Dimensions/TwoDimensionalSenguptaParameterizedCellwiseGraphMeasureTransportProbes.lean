/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Dimensions.TwoDimensionalSenguptaParameterizedCellwiseGraphMeasureTransport

/-! Hostile probes for parameterized cellwise graph-measure transport. -/

namespace YangMills.Dimensions.TwoDimensionalSenguptaParameterizedCellwiseGraphMeasureTransport.Probes

open MeasureTheory
open YangMills.Mathematics
open scoped ENNReal

noncomputable section

universe uCover uCurve uEdge uInternal uFace uRegion uSurface uVertex
  uTargetEdge uTargetInternal uTargetFace uTargetRegion uTargetSurface uTargetVertex

variable
    {CoverGroup : Type uCover} [Group CoverGroup]
    [TopologicalSpace CoverGroup] [IsTopologicalGroup CoverGroup]
    [CompactSpace CoverGroup] [T2Space CoverGroup]
    [MeasurableSpace CoverGroup] [BorelSpace CoverGroup]
    [MeasurableMul₂ CoverGroup] [MeasurableInv CoverGroup]
    {Curve : Type uCurve} [Fintype Curve] [Nonempty Curve]
    {Edge : Type uEdge} [Fintype Edge] [DecidableEq Edge]
    {InternalEdge : Type uInternal} [Fintype InternalEdge] [DecidableEq InternalEdge]
    {Face : Type uFace} [Fintype Face] [DecidableEq Face]
    {Region : Type uRegion} [Fintype Region] [DecidableEq Region]
    {Surface : Type uSurface} [TopologicalSpace Surface]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) Surface]
    {Vertex : Type uVertex}
    {baseTriangulation : TwoDimensionalSenguptaTriangulatedRegionData
      Edge InternalEdge Face Region}
    {baseClosed : TwoDimensionalSenguptaClosedTriangularPresentationData
      (Vertex := Vertex) baseTriangulation}
    {baseEmbedded : TwoDimensionalSenguptaEmbeddedTriangularPresentationData
      (Surface := Surface) (Curve := Curve) (closed := baseClosed)}
    {TargetEdge : Type uTargetEdge} [Fintype TargetEdge] [DecidableEq TargetEdge]
    {TargetInternal : Type uTargetInternal} [Fintype TargetInternal]
    [DecidableEq TargetInternal]
    {TargetFace : Type uTargetFace} [Fintype TargetFace] [DecidableEq TargetFace]
    {TargetRegion : Type uTargetRegion} [Fintype TargetRegion] [DecidableEq TargetRegion]
    {TargetSurface : Type uTargetSurface} [TopologicalSpace TargetSurface]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) TargetSurface]
    {TargetVertex : Type uTargetVertex}
    {target : TwoDimensionalSenguptaTriangulatedRegionData
      TargetEdge TargetInternal TargetFace TargetRegion}
    {targetClosed : TwoDimensionalSenguptaClosedTriangularPresentationData
      (Vertex := TargetVertex) target}
    {targetEmbedded : TwoDimensionalSenguptaEmbeddedTriangularPresentationData
      (Surface := TargetSurface) (Curve := Curve) (closed := targetClosed)}
    {coverDensity : ℝ → CoverGroup → ℝ≥0∞}
    {bundleClass : CoverGroup}
    {geometry : TwoDimensionalSenguptaCellwiseEmbeddedHomeomorphismGeometryData
      (baseEmbedded := baseEmbedded) (targetEmbedded := targetEmbedded)}
    (data : TwoDimensionalSenguptaParameterizedCellwiseGraphMeasureTransportData
      (coverDensity := coverDensity) (bundleClass := bundleClass) (geometry := geometry))

omit [T2Space CoverGroup] [MeasurableMul₂ CoverGroup] [MeasurableInv CoverGroup]
    [Nonempty Curve] in
/-- Exact positive probe: both transported normalized density-semigroup graph measures have unit mass at every
region choice. -/
theorem exact_all_region_nonvacuity (region : Region) :
    senguptaCompactSurfaceGraphMeasure data.sourcePartitionFunction bundleClass region
        (senguptaTriangulatedRegionFactor baseTriangulation coverDensity)
        (senguptaTriangulatedTwistedRegionFactor baseTriangulation coverDensity) Set.univ = 1 ∧
    senguptaCompactSurfaceGraphMeasure data.targetPartitionFunction
        (senguptaTransportedBundleClass geometry.orientationSign bundleClass)
        (geometry.regionEquiv region)
        (senguptaTriangulatedRegionFactor target coverDensity)
        (senguptaTriangulatedTwistedRegionFactor target coverDensity) Set.univ = 1 :=
  data.all_region_nonvacuity region

omit [T2Space CoverGroup] [MeasurableMul₂ CoverGroup] [MeasurableInv CoverGroup]
    [Nonempty Curve] in
include data in
/-- Hostile geometry probe: the normalized transport cannot be disconnected from the exact
cellwise factor certificate. -/
theorem missing_factor_certificate_blocked
    (missing : ¬geometry.HasFactorCertificate
      (coverDensity := coverDensity) (bundleClass := bundleClass)) : False :=
  missing
    (TwoDimensionalSenguptaParameterizedCellwiseGraphMeasureTransportData.factorCertificate data)

omit [T2Space CoverGroup] [MeasurableMul₂ CoverGroup] [MeasurableInv CoverGroup]
    [Nonempty Curve] in
/-- The selected-region normalizers retain their literal integrals and finite nonzero conditions. -/
theorem exact_normalizer_integrals_and_nonvacuity :
    data.sourcePartitionFunction =
        ∫⁻ field, senguptaCompactSurfaceGraphWeight bundleClass data.distinguishedRegion
          (senguptaTriangulatedRegionFactor baseTriangulation coverDensity)
          (senguptaTriangulatedTwistedRegionFactor baseTriangulation coverDensity) field
          ∂normalizedCompactHaarFiniteProductMeasure (Edge := Edge) (G := CoverGroup) ∧
      data.sourcePartitionFunction ≠ 0 ∧ data.sourcePartitionFunction ≠ ⊤ ∧
      data.targetPartitionFunction =
        ∫⁻ field, senguptaCompactSurfaceGraphWeight
          (senguptaTransportedBundleClass geometry.orientationSign bundleClass)
          (geometry.regionEquiv data.distinguishedRegion)
          (senguptaTriangulatedRegionFactor target coverDensity)
          (senguptaTriangulatedTwistedRegionFactor target coverDensity) field
          ∂normalizedCompactHaarFiniteProductMeasure (Edge := TargetEdge) (G := CoverGroup) ∧
      data.targetPartitionFunction ≠ 0 ∧ data.targetPartitionFunction ≠ ⊤ :=
  ⟨data.sourcePartitionFunction_eq_lintegral, data.sourcePartitionFunction_ne_zero,
    data.sourcePartitionFunction_ne_top, data.targetPartitionFunction_eq_lintegral,
    data.targetPartitionFunction_ne_zero, data.targetPartitionFunction_ne_top⟩

omit [T2Space CoverGroup] [MeasurableMul₂ CoverGroup] [MeasurableInv CoverGroup]
    [Nonempty Curve] in
/-- Hostile normalization probe: changing the source normalizer's literal integral is rejected. -/
theorem changed_source_normalizer_integral_blocked
    (changed : data.sourcePartitionFunction ≠
      ∫⁻ field, senguptaCompactSurfaceGraphWeight bundleClass data.distinguishedRegion
        (senguptaTriangulatedRegionFactor baseTriangulation coverDensity)
        (senguptaTriangulatedTwistedRegionFactor baseTriangulation coverDensity) field
        ∂normalizedCompactHaarFiniteProductMeasure (Edge := Edge) (G := CoverGroup)) : False :=
  changed data.sourcePartitionFunction_eq_lintegral

omit [T2Space CoverGroup] [MeasurableMul₂ CoverGroup] [MeasurableInv CoverGroup]
    [Nonempty Curve] in
/-- Hostile normalization probe: zero or infinite target normalizers are rejected. -/
theorem degenerate_target_normalizer_blocked
    (degenerate : data.targetPartitionFunction = 0 ∨ data.targetPartitionFunction = ⊤) : False :=
  degenerate.elim data.targetPartitionFunction_ne_zero data.targetPartitionFunction_ne_top

omit [T2Space CoverGroup] [MeasurableMul₂ CoverGroup] [MeasurableInv CoverGroup]
    [Nonempty Curve] in
/-- Hostile normalization probe: changing the target/source partition-function equality is
rejected. -/
theorem changed_partition_function_blocked
    (changed : data.targetPartitionFunction ≠ data.sourcePartitionFunction) : False :=
  changed data.partitionFunction_eq

omit [T2Space CoverGroup] [MeasurableMul₂ CoverGroup] [MeasurableInv CoverGroup]
    [Nonempty Curve] in
/-- Hostile analytic probe: changing the exact coordinate pushforward at any region is rejected. -/
theorem changed_cellwise_pushforward_blocked (region : Region)
    (changed : Measure.map (senguptaTransportExternalField geometry.externalEdgeEquiv)
        (senguptaCompactSurfaceGraphMeasure data.sourcePartitionFunction bundleClass region
          (senguptaTriangulatedRegionFactor baseTriangulation coverDensity)
          (senguptaTriangulatedTwistedRegionFactor baseTriangulation coverDensity)) ≠
      senguptaCompactSurfaceGraphMeasure data.targetPartitionFunction
        (senguptaTransportedBundleClass geometry.orientationSign bundleClass)
        (geometry.regionEquiv region)
        (senguptaTriangulatedRegionFactor target coverDensity)
        (senguptaTriangulatedTwistedRegionFactor target coverDensity)) : False :=
  changed (data.graphMeasure_pushforward region)

omit [T2Space CoverGroup] [MeasurableMul₂ CoverGroup] [MeasurableInv CoverGroup]
    [Nonempty Curve] in
include data in
/-- Hostile measurability probe: a nonmeasurable coordinate transport cannot satisfy the record. -/
theorem nonmeasurable_transport_blocked
    (nonmeasurable : ¬Measurable
      (senguptaTransportExternalField geometry.externalEdgeEquiv :
        (Edge → CoverGroup) → TargetEdge → CoverGroup)) : False :=
  nonmeasurable
    (TwoDimensionalSenguptaParameterizedCellwiseGraphMeasureTransportData.transport_measurable data)

omit [T2Space CoverGroup] [MeasurableMul₂ CoverGroup] [MeasurableInv CoverGroup]
    [Nonempty Curve] in
include data in
/-- Exact finite-word probe: coordinate transport preserves every covering-group curve holonomy. -/
theorem exact_covering_curve_holonomy (configuration : Edge → CoverGroup) :
    (fun curve => finiteOrientedWordHolonomy
      (senguptaTransportExternalField geometry.externalEdgeEquiv configuration)
      (targetEmbedded.curveWord curve)) =
    (fun curve => finiteOrientedWordHolonomy configuration (baseEmbedded.curveWord curve)) :=
  data.coveringCurveHolonomy_commutes configuration

omit [T2Space CoverGroup] [Nonempty Curve] in
/-- Hostile projected-law probe: changing the transported complete finite-curve law is rejected. -/
theorem changed_projected_curve_law_blocked
    {G : Type*} [Group G] [MeasurableSpace G]
    (projection : CoverGroup →* G) (projection_measurable : Measurable projection)
    (region : Region)
    (changed : Measure.map (senguptaFiniteGraphHolonomy projection targetEmbedded.curveWord)
        (senguptaCompactSurfaceGraphMeasure data.targetPartitionFunction
          (senguptaTransportedBundleClass geometry.orientationSign bundleClass)
          (geometry.regionEquiv region)
          (senguptaTriangulatedRegionFactor target coverDensity)
          (senguptaTriangulatedTwistedRegionFactor target coverDensity)) ≠
      Measure.map (senguptaFiniteGraphHolonomy projection baseEmbedded.curveWord)
        (senguptaCompactSurfaceGraphMeasure data.sourcePartitionFunction bundleClass region
          (senguptaTriangulatedRegionFactor baseTriangulation coverDensity)
          (senguptaTriangulatedTwistedRegionFactor baseTriangulation coverDensity))) : False :=
  changed (data.map_projectedCurveHolonomy_eq projection projection_measurable region)

end

end YangMills.Dimensions.TwoDimensionalSenguptaParameterizedCellwiseGraphMeasureTransport.Probes
