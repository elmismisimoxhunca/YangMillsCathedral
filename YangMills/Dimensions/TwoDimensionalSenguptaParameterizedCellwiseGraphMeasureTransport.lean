/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Dimensions.TwoDimensionalSenguptaUniversalCellwiseEmbeddedHomeomorphism
import YangMills.Dimensions.TwoDimensionalSenguptaCompactSurfaceFiniteHolonomyLaw

/-!
# Parameterized cellwise graph-measure transport

This module isolates the normalized weighted-measure content needed between the two fine
presentations in Sengupta Fact 3. The geometry and factor certificate are explicit parameters. The
record does not derive coordinate invariance of product Haar measure or integrate the factor
identity; it records the resulting measurable coordinate transport and exact graph-measure
pushforward as analytic obligations.
-/

namespace YangMills.Dimensions

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

/-- Exact normalized graph-measure transport for one parameterized cellwise homeomorphism geometry.
The source and target weights are not arbitrary: they are the boundary-conditioned normalized
covering density-semigroup factors of the two supplied triangulations, with the global bundle class transported by the
homeomorphism orientation sign. -/
structure TwoDimensionalSenguptaParameterizedCellwiseGraphMeasureTransportData where
  factorCertificate : geometry.HasFactorCertificate
    (coverDensity := coverDensity) (bundleClass := bundleClass)
  distinguishedRegion : Region
  sourcePartitionFunction : ℝ≥0∞
  targetPartitionFunction : ℝ≥0∞
  sourceGraphWeight_measurable : Measurable
    (senguptaCompactSurfaceGraphWeight bundleClass distinguishedRegion
      (senguptaTriangulatedRegionFactor baseTriangulation coverDensity)
      (senguptaTriangulatedTwistedRegionFactor baseTriangulation coverDensity))
  targetGraphWeight_measurable : Measurable
    (senguptaCompactSurfaceGraphWeight
      (senguptaTransportedBundleClass geometry.orientationSign bundleClass)
      (geometry.regionEquiv distinguishedRegion)
      (senguptaTriangulatedRegionFactor target coverDensity)
      (senguptaTriangulatedTwistedRegionFactor target coverDensity))
  sourcePartitionFunction_eq_lintegral : sourcePartitionFunction =
    ∫⁻ field, senguptaCompactSurfaceGraphWeight bundleClass distinguishedRegion
      (senguptaTriangulatedRegionFactor baseTriangulation coverDensity)
      (senguptaTriangulatedTwistedRegionFactor baseTriangulation coverDensity) field
      ∂normalizedCompactHaarFiniteProductMeasure (Edge := Edge) (G := CoverGroup)
  targetPartitionFunction_eq_lintegral : targetPartitionFunction =
    ∫⁻ field, senguptaCompactSurfaceGraphWeight
      (senguptaTransportedBundleClass geometry.orientationSign bundleClass)
      (geometry.regionEquiv distinguishedRegion)
      (senguptaTriangulatedRegionFactor target coverDensity)
      (senguptaTriangulatedTwistedRegionFactor target coverDensity) field
      ∂normalizedCompactHaarFiniteProductMeasure (Edge := TargetEdge) (G := CoverGroup)
  sourcePartitionFunction_ne_zero : sourcePartitionFunction ≠ 0
  sourcePartitionFunction_ne_top : sourcePartitionFunction ≠ ⊤
  targetPartitionFunction_ne_zero : targetPartitionFunction ≠ 0
  targetPartitionFunction_ne_top : targetPartitionFunction ≠ ⊤
  partitionFunction_eq : targetPartitionFunction = sourcePartitionFunction
  sourceGraphMeasure_univ : ∀ region,
    senguptaCompactSurfaceGraphMeasure sourcePartitionFunction bundleClass region
      (senguptaTriangulatedRegionFactor baseTriangulation coverDensity)
      (senguptaTriangulatedTwistedRegionFactor baseTriangulation coverDensity) Set.univ = 1
  targetGraphMeasure_univ : ∀ region,
    senguptaCompactSurfaceGraphMeasure targetPartitionFunction
      (senguptaTransportedBundleClass geometry.orientationSign bundleClass)
      (geometry.regionEquiv region)
      (senguptaTriangulatedRegionFactor target coverDensity)
      (senguptaTriangulatedTwistedRegionFactor target coverDensity) Set.univ = 1
  transport_measurable : Measurable
    (senguptaTransportExternalField geometry.externalEdgeEquiv :
      (Edge → CoverGroup) → TargetEdge → CoverGroup)
  graphMeasure_pushforward : ∀ region,
    Measure.map (senguptaTransportExternalField geometry.externalEdgeEquiv)
      (senguptaCompactSurfaceGraphMeasure sourcePartitionFunction bundleClass region
        (senguptaTriangulatedRegionFactor baseTriangulation coverDensity)
        (senguptaTriangulatedTwistedRegionFactor baseTriangulation coverDensity)) =
    senguptaCompactSurfaceGraphMeasure targetPartitionFunction
      (senguptaTransportedBundleClass geometry.orientationSign bundleClass)
      (geometry.regionEquiv region)
      (senguptaTriangulatedRegionFactor target coverDensity)
      (senguptaTriangulatedTwistedRegionFactor target coverDensity)

namespace TwoDimensionalSenguptaParameterizedCellwiseGraphMeasureTransportData

omit [T2Space CoverGroup] [MeasurableMul₂ CoverGroup] [MeasurableInv CoverGroup]
    [Nonempty Curve] in
/-- The stored transport is the literal coordinate pushforward between the two normalized covering density-semigroup graph
measures for every complementary region. -/
theorem exact_graphMeasure_pushforward
    (data : TwoDimensionalSenguptaParameterizedCellwiseGraphMeasureTransportData
      (coverDensity := coverDensity) (bundleClass := bundleClass) (geometry := geometry))
    (region : Region) :
    Measure.map (senguptaTransportExternalField geometry.externalEdgeEquiv)
      (senguptaCompactSurfaceGraphMeasure data.sourcePartitionFunction bundleClass region
        (senguptaTriangulatedRegionFactor baseTriangulation coverDensity)
        (senguptaTriangulatedTwistedRegionFactor baseTriangulation coverDensity)) =
    senguptaCompactSurfaceGraphMeasure data.targetPartitionFunction
      (senguptaTransportedBundleClass geometry.orientationSign bundleClass)
      (geometry.regionEquiv region)
      (senguptaTriangulatedRegionFactor target coverDensity)
      (senguptaTriangulatedTwistedRegionFactor target coverDensity) :=
  data.graphMeasure_pushforward region

omit [T2Space CoverGroup] [MeasurableMul₂ CoverGroup] [MeasurableInv CoverGroup]
    [Nonempty Curve] in
/-- Both sides remain probability measures for every distinguished-region choice. -/
theorem all_region_nonvacuity
    (data : TwoDimensionalSenguptaParameterizedCellwiseGraphMeasureTransportData
      (coverDensity := coverDensity) (bundleClass := bundleClass) (geometry := geometry))
    (region : Region) :
    senguptaCompactSurfaceGraphMeasure data.sourcePartitionFunction bundleClass region
        (senguptaTriangulatedRegionFactor baseTriangulation coverDensity)
        (senguptaTriangulatedTwistedRegionFactor baseTriangulation coverDensity) Set.univ = 1 ∧
    senguptaCompactSurfaceGraphMeasure data.targetPartitionFunction
        (senguptaTransportedBundleClass geometry.orientationSign bundleClass)
        (geometry.regionEquiv region)
        (senguptaTriangulatedRegionFactor target coverDensity)
        (senguptaTriangulatedTwistedRegionFactor target coverDensity) Set.univ = 1 :=
  ⟨data.sourceGraphMeasure_univ region, data.targetGraphMeasure_univ region⟩

end TwoDimensionalSenguptaParameterizedCellwiseGraphMeasureTransportData

end

end YangMills.Dimensions
