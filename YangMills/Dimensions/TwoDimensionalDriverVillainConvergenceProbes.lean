/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Dimensions.TwoDimensionalDriverVillainConvergence

namespace YangMills.Dimensions.TwoDimensionalDriverVillainConvergence.Probes

open Filter MeasureTheory
open YangMills.Mathematics
open scoped Manifold ContDiff Topology

noncomputable section

universe uE uG uGauge uSample uConnection
  uVertex uEdge uFace uXAxisCell uLargeVertex uLargeEdge uLargeFace uLargeXAxisCell
  uFineVertex uFineEdge uFineFace uFineXAxisCell
  uFineLargeVertex uFineLargeEdge uFineLargeFace uFineLargeXAxisCell

attribute [local instance]
  TwoDimensionalLatticeApproximatingSequenceData.fineEdgeDecidableEq

variable
    {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [SecondCountableTopology G] [ChartedSpace E G]
    [LieGroup (modelWithCornersSelf ℝ E) ∞ G]
    [MeasurableSpace G] [BorelSpace G] [MeasurableMul₂ G] [MeasurableInv G]
    {Gauge : Type uGauge} [Group Gauge] {Sample : Type uSample} [MeasurableSpace Sample]
    {Connection : Type uConnection} {gaugeGroup : Geometry.CompactSimpleGaugeGroupData G E}
    {base : TwoDimensionalGaugeFixedHolonomyMeasureData G Gauge Sample Connection}
    {law : TwoDimensionalSelectedLoopHaarDensityLawData base}
    {semigroup : TwoDimensionalSelectedLoopConvolutionSemigroupData law}
    {coarse : TwoDimensionalEmbeddedPlanarGraphData.{uVertex, uEdge, uFace, uXAxisCell} base}
    {enlarged : TwoDimensionalEmbeddedPlanarGraphData.{uLargeVertex, uLargeEdge,
      uLargeFace, uLargeXAxisCell} base}
    [DecidableEq coarse.Edge] [DecidableEq enlarged.Edge]
    {common : TwoDimensionalVillainCommonHeatChainData (gaugeGroup := gaugeGroup) semigroup}
    {axial : TwoDimensionalDriverAxialEnlargementData
      (G := G) (coarse := coarse) (enlarged := enlarged)}
    {continuum : TwoDimensionalDriverAxialEnlargedHeatExpectationData (law := law) axial}
    {coarseApproximation : TwoDimensionalLatticeApproximatingHolonomyData.{uVertex, uEdge,
      uFace, uXAxisCell, uFineVertex, uFineEdge, uFineFace, uFineXAxisCell}
      (base := base) (coarse := coarse)}
    {enlargedApproximation : TwoDimensionalLatticeApproximatingHolonomyData.{uLargeVertex,
      uLargeEdge, uLargeFace, uLargeXAxisCell, uFineLargeVertex, uFineLargeEdge,
      uFineLargeFace, uFineLargeXAxisCell} (base := base) (coarse := enlarged)}
    {faceGeometry : TwoDimensionalDriverAxialLatticeFaceGeometryData
      (axial := axial) (coarseApproximation := coarseApproximation)
      (enlargedApproximation := enlargedApproximation)}
    {productIdentity : TwoDimensionalDriverAxialLatticeProductIdentityData faceGeometry
      (twoDimensionalVillainActionFamily common.heat common.kernel)}
    {data : TwoDimensionalDriverVillainConvergenceData common axial continuum
      coarseApproximation enlargedApproximation faceGeometry}

omit [IsTopologicalGroup G] [T2Space G] [MeasurableMul₂ G] [MeasurableInv G]
    [DecidableEq coarse.Edge] in
/-- Every continuous coarse function is covered explicitly by a measurable bounded test. -/
theorem exact_continuous_coverage
    (observable : (coarse.Edge → G) → ℝ) (continuous : Continuous observable) :
    ∃ test : BoundedContinuousRealFunction (coarse.Edge → G), test.toFun = observable :=
  ⟨BoundedContinuousRealFunction.ofContinuous observable continuous, rfl⟩

omit [MeasurableMul₂ G] [MeasurableInv G] in
/-- The only new analytic obligation is convergence of the exact finite selected-density integrals. -/
theorem exact_fine_heat_integral_limit
    (data : TwoDimensionalDriverVillainConvergenceData common axial continuum
      coarseApproximation enlargedApproximation faceGeometry)
    (test : BoundedContinuousRealFunction (coarse.Edge → G)) :
    Tendsto
      (fun spacing => ∫ configuration,
        test (twoDimensionalFineEnlargedCoarseRestriction faceGeometry spacing configuration)
          ∂twoDimensionalFineEnlargedActionMeasure faceGeometry
            (twoDimensionalVillainActionFamily common.heat common.kernel) spacing)
      positiveLatticeSpacingAtZero
      (nhds (∫ configuration, test (axial.coarseRestriction configuration)
        ∂generalBoundaryTreeFrozenFaceWeightMeasure
          (law := law) continuum.choice axial.tree)) :=
  data.fineHeatIntegral_tendsto test

/-- Driver Theorem 8.5 is recovered for every continuous coarse function. -/
theorem exact_every_continuous_villain_limit
    (continuum : TwoDimensionalDriverAxialEnlargedHeatExpectationData (law := law) axial)
    (data : TwoDimensionalDriverVillainConvergenceData common axial continuum
      coarseApproximation enlargedApproximation faceGeometry)
    (observable : (coarse.Edge → G) → ℝ) (continuous : Continuous observable) :
    Tendsto
      (fun spacing => ∫ configuration,
        observable (coarseApproximation.coarseRestriction spacing configuration)
          ∂(productIdentity.latticeLimit spacing).limitMeasure)
      positiveLatticeSpacingAtZero
      (nhds (∫ sample, observable (fun edge => base.holonomy (coarse.edgePath edge)
        (base.sampleConnection sample)) ∂base.probabilityMeasure)) :=
  TwoDimensionalDriverVillainConvergenceData.everyContinuous_latticeExpectation_tendsto_continuum
    common axial continuum coarseApproximation enlargedApproximation faceGeometry
      productIdentity data observable continuous

omit [MeasurableMul₂ G] [MeasurableInv G] in
/-- The heat chain is induced by the exact same representation differential and trace pairing. -/
theorem exact_common_trace_pairing
    (first second : GroupLieAlgebra (modelWithCornersSelf ℝ E) G) :
    common.inner.pairing first second =
      twoDimensionalRepresentationTracePairing common.representation first second :=
  TwoDimensionalVillainCommonHeatChainData.inner_pairing_eq_trace
    semigroup common first second

/-- Failure of one eligible continuous Villain limit is hostilely rejected. -/
theorem failed_villain_limit_blocked
    (continuum : TwoDimensionalDriverAxialEnlargedHeatExpectationData (law := law) axial)
    (data : TwoDimensionalDriverVillainConvergenceData common axial continuum
      coarseApproximation enlargedApproximation faceGeometry)
    (observable : (coarse.Edge → G) → ℝ) (continuous : Continuous observable)
    (failed : ¬ Tendsto
      (fun spacing => ∫ configuration,
        observable (coarseApproximation.coarseRestriction spacing configuration)
          ∂(productIdentity.latticeLimit spacing).limitMeasure)
      positiveLatticeSpacingAtZero
      (nhds (∫ sample, observable (fun edge => base.holonomy (coarse.edgePath edge)
        (base.sampleConnection sample)) ∂base.probabilityMeasure))) : False :=
  failed (exact_every_continuous_villain_limit continuum data observable continuous)

/-- This lower-dimensional convergence contract cannot inhabit the four-dimensional endpoint. -/
theorem villain_limit_not_four_dimensional :
    EuclideanDimension.two ≠ EuclideanDimension.four :=
  EuclideanDimension.two_ne_four

end

end YangMills.Dimensions.TwoDimensionalDriverVillainConvergence.Probes
