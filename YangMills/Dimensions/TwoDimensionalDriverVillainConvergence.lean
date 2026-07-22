/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Dimensions.TwoDimensionalDriverAxialEnlargedHeatExpectation
import YangMills.Dimensions.TwoDimensionalVillainConvolutionPower
import YangMills.Dimensions.TwoDimensionalVillainCommonHeatChain

/-!
# Driver Theorem 8.5 Villain convergence contract

This module closes the source-facing dependency chain for Driver Theorem 8.5: the representation
with injective differential determines the invariant pairing and heat semigroup; the Villain action
is exactly `Q_{ε²}`; the finite lattice expectation is rewritten on compatible `VB(ε)`; and those
finite selected-density integrals converge to the exact `VB` heat integral. Equation (6.1) then
derives convergence to the original continuum expectation.

Only the final varying-finite-graph integral convergence is an analytic obligation. No graph family,
weak limit, continuum theory, or theorem inhabitant is constructed here.
-/

namespace YangMills.Dimensions

open Filter MeasureTheory
open YangMills.Mathematics
open scoped Manifold ContDiff Topology

noncomputable section

universe uE uG uGauge uSample uConnection
  uVertex uEdge uFace uXAxisCell
  uLargeVertex uLargeEdge uLargeFace uLargeXAxisCell
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
    {Connection : Type uConnection}
    {base : TwoDimensionalGaugeFixedHolonomyMeasureData G Gauge Sample Connection}
    {law : TwoDimensionalSelectedLoopHaarDensityLawData base}
    {semigroup : TwoDimensionalSelectedLoopConvolutionSemigroupData law}
    {coarse : TwoDimensionalEmbeddedPlanarGraphData.{uVertex, uEdge, uFace, uXAxisCell} base}
    {enlarged : TwoDimensionalEmbeddedPlanarGraphData.{uLargeVertex, uLargeEdge,
      uLargeFace, uLargeXAxisCell} base}
    [DecidableEq coarse.Edge] [DecidableEq enlarged.Edge]
    (common : TwoDimensionalVillainCommonHeatChainCoreData (E := E) semigroup)
    (axial : TwoDimensionalDriverAxialEnlargementData
      (G := G) (coarse := coarse) (enlarged := enlarged))
    (continuum : TwoDimensionalDriverAxialEnlargedHeatExpectationData (law := law) axial)
    (coarseApproximation : TwoDimensionalLatticeApproximatingHolonomyData.{uVertex, uEdge,
      uFace, uXAxisCell, uFineVertex, uFineEdge, uFineFace, uFineXAxisCell}
      (base := base) (coarse := coarse))
    (enlargedApproximation : TwoDimensionalLatticeApproximatingHolonomyData.{uLargeVertex,
      uLargeEdge, uLargeFace, uLargeXAxisCell, uFineLargeVertex, uFineLargeEdge,
      uFineLargeFace, uFineLargeXAxisCell} (base := base) (coarse := enlarged))
    (faceGeometry : TwoDimensionalDriverAxialLatticeFaceGeometryData
      (axial := axial) (coarseApproximation := coarseApproximation)
      (enlargedApproximation := enlargedApproximation))
    (productIdentity : TwoDimensionalDriverAxialLatticeProductIdentityData faceGeometry
      (twoDimensionalVillainActionFamily common.heat common.kernel))

/-- Uninhabited connected compact Lie-group contract for Driver Theorem 8.5. -/
structure TwoDimensionalDriverVillainConvergenceData where
  fineHeatIntegral_tendsto : ∀ test : BoundedContinuousRealFunction (coarse.Edge → G),
    Tendsto
      (fun spacing => ∫ configuration,
        test (twoDimensionalFineEnlargedCoarseRestriction faceGeometry spacing configuration)
          ∂twoDimensionalFineEnlargedActionMeasure faceGeometry
            (twoDimensionalVillainActionFamily common.heat common.kernel) spacing)
      positiveLatticeSpacingAtZero
      (nhds (∫ configuration, test (axial.coarseRestriction configuration)
        ∂generalBoundaryTreeFrozenFaceWeightMeasure
          (law := law) continuum.choice axial.tree))

namespace TwoDimensionalDriverVillainConvergenceData

/-- Theorem 8.5 first follows for every explicitly bounded continuous test by the exact finite
product identity. -/
theorem latticeExpectation_tendsto_enlargedHeat
    (data : TwoDimensionalDriverVillainConvergenceData
      common axial continuum coarseApproximation enlargedApproximation faceGeometry)
    (test : BoundedContinuousRealFunction (coarse.Edge → G)) :
    Tendsto
      (fun spacing => ∫ configuration,
        test (coarseApproximation.coarseRestriction spacing configuration)
          ∂(productIdentity.latticeLimit spacing).limitMeasure)
      positiveLatticeSpacingAtZero
      (nhds (∫ configuration, test (axial.coarseRestriction configuration)
        ∂generalBoundaryTreeFrozenFaceWeightMeasure
          (law := law) continuum.choice axial.tree)) := by
  have equality :
      (fun spacing => ∫ configuration,
        test (coarseApproximation.coarseRestriction spacing configuration)
          ∂(productIdentity.latticeLimit spacing).limitMeasure) =
      fun spacing => ∫ configuration,
        test (twoDimensionalFineEnlargedCoarseRestriction faceGeometry spacing configuration)
          ∂twoDimensionalFineEnlargedActionMeasure faceGeometry
            (twoDimensionalVillainActionFamily common.heat common.kernel) spacing := by
    funext spacing
    exact productIdentity.expectation_eq_fineEnlargedIntegral spacing test
      test.measurable_toFun ⟨test.bound, test.abs_le_bound⟩
  rw [equality]
  exact data.fineHeatIntegral_tendsto test

/-- Equation (6.1) identifies the same limit with the original continuum holonomy expectation. -/
theorem latticeExpectation_tendsto_continuum
    (data : TwoDimensionalDriverVillainConvergenceData
      common axial continuum coarseApproximation enlargedApproximation faceGeometry)
    (test : BoundedContinuousRealFunction (coarse.Edge → G)) :
    Tendsto
      (fun spacing => ∫ configuration,
        test (coarseApproximation.coarseRestriction spacing configuration)
          ∂(productIdentity.latticeLimit spacing).limitMeasure)
      positiveLatticeSpacingAtZero
      (nhds (∫ sample, test (fun edge => base.holonomy (coarse.edgePath edge)
        (base.sampleConnection sample)) ∂base.probabilityMeasure)) := by
  rw [continuum.expectation_eq_enlargedHeatIntegral test test.measurable_toFun
    ⟨test.bound, test.abs_le_bound⟩]
  exact TwoDimensionalDriverVillainConvergenceData.latticeExpectation_tendsto_enlargedHeat
    common axial continuum coarseApproximation enlargedApproximation faceGeometry
      productIdentity data test

/-- The source's universal continuous-function statement is recovered through explicit compact-test
coverage rather than silently assuming boundedness/measurability compatibility. -/
theorem everyContinuous_latticeExpectation_tendsto_continuum
    (data : TwoDimensionalDriverVillainConvergenceData
      common axial continuum coarseApproximation enlargedApproximation faceGeometry)
    (observable : (coarse.Edge → G) → ℝ) (continuous : Continuous observable) :
    Tendsto
      (fun spacing => ∫ configuration,
        observable (coarseApproximation.coarseRestriction spacing configuration)
          ∂(productIdentity.latticeLimit spacing).limitMeasure)
      positiveLatticeSpacingAtZero
      (nhds (∫ sample, observable (fun edge => base.holonomy (coarse.edgePath edge)
        (base.sampleConnection sample)) ∂base.probabilityMeasure)) := by
  let test : BoundedContinuousRealFunction (coarse.Edge → G) :=
    BoundedContinuousRealFunction.ofContinuous observable continuous
  change Tendsto
    (fun spacing => ∫ configuration,
      test (coarseApproximation.coarseRestriction spacing configuration)
        ∂(productIdentity.latticeLimit spacing).limitMeasure)
    positiveLatticeSpacingAtZero
    (nhds (∫ sample, test (fun edge => base.holonomy (coarse.edgePath edge)
      (base.sampleConnection sample)) ∂base.probabilityMeasure))
  exact TwoDimensionalDriverVillainConvergenceData.latticeExpectation_tendsto_continuum
    common axial continuum coarseApproximation enlargedApproximation faceGeometry
      productIdentity data test

end TwoDimensionalDriverVillainConvergenceData

end

end YangMills.Dimensions
