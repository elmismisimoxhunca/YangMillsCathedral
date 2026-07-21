/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Dimensions.TwoDimensionalDriverAxialLatticeFaceGeometry
import YangMills.Dimensions.TwoDimensionalDriverAxialWeakLimit

/-!
# Driver's enlarged finite-graph lattice product identity

The first displayed equality in the proofs of Driver Theorems 8.5 and 8.10 rewrites the infinite
axial lattice expectation as an integral on `VB(ε)`. Every face contributes the convolution power
of the one-plaquette action indexed by its exact positive plaquette count, while `T(ε)` coordinates
are frozen to the identity. This module records that measure-level bridge for every bounded
measurable coarse observable.

It assumes the identity and constructs no infinite-volume law, convergence theorem, or Yang--Mills
theory.
-/

namespace YangMills.Dimensions

open MeasureTheory Set
open YangMills.Mathematics

noncomputable section

universe uG uGauge uSample uConnection
  uVertex uEdge uFace uXAxisCell
  uLargeVertex uLargeEdge uLargeFace uLargeXAxisCell
  uFineVertex uFineEdge uFineFace uFineXAxisCell
  uFineLargeVertex uFineLargeEdge uFineLargeFace uFineLargeXAxisCell

attribute [local instance]
  TwoDimensionalLatticeApproximatingSequenceData.fineEdgeDecidableEq

/-- Convert one strictly positive real lattice action to its exact `ENNReal` density. -/
def twoDimensionalLatticeActionENNRealDensity
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (action : TwoDimensionalLatticeActionData G) : G → ENNReal :=
  fun g => ENNReal.ofReal (action.action g)

/-- `n+1` normalized-Haar convolution factors in Driver's fixed `x⁻¹z` orientation. -/
def twoDimensionalLatticeActionConvolutionPower
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (action : TwoDimensionalLatticeActionData G) : ℕ → G → ENNReal
  | 0 => twoDimensionalLatticeActionENNRealDensity action
  | n + 1 => normalizedCompactHaarDensityConvolution G
      (twoDimensionalLatticeActionConvolutionPower action n)
      (twoDimensionalLatticeActionENNRealDensity action)

/-- The positive real action gives a measurable `ENNReal` density. -/
theorem twoDimensionalLatticeActionENNRealDensity_measurable
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (action : TwoDimensionalLatticeActionData G) :
    Measurable (twoDimensionalLatticeActionENNRealDensity action) :=
  ENNReal.measurable_ofReal.comp action.action_continuous.measurable

/-- Every finite normalized-Haar convolution power of one lattice action is measurable. -/
theorem twoDimensionalLatticeActionConvolutionPower_measurable
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    [MeasurableMul₂ G] [MeasurableInv G]
    (action : TwoDimensionalLatticeActionData G) (n : ℕ) :
    Measurable (twoDimensionalLatticeActionConvolutionPower action n) := by
  letI : IsProbabilityMeasure (normalizedCompactHaarMeasure G) :=
    normalizedCompactHaarMeasure_isProbability G
  induction n with
  | zero => exact twoDimensionalLatticeActionENNRealDensity_measurable action
  | succ n inductionHypothesis =>
      rw [twoDimensionalLatticeActionConvolutionPower]
      unfold normalizedCompactHaarDensityConvolution
      apply Measurable.lintegral_prod_right
      exact (inductionHypothesis.comp measurable_snd).mul
        ((twoDimensionalLatticeActionENNRealDensity_measurable action).comp
          (measurable_snd.inv.mul measurable_fst))

variable
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    [MeasurableMul₂ G] [MeasurableInv G]
    {Gauge : Type uGauge} [Group Gauge]
    {Sample : Type uSample} [MeasurableSpace Sample]
    {Connection : Type uConnection}
    {base : TwoDimensionalGaugeFixedHolonomyMeasureData G Gauge Sample Connection}
    {coarse : TwoDimensionalEmbeddedPlanarGraphData.{uVertex, uEdge, uFace, uXAxisCell} base}
    {enlarged : TwoDimensionalEmbeddedPlanarGraphData.{uLargeVertex, uLargeEdge,
      uLargeFace, uLargeXAxisCell} base}
    [DecidableEq coarse.Edge] [DecidableEq enlarged.Edge]
    {axial : TwoDimensionalDriverAxialEnlargementData
      (G := G) (coarse := coarse) (enlarged := enlarged)}
    {coarseApproximation : TwoDimensionalLatticeApproximatingHolonomyData.{uVertex, uEdge,
      uFace, uXAxisCell, uFineVertex, uFineEdge, uFineFace, uFineXAxisCell}
      (base := base) (coarse := coarse)}
    {enlargedApproximation : TwoDimensionalLatticeApproximatingHolonomyData.{uLargeVertex,
      uLargeEdge, uLargeFace, uLargeXAxisCell, uFineLargeVertex, uFineLargeEdge,
      uFineLargeFace, uFineLargeXAxisCell} (base := base) (coarse := enlarged)}
    (faceGeometry : TwoDimensionalDriverAxialLatticeFaceGeometryData
      (axial := axial) (coarseApproximation := coarseApproximation)
      (enlargedApproximation := enlargedApproximation))
    (actionAt : PositiveLatticeSpacing → TwoDimensionalLatticeActionData G)

/-- Exact restriction `Ω(VB(ε)) → Ω(B)` through `B(ε) → VB(ε)` and `B → B(ε)`. -/
def twoDimensionalFineEnlargedCoarseRestriction
    (spacing : PositiveLatticeSpacing) :
    ((enlargedApproximation.fine spacing).Edge → G) → (coarse.Edge → G) :=
  fun configuration edge =>
    (faceGeometry.latticeEnlargement.fineRefinement spacing).combinatorial.configurationMap
      configuration (coarseApproximation.edgeMap spacing edge)

/-- Product over fine enlarged faces of the exact positive convolution powers. -/
def twoDimensionalFineEnlargedActionDensityProduct
    (spacing : PositiveLatticeSpacing)
    (configuration : (enlargedApproximation.fine spacing).Edge → G) : ENNReal :=
  ∏ face : (enlargedApproximation.fine spacing).Face,
    twoDimensionalLatticeActionConvolutionPower (actionAt spacing)
      ((faceGeometry.facePlaquettes spacing face).card - 1)
      (finiteOrientedWordHolonomy configuration
        ((faceGeometry.latticeEnlargement.fineBoundaryConnected spacing).boundaryWord face))

omit [T2Space G] in
/-- The exact fine-face action product is measurable, derived from action continuity, measurable
normalized-Haar convolution, and finite-word holonomy. -/
theorem twoDimensionalFineEnlargedActionDensityProduct_measurable
    (spacing : PositiveLatticeSpacing) :
    Measurable (twoDimensionalFineEnlargedActionDensityProduct faceGeometry actionAt spacing) := by
  apply Finset.measurable_fun_prod
  intro face _
  exact (twoDimensionalLatticeActionConvolutionPower_measurable
    (actionAt spacing) ((faceGeometry.facePlaquettes spacing face).card - 1)).comp
      (finiteOrientedWordHolonomy_measurable
        ((faceGeometry.latticeEnlargement.fineBoundaryConnected spacing).boundaryWord face))

/-- Driver's exact `VB(ε)` carrier: tree-frozen product Haar weighted by action convolution powers. -/
def twoDimensionalFineEnlargedActionMeasure
    (spacing : PositiveLatticeSpacing) :
    Measure ((enlargedApproximation.fine spacing).Edge → G) :=
  (finiteTreeFrozenProductMeasure (enlargedApproximation.fine spacing).Edge G
    (faceGeometry.latticeEnlargement.fineTree spacing)).withDensity
      (twoDimensionalFineEnlargedActionDensityProduct faceGeometry actionAt spacing)

/-- Source-facing first product identity in Driver's Theorems 8.5/8.10 proofs. -/
structure TwoDimensionalDriverAxialLatticeProductIdentityData where
  latticeLimit : ∀ spacing,
    TwoDimensionalDriverAxialWeakLimitData spacing (actionAt spacing)
  expectation_eq_fineEnlargedIntegral : ∀ spacing
      (observable : (coarse.Edge → G) → ℝ),
    Measurable observable →
    (∃ bound : ℝ, ∀ configuration, |observable configuration| ≤ bound) →
    (∫ configuration,
      observable (coarseApproximation.coarseRestriction spacing configuration)
        ∂(latticeLimit spacing).limitMeasure) =
      ∫ configuration,
        observable (twoDimensionalFineEnlargedCoarseRestriction faceGeometry spacing configuration)
          ∂twoDimensionalFineEnlargedActionMeasure faceGeometry actionAt spacing

namespace TwoDimensionalDriverAxialLatticeProductIdentityData

/-- The universal identity at the constant-one observable derives normalization of the exact fine
carrier from normalization of the same action-indexed Theorem 7.2 law. -/
theorem fineMeasure_univ
    (data : TwoDimensionalDriverAxialLatticeProductIdentityData faceGeometry actionAt)
    (spacing : PositiveLatticeSpacing) :
    twoDimensionalFineEnlargedActionMeasure faceGeometry actionAt spacing univ = 1 := by
  have formula := data.expectation_eq_fineEnlargedIntegral spacing
    (fun _ : coarse.Edge → G => (1 : ℝ)) measurable_const
    ⟨1, fun _ => by norm_num⟩
  have latticeIntegral :
      (∫ _ : EpsilonSquareLatticeAxialConfiguration G spacing, (1 : ℝ)
        ∂(data.latticeLimit spacing).limitMeasure) = 1 := by
    rw [integral_const, Measure.real_def, (data.latticeLimit spacing).limit_normalized]
    norm_num
  have fineIntegral :
      (∫ _ : (enlargedApproximation.fine spacing).Edge → G, (1 : ℝ)
        ∂twoDimensionalFineEnlargedActionMeasure faceGeometry actionAt spacing) = 1 := by
    rw [← formula]
    exact latticeIntegral
  rw [integral_const] at fineIntegral
  have toReal_eq_one :
      (twoDimensionalFineEnlargedActionMeasure faceGeometry actionAt spacing univ).toReal = 1 := by
    simpa [Measure.real_def] using fineIntegral
  exact (ENNReal.toReal_eq_one_iff _).mp toReal_eq_one

/-- Every exact enlarged action carrier is nonzero by derived normalization. -/
theorem fineMeasure_ne_zero
    (data : TwoDimensionalDriverAxialLatticeProductIdentityData faceGeometry actionAt)
    (spacing : PositiveLatticeSpacing) :
    twoDimensionalFineEnlargedActionMeasure faceGeometry actionAt spacing ≠ 0 := by
  intro zeroMeasure
  have normalized := TwoDimensionalDriverAxialLatticeProductIdentityData.fineMeasure_univ
    faceGeometry actionAt data spacing
  rw [zeroMeasure] at normalized
  simp at normalized

omit [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [BorelSpace G] [MeasurableMul₂ G] [MeasurableInv G] in
/-- The selected exponent has exactly the source's positive number of convolution factors. -/
theorem convolutionFactorCount
    (spacing : PositiveLatticeSpacing)
    (face : (enlargedApproximation.fine spacing).Face) :
    ((faceGeometry.facePlaquettes spacing face).card - 1) + 1 =
      (faceGeometry.facePlaquettes spacing face).card := by
  have positive := faceGeometry.facePlaquetteCard_pos spacing face
  omega

end TwoDimensionalDriverAxialLatticeProductIdentityData

end

end YangMills.Dimensions
