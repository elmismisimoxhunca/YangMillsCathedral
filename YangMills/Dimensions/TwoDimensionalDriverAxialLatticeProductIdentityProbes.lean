/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Dimensions.TwoDimensionalDriverAxialLatticeProductIdentity

namespace YangMills.Dimensions.TwoDimensionalDriverAxialLatticeProductIdentity.Probes

open MeasureTheory Set
open YangMills.Mathematics

noncomputable section

universe uG uGauge uSample uConnection
  uVertex uEdge uFace uXAxisCell uLargeVertex uLargeEdge uLargeFace uLargeXAxisCell
  uFineVertex uFineEdge uFineFace uFineXAxisCell
  uFineLargeVertex uFineLargeEdge uFineLargeFace uFineLargeXAxisCell

attribute [local instance]
  TwoDimensionalLatticeApproximatingSequenceData.fineEdgeDecidableEq

variable
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    [MeasurableMul₂ G] [MeasurableInv G]
    {Gauge : Type uGauge} [Group Gauge] {Sample : Type uSample} [MeasurableSpace Sample]
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
    {faceGeometry : TwoDimensionalDriverAxialLatticeFaceGeometryData
      (axial := axial) (coarseApproximation := coarseApproximation)
      (enlargedApproximation := enlargedApproximation)}
    {actionAt : PositiveLatticeSpacing → TwoDimensionalLatticeActionData G}

omit [T2Space G] [MeasurableMul₂ G] [MeasurableInv G] in
/-- The zero recursion index means exactly one action factor, never an identity-function surrogate. -/
theorem exact_one_factor (spacing : PositiveLatticeSpacing) (g : G) :
    twoDimensionalLatticeActionConvolutionPower (actionAt spacing) 0 g =
      ENNReal.ofReal ((actionAt spacing).action g) :=
  rfl

omit [T2Space G] [MeasurableMul₂ G] [MeasurableInv G] in
/-- The successor recursion uses Driver's fixed normalized-Haar `x⁻¹z` convolution orientation. -/
theorem exact_successor_orientation (spacing : PositiveLatticeSpacing) (n : ℕ) (g : G) :
    twoDimensionalLatticeActionConvolutionPower (actionAt spacing) (n + 1) g =
      normalizedCompactHaarDensityConvolution G
        (twoDimensionalLatticeActionConvolutionPower (actionAt spacing) n)
        (twoDimensionalLatticeActionENNRealDensity (actionAt spacing)) g :=
  rfl

omit [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [BorelSpace G] [MeasurableMul₂ G] [MeasurableInv G] in
/-- Each fine face uses exactly its positive plaquette count as the number of factors. -/
theorem exact_face_factor_count
    (spacing : PositiveLatticeSpacing)
    (face : (enlargedApproximation.fine spacing).Face) :
    ((faceGeometry.facePlaquettes spacing face).card - 1) + 1 =
      (faceGeometry.facePlaquettes spacing face).card :=
  TwoDimensionalDriverAxialLatticeProductIdentityData.convolutionFactorCount
    faceGeometry spacing face

omit [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [BorelSpace G] [MeasurableMul₂ G] [MeasurableInv G] in
/-- Fine restriction is literally the `B(ε) → VB(ε)` configuration map evaluated on the exact
`B → B(ε)` edge image. -/
theorem exact_fine_coarse_restriction
    (spacing : PositiveLatticeSpacing)
    (configuration : (enlargedApproximation.fine spacing).Edge → G)
    (edge : coarse.Edge) :
    twoDimensionalFineEnlargedCoarseRestriction faceGeometry spacing configuration edge =
      (faceGeometry.latticeEnlargement.fineRefinement spacing).combinatorial.configurationMap
        configuration (coarseApproximation.edgeMap spacing edge) :=
  rfl

omit [T2Space G] [MeasurableMul₂ G] [MeasurableInv G] in
/-- The face density uses the certified fine BC word, not an unrelated loop. -/
theorem exact_fine_boundary_density
    (spacing : PositiveLatticeSpacing)
    (configuration : (enlargedApproximation.fine spacing).Edge → G) :
    twoDimensionalFineEnlargedActionDensityProduct faceGeometry actionAt spacing configuration =
      ∏ face : (enlargedApproximation.fine spacing).Face,
        twoDimensionalLatticeActionConvolutionPower (actionAt spacing)
          ((faceGeometry.facePlaquettes spacing face).card - 1)
          (finiteOrientedWordHolonomy configuration
            ((faceGeometry.latticeEnlargement.fineBoundaryConnected spacing).boundaryWord face)) :=
  rfl

omit [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [BorelSpace G] [MeasurableMul₂ G] [MeasurableInv G] in
/-- Replacing the exact coarse restriction is hostilely rejected. -/
theorem changed_fine_restriction_blocked
    (spacing : PositiveLatticeSpacing)
    (configuration : (enlargedApproximation.fine spacing).Edge → G)
    (edge : coarse.Edge)
    (changed : twoDimensionalFineEnlargedCoarseRestriction faceGeometry spacing configuration edge ≠
      (faceGeometry.latticeEnlargement.fineRefinement spacing).combinatorial.configurationMap
        configuration (coarseApproximation.edgeMap spacing edge)) : False :=
  changed rfl

omit [T2Space G] [MeasurableMul₂ G] [MeasurableInv G] in
/-- Replacing the certified BC boundary word in the density is hostilely rejected. -/
theorem changed_fine_boundary_density_blocked
    (spacing : PositiveLatticeSpacing)
    (configuration : (enlargedApproximation.fine spacing).Edge → G)
    (changed : twoDimensionalFineEnlargedActionDensityProduct
      faceGeometry actionAt spacing configuration ≠
      ∏ face : (enlargedApproximation.fine spacing).Face,
        twoDimensionalLatticeActionConvolutionPower (actionAt spacing)
          ((faceGeometry.facePlaquettes spacing face).card - 1)
          (finiteOrientedWordHolonomy configuration
            ((faceGeometry.latticeEnlargement.fineBoundaryConnected spacing).boundaryWord face))) :
    False :=
  changed rfl

omit [T2Space G] [MeasurableMul₂ G] [MeasurableInv G] in
/-- The `VB(ε)` measure is literally a density over the exact tree-frozen product Haar carrier. -/
theorem exact_fine_measure (spacing : PositiveLatticeSpacing) :
    twoDimensionalFineEnlargedActionMeasure faceGeometry actionAt spacing =
      (finiteTreeFrozenProductMeasure (enlargedApproximation.fine spacing).Edge G
        (faceGeometry.latticeEnlargement.fineTree spacing)).withDensity
          (twoDimensionalFineEnlargedActionDensityProduct faceGeometry actionAt spacing) :=
  rfl

/-- Driver's finite-graph identity covers every bounded measurable coarse real observable. -/
theorem exact_arbitrary_observable_identity
    (data : TwoDimensionalDriverAxialLatticeProductIdentityData faceGeometry actionAt)
    (spacing : PositiveLatticeSpacing)
    (observable : (coarse.Edge → G) → ℝ)
    (hm : Measurable observable)
    (hb : ∃ bound : ℝ, ∀ configuration, |observable configuration| ≤ bound) :
    (∫ configuration,
      observable (coarseApproximation.coarseRestriction spacing configuration)
        ∂(data.latticeLimit spacing).limitMeasure) =
      ∫ configuration,
        observable (twoDimensionalFineEnlargedCoarseRestriction faceGeometry spacing configuration)
          ∂twoDimensionalFineEnlargedActionMeasure faceGeometry actionAt spacing :=
  data.expectation_eq_fineEnlargedIntegral spacing observable hm hb

/-- The weighted fine carrier is normalized and nonzero. -/
theorem exact_normalized_nonzero
    (data : TwoDimensionalDriverAxialLatticeProductIdentityData faceGeometry actionAt)
    (spacing : PositiveLatticeSpacing) :
    twoDimensionalFineEnlargedActionMeasure faceGeometry actionAt spacing univ = 1 ∧
      twoDimensionalFineEnlargedActionMeasure faceGeometry actionAt spacing ≠ 0 :=
  ⟨data.fineMeasure_normalized spacing,
    TwoDimensionalDriverAxialLatticeProductIdentityData.fineMeasure_ne_zero
      faceGeometry actionAt data spacing⟩

/-- One failed eligible identity is hostilely rejected. -/
theorem wrong_product_identity_blocked
    (data : TwoDimensionalDriverAxialLatticeProductIdentityData faceGeometry actionAt)
    (spacing : PositiveLatticeSpacing)
    (observable : (coarse.Edge → G) → ℝ)
    (hm : Measurable observable)
    (hb : ∃ bound : ℝ, ∀ configuration, |observable configuration| ≤ bound)
    (failed : (∫ configuration,
      observable (coarseApproximation.coarseRestriction spacing configuration)
        ∂(data.latticeLimit spacing).limitMeasure) ≠
      ∫ configuration,
        observable (twoDimensionalFineEnlargedCoarseRestriction faceGeometry spacing configuration)
          ∂twoDimensionalFineEnlargedActionMeasure faceGeometry actionAt spacing) : False :=
  failed (data.expectation_eq_fineEnlargedIntegral spacing observable hm hb)

end

end YangMills.Dimensions.TwoDimensionalDriverAxialLatticeProductIdentity.Probes
