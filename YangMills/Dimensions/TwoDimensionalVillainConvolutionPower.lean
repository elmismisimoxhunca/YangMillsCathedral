/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Dimensions.TwoDimensionalDriverAxialLatticeProductIdentity
import YangMills.Dimensions.TwoDimensionalLatticeSpacingActionFamily

/-!
# Derived Villain convolution powers

Driver Definition 8.3 uses `Aᵋ = Q_{ε²}`. The unchanged convolution semigroup therefore derives,
rather than assumes, that `k` action factors equal `Q_{kε²}`. Combined with the exact plaquette
count of every `VB(ε)` face, its lattice action density is literally the selected heat density at the
fine geometric face area.
-/

namespace YangMills.Dimensions

open YangMills.Mathematics
open scoped Manifold ContDiff

noncomputable section

universe uE uG uGauge uSample uConnection
  uVertex uEdge uFace uXAxisCell
  uLargeVertex uLargeEdge uLargeFace uLargeXAxisCell
  uFineVertex uFineEdge uFineFace uFineXAxisCell
  uFineLargeVertex uFineLargeEdge uFineLargeFace uFineLargeXAxisCell

attribute [local instance]
  TwoDimensionalLatticeApproximatingSequenceData.fineEdgeDecidableEq

variable
    {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [SecondCountableTopology G] [ChartedSpace E G]
    [LieGroup (modelWithCornersSelf ℝ E) ∞ G]
    [MeasurableSpace G] [BorelSpace G]
    {Gauge : Type uGauge} [Group Gauge]
    {Sample : Type uSample} [MeasurableSpace Sample]
    {Connection : Type uConnection}
    {inner : Geometry.InvariantInnerProductData
      (I := modelWithCornersSelf ℝ E) (G := G)}
    {base : TwoDimensionalGaugeFixedHolonomyMeasureData G Gauge Sample Connection}
    {law : TwoDimensionalSelectedLoopHaarDensityLawData base}
    {semigroup : TwoDimensionalSelectedLoopConvolutionSemigroupData law}
    {laplacian : RightInvariantPairingLaplacianData inner}
    (heat : TwoDimensionalSelectedLoopHeatEquationCoreData
      inner law semigroup laplacian)
    (kernel : TwoDimensionalSelectedLoopHeatKernelOperatorData heat)

/-- `n+1` Villain factors are exactly the unchanged density at time `(n+1)ε²`. -/
theorem twoDimensionalVillainConvolutionPower_eq_selectedDensity
    (spacing : PositiveLatticeSpacing) (n : ℕ) (g : G) :
    twoDimensionalLatticeActionConvolutionPower
        (twoDimensionalVillainActionFamily heat kernel spacing) n g =
      law.selectedAreaDensity
        (((n + 1 : ℕ) : ℝ) * twoDimensionalVillainTime spacing) g := by
  induction n generalizing g with
  | zero =>
      change ENNReal.ofReal (twoDimensionalVillainAction heat kernel spacing g) = _
      simpa using TwoDimensionalVillainAction.action_toENNReal heat kernel spacing g
  | succ n inductionHypothesis =>
      rw [twoDimensionalLatticeActionConvolutionPower]
      have previousTimePos :
          0 < (((n + 1 : ℕ) : ℝ) * twoDimensionalVillainTime spacing) :=
        mul_pos (by positivity) (TwoDimensionalVillainAction.time_pos spacing)
      have oneTimePos : 0 < twoDimensionalVillainTime spacing :=
        TwoDimensionalVillainAction.time_pos spacing
      calc
        normalizedCompactHaarDensityConvolution G
            (twoDimensionalLatticeActionConvolutionPower
              (twoDimensionalVillainActionFamily heat kernel spacing) n)
            (twoDimensionalLatticeActionENNRealDensity
              (twoDimensionalVillainActionFamily heat kernel spacing)) g =
          normalizedCompactHaarDensityConvolution G
            (law.selectedAreaDensity
              (((n + 1 : ℕ) : ℝ) * twoDimensionalVillainTime spacing))
            (law.selectedAreaDensity (twoDimensionalVillainTime spacing)) g := by
              congr 2
              · funext x
                exact inductionHypothesis x
              · funext x
                exact TwoDimensionalVillainAction.action_toENNReal heat kernel spacing x
        _ = law.selectedAreaDensity
            ((((n + 1 : ℕ) : ℝ) * twoDimensionalVillainTime spacing) +
              twoDimensionalVillainTime spacing) g :=
          (semigroup.density_add _ _ previousTimePos oneTimePos g).symm
        _ = law.selectedAreaDensity
            (((n + 2 : ℕ) : ℝ) * twoDimensionalVillainTime spacing) g := by
          congr 2
          push_cast
          ring

variable
    [MeasurableMul₂ G] [MeasurableInv G]
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

omit [MeasurableMul₂ G] [MeasurableInv G] in
/-- The convolution power selected by one exact fine face is its unchanged density at that face's
geometric area. -/
theorem twoDimensionalVillainFaceConvolutionPower_eq_selectedDensity
    (spacing : PositiveLatticeSpacing)
    (face : (enlargedApproximation.fine spacing).Face) (g : G) :
    twoDimensionalLatticeActionConvolutionPower
        (twoDimensionalVillainActionFamily heat kernel spacing)
        ((faceGeometry.facePlaquettes spacing face).card - 1) g =
      law.selectedAreaDensity
        ((enlargedApproximation.fine spacing).faceArea face) g := by
  rw [twoDimensionalVillainConvolutionPower_eq_selectedDensity heat kernel]
  congr 2
  rw [faceGeometry.faceArea_eq_card_mul_spacing_sq spacing face,
    twoDimensionalVillainTime]
  rw [TwoDimensionalDriverAxialLatticeProductIdentityData.convolutionFactorCount
    faceGeometry spacing face]

omit [MeasurableMul₂ G] [MeasurableInv G] in
/-- Hence the entire Villain `VB(ε)` face product is literally the product of unchanged selected
heat densities at exact fine geometric areas. -/
theorem twoDimensionalVillainFineEnlargedActionDensityProduct_eq_selectedDensityProduct
    (spacing : PositiveLatticeSpacing)
    (configuration : (enlargedApproximation.fine spacing).Edge → G) :
    twoDimensionalFineEnlargedActionDensityProduct faceGeometry
        (twoDimensionalVillainActionFamily heat kernel) spacing configuration =
      ∏ face : (enlargedApproximation.fine spacing).Face,
        law.selectedAreaDensity ((enlargedApproximation.fine spacing).faceArea face)
          (finiteOrientedWordHolonomy configuration
            ((faceGeometry.latticeEnlargement.fineBoundaryConnected spacing).boundaryWord face)) := by
  apply Finset.prod_congr rfl
  intro face _
  exact twoDimensionalVillainFaceConvolutionPower_eq_selectedDensity
    heat kernel faceGeometry spacing face _

end

end YangMills.Dimensions
