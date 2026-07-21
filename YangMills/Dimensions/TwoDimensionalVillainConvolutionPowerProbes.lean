/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Dimensions.TwoDimensionalVillainConvolutionPower

namespace YangMills.Dimensions.TwoDimensionalVillainConvolutionPower.Probes

open YangMills.Mathematics
open scoped Manifold ContDiff

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
    [MeasurableSpace G] [BorelSpace G]
    {Gauge : Type uGauge} [Group Gauge] {Sample : Type uSample} [MeasurableSpace Sample]
    {Connection : Type uConnection}
    {gaugeGroup : Geometry.CompactSimpleGaugeGroupData G E}
    {inner : Geometry.InvariantInnerProductData (I := modelWithCornersSelf ℝ E) (G := G)}
    {base : TwoDimensionalGaugeFixedHolonomyMeasureData G Gauge Sample Connection}
    {law : TwoDimensionalSelectedLoopHaarDensityLawData base}
    {semigroup : TwoDimensionalSelectedLoopConvolutionSemigroupData law}
    {laplacian : RightInvariantPairingLaplacianData inner}
    {heat : TwoDimensionalSelectedLoopHeatEquationData
      gaugeGroup inner law semigroup laplacian}
    {kernel : TwoDimensionalSelectedLoopHeatKernelOperatorData heat}
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

/-- Every positive number of Villain factors is derived from the same selected density semigroup. -/
theorem exact_villain_power
    (spacing : PositiveLatticeSpacing) (n : ℕ) (g : G) :
    twoDimensionalLatticeActionConvolutionPower
        (twoDimensionalVillainActionFamily heat kernel spacing) n g =
      law.selectedAreaDensity
        (((n + 1 : ℕ) : ℝ) * twoDimensionalVillainTime spacing) g :=
  twoDimensionalVillainConvolutionPower_eq_selectedDensity heat kernel spacing n g

/-- The exact polyomino count converts the face power to its geometric-area density. -/
theorem exact_villain_face_density
    (spacing : PositiveLatticeSpacing)
    (face : (enlargedApproximation.fine spacing).Face) (g : G) :
    twoDimensionalLatticeActionConvolutionPower
        (twoDimensionalVillainActionFamily heat kernel spacing)
        ((faceGeometry.facePlaquettes spacing face).card - 1) g =
      law.selectedAreaDensity ((enlargedApproximation.fine spacing).faceArea face) g :=
  twoDimensionalVillainFaceConvolutionPower_eq_selectedDensity
    heat kernel faceGeometry spacing face g

variable [MeasurableMul₂ G] [MeasurableInv G]

omit [MeasurableMul₂ G] [MeasurableInv G] in
/-- The full action density product is definitionally tied to the unchanged selected heat family. -/
theorem exact_villain_product
    (spacing : PositiveLatticeSpacing)
    (configuration : (enlargedApproximation.fine spacing).Edge → G) :
    twoDimensionalFineEnlargedActionDensityProduct faceGeometry
        (twoDimensionalVillainActionFamily heat kernel) spacing configuration =
      ∏ face : (enlargedApproximation.fine spacing).Face,
        law.selectedAreaDensity ((enlargedApproximation.fine spacing).faceArea face)
          (finiteOrientedWordHolonomy configuration
            ((faceGeometry.latticeEnlargement.fineBoundaryConnected spacing).boundaryWord face)) :=
  twoDimensionalVillainFineEnlargedActionDensityProduct_eq_selectedDensityProduct
    heat kernel faceGeometry spacing configuration

omit [MeasurableMul₂ G] [MeasurableInv G] in
/-- An unrelated proposed face density cannot replace the derived common heat density. -/
theorem unrelated_villain_face_density_blocked
    (spacing : PositiveLatticeSpacing)
    (face : (enlargedApproximation.fine spacing).Face) (g : G)
    (wrong : twoDimensionalLatticeActionConvolutionPower
        (twoDimensionalVillainActionFamily heat kernel spacing)
        ((faceGeometry.facePlaquettes spacing face).card - 1) g ≠
      law.selectedAreaDensity ((enlargedApproximation.fine spacing).faceArea face) g) : False :=
  wrong (twoDimensionalVillainFaceConvolutionPower_eq_selectedDensity
    heat kernel faceGeometry spacing face g)

end

end YangMills.Dimensions.TwoDimensionalVillainConvolutionPower.Probes
