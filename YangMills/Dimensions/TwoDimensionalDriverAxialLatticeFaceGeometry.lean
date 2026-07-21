/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Dimensions.TwoDimensionalDriverAxialLatticeEnlargement
import YangMills.Dimensions.TwoDimensionalLatticeSpacingActionFamily

/-!
# Plaquette geometry of Driver's enlarged lattice faces

In the proof of Theorems 8.5 and 8.10, every bounded face of `VB(ε)` is a finite polyomino, so
`|R(ε)| / ε²` is a positive integer and indexes a convolution power. The proof then reindexes the
fine-face product by continuum faces for sufficiently small `ε`. This module records those exact
geometric obligations. It constructs no graph, action, measure, or limit.
-/

namespace YangMills.Dimensions

open Filter Set

noncomputable section

universe uG uGauge uSample uConnection
  uVertex uEdge uFace uXAxisCell
  uLargeVertex uLargeEdge uLargeFace uLargeXAxisCell
  uFineVertex uFineEdge uFineFace uFineXAxisCell
  uFineLargeVertex uFineLargeEdge uFineLargeFace uFineLargeXAxisCell

attribute [local instance]
  TwoDimensionalLatticeApproximatingSequenceData.fineEdgeDecidableEq

/-- Closed elementary square with lower-left lattice site `(m,n)` at spacing `ε`. -/
def epsilonSquareLatticeClosedPlaquetteRegion
    (spacing : PositiveLatticeSpacing) (site : ℤ × ℤ) :
    Set EuclideanDimension.two.Spacetime :=
  {point |
    (site.1 : ℝ) * spacing.1 ≤ twoDimensionalFirstCoordinate point ∧
      twoDimensionalFirstCoordinate point ≤ ((site.1 + 1 : ℤ) : ℝ) * spacing.1 ∧
      (site.2 : ℝ) * spacing.1 ≤ twoDimensionalSecondCoordinate point ∧
      twoDimensionalSecondCoordinate point ≤ ((site.2 + 1 : ℤ) : ℝ) * spacing.1}

variable
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
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

/-- Exact finite-square decomposition and eventual face correspondence used in Driver §8. -/
structure TwoDimensionalDriverAxialLatticeFaceGeometryData where
  latticeEnlargement : TwoDimensionalDriverAxialLatticeEnlargementData
    axial coarseApproximation enlargedApproximation
  facePlaquettes : ∀ spacing,
    (enlargedApproximation.fine spacing).Face → Finset (ℤ × ℤ)
  facePlaquettes_nonempty : ∀ spacing face,
    (facePlaquettes spacing face).Nonempty
  /-- The open complementary face is its finite closed polyomino interior with the entire fine graph
  trace removed. The subtraction retains Driver-permitted internal bridge/slit edges. -/
  faceRegion_eq_polyominoInterior_diff_trace : ∀ spacing face,
    (enlargedApproximation.fine spacing).faceRegion face =
      interior (⋃ site ∈ facePlaquettes spacing face,
        epsilonSquareLatticeClosedPlaquetteRegion spacing site) \
        finiteEmbeddedGraphTrace (enlargedApproximation.fine spacing).Edge
          (enlargedApproximation.fine spacing).pathCurve
          (enlargedApproximation.fine spacing).edgePath
  /-- Consequently the exact convolution exponent is the positive integer number of plaquettes. -/
  faceArea_eq_card_mul_spacing_sq : ∀ spacing face,
    (enlargedApproximation.fine spacing).faceArea face =
      ((facePlaquettes spacing face).card : ℝ) * spacing.1 ^ 2
  /-- Driver's product reindexing is only required eventually; no false equality is imposed when
  coarse faces collide at larger lattice spacing. -/
  faceMap_eventually_bijective :
    ∀ᶠ spacing in positiveLatticeSpacingAtZero,
      Function.Bijective (enlargedApproximation.faceMap spacing)
  mappedFaceArea_tendsto : ∀ face : enlarged.Face,
    Tendsto
      (fun spacing => (enlargedApproximation.fine spacing).faceArea
        (enlargedApproximation.faceMap spacing face))
      positiveLatticeSpacingAtZero
      (nhds (enlarged.faceArea face))

namespace TwoDimensionalDriverAxialLatticeFaceGeometryData

omit [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [BorelSpace G]
    [MeasurableMul₂ G] [MeasurableInv G] in
/-- Every convolution exponent is genuinely positive. -/
theorem facePlaquetteCard_pos
    (data : TwoDimensionalDriverAxialLatticeFaceGeometryData
      (axial := axial) (coarseApproximation := coarseApproximation)
      (enlargedApproximation := enlargedApproximation))
    (spacing : PositiveLatticeSpacing)
    (face : (enlargedApproximation.fine spacing).Face) :
    0 < (data.facePlaquettes spacing face).card :=
  Finset.card_pos.mpr (data.facePlaquettes_nonempty spacing face)

omit [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [BorelSpace G]
    [MeasurableMul₂ G] [MeasurableInv G] in
/-- The source exponent `|R(ε)| / ε²` is exactly the stored positive natural number. -/
theorem faceArea_div_spacing_sq
    (data : TwoDimensionalDriverAxialLatticeFaceGeometryData
      (axial := axial) (coarseApproximation := coarseApproximation)
      (enlargedApproximation := enlargedApproximation))
    (spacing : PositiveLatticeSpacing)
    (face : (enlargedApproximation.fine spacing).Face) :
    (enlargedApproximation.fine spacing).faceArea face / spacing.1 ^ 2 =
      (data.facePlaquettes spacing face).card := by
  rw [data.faceArea_eq_card_mul_spacing_sq spacing face]
  field_simp [ne_of_gt spacing.property]

end TwoDimensionalDriverAxialLatticeFaceGeometryData

end

end YangMills.Dimensions
