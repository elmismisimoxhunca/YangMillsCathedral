/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Dimensions.TwoDimensionalDriverAxialLatticeFaceGeometry

namespace YangMills.Dimensions.TwoDimensionalDriverAxialLatticeFaceGeometry.Probes

open Filter Set

noncomputable section

universe uG uGauge uSample uConnection
  uVertex uEdge uFace uXAxisCell uLargeVertex uLargeEdge uLargeFace uLargeXAxisCell
  uFineVertex uFineEdge uFineFace uFineXAxisCell
  uFineLargeVertex uFineLargeEdge uFineLargeFace uFineLargeXAxisCell

attribute [local instance]
  TwoDimensionalLatticeApproximatingSequenceData.fineEdgeDecidableEq

variable
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
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
    {data : TwoDimensionalDriverAxialLatticeFaceGeometryData
      (axial := axial) (coarseApproximation := coarseApproximation)
      (enlargedApproximation := enlargedApproximation)}

omit [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [BorelSpace G]
    [MeasurableMul₂ G] [MeasurableInv G] in
/-- Every fine face is its finite polyomino interior minus the exact graph trace. -/
theorem exact_polyomino_minus_trace
    (spacing : PositiveLatticeSpacing)
    (face : (enlargedApproximation.fine spacing).Face) :
    (enlargedApproximation.fine spacing).faceRegion face =
      interior (⋃ site ∈ data.facePlaquettes spacing face,
        epsilonSquareLatticeClosedPlaquetteRegion spacing site) \
        finiteEmbeddedGraphTrace (enlargedApproximation.fine spacing).Edge
          (enlargedApproximation.fine spacing).pathCurve
          (enlargedApproximation.fine spacing).edgePath :=
  data.faceRegion_eq_polyominoInterior_diff_trace spacing face

omit [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [BorelSpace G]
    [MeasurableMul₂ G] [MeasurableInv G] in
/-- In particular, an internal bridge/slit is not silently filled by the closed polyomino union. -/
theorem internal_trace_not_filled
    (data : TwoDimensionalDriverAxialLatticeFaceGeometryData
      (axial := axial) (coarseApproximation := coarseApproximation)
      (enlargedApproximation := enlargedApproximation))
    (spacing : PositiveLatticeSpacing)
    (face : (enlargedApproximation.fine spacing).Face)
    (point : EuclideanDimension.two.Spacetime)
    (inside : point ∈ (enlargedApproximation.fine spacing).faceRegion face) :
    point ∉ finiteEmbeddedGraphTrace (enlargedApproximation.fine spacing).Edge
      (enlargedApproximation.fine spacing).pathCurve
      (enlargedApproximation.fine spacing).edgePath := by
  rw [data.faceRegion_eq_polyominoInterior_diff_trace spacing face] at inside
  exact inside.2

omit [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [BorelSpace G]
    [MeasurableMul₂ G] [MeasurableInv G] in
/-- The source convolution exponent is exactly a positive natural number. -/
theorem exact_positive_convolution_exponent
    (spacing : PositiveLatticeSpacing)
    (face : (enlargedApproximation.fine spacing).Face) :
    0 < (data.facePlaquettes spacing face).card ∧
      (enlargedApproximation.fine spacing).faceArea face / spacing.1 ^ 2 =
        (data.facePlaquettes spacing face).card :=
  ⟨data.facePlaquetteCard_pos spacing face,
    data.faceArea_div_spacing_sq spacing face⟩

omit [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [BorelSpace G]
    [MeasurableMul₂ G] [MeasurableInv G] in
/-- Distinct continuum faces are eventually protected against a colliding fine label. -/
theorem distinct_face_collision_eventually_blocked
    (first second : enlarged.Face) (different : first ≠ second) :
    ∀ᶠ spacing in positiveLatticeSpacingAtZero,
      enlargedApproximation.faceMap spacing first ≠
        enlargedApproximation.faceMap spacing second :=
  twoDimensionalFaceMap_eventually_pairwise_ne first second different

omit [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [BorelSpace G]
    [MeasurableMul₂ G] [MeasurableInv G] in
/-- Product reindexing requires bijectivity only eventually, preserving collision-safe Definition 8.1. -/
theorem exact_eventual_face_bijection :
    ∀ᶠ spacing in positiveLatticeSpacingAtZero,
      Function.Bijective (enlargedApproximation.faceMap spacing) :=
  twoDimensionalFaceMap_eventually_bijective

omit [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [BorelSpace G]
    [MeasurableMul₂ G] [MeasurableInv G] in
/-- The uniform geometric estimate gives an exact first-order mapped-area bound. -/
theorem exact_mapped_area_bound
    (spacing : PositiveLatticeSpacing)
    (belowCutoff : spacing.1 < enlargedApproximation.areaOrderCutoff)
    (face : enlarged.Face) :
    |(enlargedApproximation.fine spacing).faceArea
        (enlargedApproximation.faceMap spacing face) - enlarged.faceArea face| ≤
      enlargedApproximation.areaOrderConstant * spacing.1 :=
  twoDimensionalMappedFaceArea_abs_sub_le spacing belowCutoff face

omit [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [BorelSpace G]
    [MeasurableMul₂ G] [MeasurableInv G] in
/-- Each mapped polyomino area tends to its exact continuum face area by derivation, not a field. -/
theorem exact_mapped_area_limit (face : enlarged.Face) :
    Tendsto
      (fun spacing => (enlargedApproximation.fine spacing).faceArea
        (enlargedApproximation.faceMap spacing face))
      positiveLatticeSpacingAtZero (nhds (enlarged.faceArea face)) :=
  twoDimensionalMappedFaceArea_tendsto face

omit [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [BorelSpace G]
    [MeasurableMul₂ G] [MeasurableInv G] in
/-- An empty proposed plaquette family is hostilely rejected for every fine face. -/
theorem empty_face_plaquettes_blocked
    (spacing : PositiveLatticeSpacing)
    (face : (enlargedApproximation.fine spacing).Face)
    (claimed : data.facePlaquettes spacing face = ∅) : False := by
  have nonempty := data.facePlaquettes_nonempty spacing face
  rw [claimed] at nonempty
  exact Finset.not_nonempty_empty nonempty

end

end YangMills.Dimensions.TwoDimensionalDriverAxialLatticeFaceGeometry.Probes
