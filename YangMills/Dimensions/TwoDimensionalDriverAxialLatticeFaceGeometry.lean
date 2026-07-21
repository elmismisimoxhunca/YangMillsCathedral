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

open Filter Set MeasureTheory

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

omit [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [BorelSpace G]
    [MeasurableMul₂ G] [MeasurableInv G] in
/-- The Definition 8.1 symmetric-difference estimate already bounds the absolute difference between
mapped fine-face area and continuum face area. This is derived rather than stored in later data. -/
theorem twoDimensionalMappedFaceArea_abs_sub_le
    (spacing : PositiveLatticeSpacing)
    (belowCutoff : spacing.1 < enlargedApproximation.areaOrderCutoff)
    (face : enlarged.Face) :
    |(enlargedApproximation.fine spacing).faceArea
        (enlargedApproximation.faceMap spacing face) - enlarged.faceArea face| ≤
      enlargedApproximation.areaOrderConstant * spacing.1 := by
  let coordinateEquiv := EuclideanSpace.equiv EuclideanDimension.two.CoordinateIndex ℝ
  let coordinateMeasure : Measure (EuclideanDimension.two.CoordinateIndex → ℝ) :=
    Measure.pi (fun _ : EuclideanDimension.two.CoordinateIndex => MeasureTheory.volume)
  let coarseSet := coordinateEquiv '' enlarged.faceRegion face
  let fineSet := coordinateEquiv ''
    (enlargedApproximation.fine spacing).faceRegion
      (enlargedApproximation.faceMap spacing face)
  have coarseMeasurable : MeasurableSet coarseSet :=
    (coordinateEquiv.isOpenMap _ (enlarged.faceRegion_open face)).measurableSet
  have fineMeasurable : MeasurableSet fineSet :=
    (coordinateEquiv.isOpenMap _
      ((enlargedApproximation.fine spacing).faceRegion_open
        (enlargedApproximation.faceMap spacing face))).measurableSet
  have coarseVolume : coordinateMeasure coarseSet =
      ENNReal.ofReal (enlarged.faceArea face) := by
    simpa [coordinateMeasure, coordinateEquiv, coarseSet,
      twoDimensionalCoordinateLebesgueVolume] using enlarged.faceArea_eq_volume face
  have fineVolume : coordinateMeasure fineSet =
      ENNReal.ofReal ((enlargedApproximation.fine spacing).faceArea
        (enlargedApproximation.faceMap spacing face)) := by
    simpa [coordinateMeasure, coordinateEquiv, fineSet,
      twoDimensionalCoordinateLebesgueVolume] using
      (enlargedApproximation.fine spacing).faceArea_eq_volume
        (enlargedApproximation.faceMap spacing face)
  have coarseFinite : coordinateMeasure coarseSet ≠ ⊤ := by rw [coarseVolume]; simp
  have fineFinite : coordinateMeasure fineSet ≠ ⊤ := by rw [fineVolume]; simp
  have symmetricBound := enlargedApproximation.face_symmetricDifference_area_le
    spacing belowCutoff face
  have imageSymmetric : coordinateEquiv ''
      twoDimensionalRegionSymmetricDifference
        (enlarged.faceRegion face)
        ((enlargedApproximation.fine spacing).faceRegion
          (enlargedApproximation.faceMap spacing face)) =
      symmDiff coarseSet fineSet := by
    exact Set.image_symmDiff coordinateEquiv.injective _ _
  have errorNonnegative :
      0 ≤ enlargedApproximation.areaOrderConstant * spacing.1 :=
    mul_nonneg enlargedApproximation.areaOrderConstant_nonnegative spacing.property.le
  have symmetricMeasureBound :
      coordinateMeasure (symmDiff coarseSet fineSet) ≤
        ENNReal.ofReal (enlargedApproximation.areaOrderConstant * spacing.1) := by
    simpa [coordinateMeasure, coordinateEquiv, coarseSet, fineSet,
      twoDimensionalCoordinateLebesgueVolume, imageSymmetric] using symmetricBound
  have symmetricFinite : coordinateMeasure (symmDiff coarseSet fineSet) ≠ ⊤ :=
    ne_top_of_le_ne_top (by simp) symmetricMeasureBound
  have coarseReal : coordinateMeasure.real coarseSet = enlarged.faceArea face := by
    rw [Measure.real, coarseVolume,
      ENNReal.toReal_ofReal (enlarged.faceArea_pos face).le]
  have fineReal : coordinateMeasure.real fineSet =
      (enlargedApproximation.fine spacing).faceArea
        (enlargedApproximation.faceMap spacing face) := by
    rw [Measure.real, fineVolume,
      ENNReal.toReal_ofReal
        ((enlargedApproximation.fine spacing).faceArea_pos _).le]
  calc
    |(enlargedApproximation.fine spacing).faceArea
        (enlargedApproximation.faceMap spacing face) - enlarged.faceArea face| =
      |coordinateMeasure.real fineSet - coordinateMeasure.real coarseSet| := by
        rw [fineReal, coarseReal]
    _ = |coordinateMeasure.real coarseSet - coordinateMeasure.real fineSet| :=
      abs_sub_comm _ _
    _ ≤ coordinateMeasure.real (symmDiff coarseSet fineSet) :=
      MeasureTheory.abs_measureReal_sub_le_measureReal_symmDiff'
        coarseMeasurable.nullMeasurableSet fineMeasurable.nullMeasurableSet
        coarseFinite fineFinite
    _ ≤ (ENNReal.ofReal
        (enlargedApproximation.areaOrderConstant * spacing.1)).toReal := by
      rw [Measure.real]
      exact (ENNReal.toReal_le_toReal symmetricFinite (by simp)).2 (by
        simpa [coordinateMeasure, coordinateEquiv, coarseSet, fineSet,
          twoDimensionalCoordinateLebesgueVolume, imageSymmetric] using symmetricBound)
    _ = enlargedApproximation.areaOrderConstant * spacing.1 :=
      ENNReal.toReal_ofReal errorNonnegative

omit [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [BorelSpace G]
    [MeasurableMul₂ G] [MeasurableInv G] in
/-- Mapped fine-face areas converge to the continuum areas, derived from the uniform
symmetric-difference estimate. -/
theorem twoDimensionalMappedFaceArea_tendsto
    (face : enlarged.Face) :
    Tendsto
      (fun spacing => (enlargedApproximation.fine spacing).faceArea
        (enlargedApproximation.faceMap spacing face))
      positiveLatticeSpacingAtZero
      (nhds (enlarged.faceArea face)) := by
  have spacingTends :
      Tendsto (fun spacing : PositiveLatticeSpacing => spacing.1)
        positiveLatticeSpacingAtZero (nhds (0 : ℝ)) :=
    positiveLatticeSpacingAtZero_tendsto.mono_right inf_le_left
  have belowCutoff : ∀ᶠ spacing in positiveLatticeSpacingAtZero,
      spacing.1 < enlargedApproximation.areaOrderCutoff :=
    (tendsto_order.1 spacingTends).2 _ enlargedApproximation.areaOrderCutoff_pos
  have errorTends : Tendsto
      (fun spacing : PositiveLatticeSpacing =>
        enlargedApproximation.areaOrderConstant * spacing.1)
      positiveLatticeSpacingAtZero (nhds 0) := by
    simpa using spacingTends.const_mul enlargedApproximation.areaOrderConstant
  apply tendsto_iff_dist_tendsto_zero.mpr
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall (fun _ => dist_nonneg)
  · filter_upwards [belowCutoff] with spacing hspacing
    simpa [Real.dist_eq] using
      twoDimensionalMappedFaceArea_abs_sub_le
        (enlargedApproximation := enlargedApproximation) spacing hspacing face
  · exact errorTends

omit [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [BorelSpace G]
    [MeasurableMul₂ G] [MeasurableInv G] in
/-- Distinct continuum faces eventually receive distinct fine-face labels. -/
theorem twoDimensionalFaceMap_eventually_pairwise_ne
    (first second : enlarged.Face) (different : first ≠ second) :
    ∀ᶠ spacing in positiveLatticeSpacingAtZero,
      enlargedApproximation.faceMap spacing first ≠
        enlargedApproximation.faceMap spacing second := by
  have spacingTends :
      Tendsto (fun spacing : PositiveLatticeSpacing => spacing.1)
        positiveLatticeSpacingAtZero (nhds (0 : ℝ)) :=
    positiveLatticeSpacingAtZero_tendsto.mono_right inf_le_left
  have belowCutoff : ∀ᶠ spacing in positiveLatticeSpacingAtZero,
      spacing.1 < enlargedApproximation.areaOrderCutoff :=
    (tendsto_order.1 spacingTends).2 _ enlargedApproximation.areaOrderCutoff_pos
  have scaledTends : Tendsto
      (fun spacing : PositiveLatticeSpacing =>
        (2 * enlargedApproximation.areaOrderConstant) * spacing.1)
      positiveLatticeSpacingAtZero (nhds 0) := by
    simpa using spacingTends.const_mul (2 * enlargedApproximation.areaOrderConstant)
  have scaledSmall : ∀ᶠ spacing in positiveLatticeSpacingAtZero,
      (2 * enlargedApproximation.areaOrderConstant) * spacing.1 <
        enlarged.faceArea first :=
    (tendsto_order.1 scaledTends).2 _ (enlarged.faceArea_pos first)
  filter_upwards [belowCutoff, scaledSmall] with spacing hcutoff hsmall
  intro collision
  let coordinateEquiv := EuclideanSpace.equiv EuclideanDimension.two.CoordinateIndex ℝ
  let coordinateMeasure : Measure (EuclideanDimension.two.CoordinateIndex → ℝ) :=
    Measure.pi (fun _ : EuclideanDimension.two.CoordinateIndex => MeasureTheory.volume)
  let firstSet := coordinateEquiv '' enlarged.faceRegion first
  let secondSet := coordinateEquiv '' enlarged.faceRegion second
  let fineSet := coordinateEquiv ''
    (enlargedApproximation.fine spacing).faceRegion
      (enlargedApproximation.faceMap spacing first)
  have firstVolume : coordinateMeasure firstSet =
      ENNReal.ofReal (enlarged.faceArea first) := by
    simpa [coordinateMeasure, coordinateEquiv, firstSet,
      twoDimensionalCoordinateLebesgueVolume] using enlarged.faceArea_eq_volume first
  have firstSubset : firstSet ⊆ symmDiff firstSet secondSet := by
    rintro _ ⟨point, pointFirst, rfl⟩
    have disjoint := Set.disjoint_left.1 (enlarged.faceRegion_disjoint first second different)
    have pointNotSecond : point ∉ enlarged.faceRegion second := fun pointSecond =>
      disjoint pointFirst pointSecond
    exact Or.inl ⟨⟨point, pointFirst, rfl⟩, by
      rintro ⟨candidate, candidateSecond, candidateEq⟩
      exact pointNotSecond (coordinateEquiv.injective candidateEq ▸ candidateSecond)⟩
  have lower : ENNReal.ofReal (enlarged.faceArea first) ≤
      coordinateMeasure (symmDiff firstSet secondSet) := by
    rw [← firstVolume]
    exact measure_mono firstSubset
  have triangle := measure_symmDiff_le firstSet fineSet secondSet (μ := coordinateMeasure)
  have firstApprox := enlargedApproximation.face_symmetricDifference_area_le
    spacing hcutoff first
  have secondApprox := enlargedApproximation.face_symmetricDifference_area_le
    spacing hcutoff second
  have firstImage : coordinateEquiv '' twoDimensionalRegionSymmetricDifference
      (enlarged.faceRegion first)
      ((enlargedApproximation.fine spacing).faceRegion
        (enlargedApproximation.faceMap spacing first)) =
      symmDiff firstSet fineSet :=
    Set.image_symmDiff coordinateEquiv.injective _ _
  have secondImage : coordinateEquiv '' twoDimensionalRegionSymmetricDifference
      (enlarged.faceRegion second)
      ((enlargedApproximation.fine spacing).faceRegion
        (enlargedApproximation.faceMap spacing second)) =
      symmDiff secondSet fineSet := by
    simpa [fineSet, secondSet, collision, twoDimensionalRegionSymmetricDifference,
      symmDiff_def] using
      (Set.image_symmDiff coordinateEquiv.injective
        (enlarged.faceRegion second)
        ((enlargedApproximation.fine spacing).faceRegion
          (enlargedApproximation.faceMap spacing second)))
  have firstBound : coordinateMeasure (symmDiff firstSet fineSet) ≤
      ENNReal.ofReal (enlargedApproximation.areaOrderConstant * spacing.1) := by
    simpa [coordinateMeasure, coordinateEquiv, firstSet, fineSet,
      twoDimensionalCoordinateLebesgueVolume, firstImage] using firstApprox
  have secondBound : coordinateMeasure (symmDiff fineSet secondSet) ≤
      ENNReal.ofReal (enlargedApproximation.areaOrderConstant * spacing.1) := by
    have bound : coordinateMeasure (symmDiff secondSet fineSet) ≤
        ENNReal.ofReal (enlargedApproximation.areaOrderConstant * spacing.1) := by
      simpa [coordinateMeasure, coordinateEquiv, secondSet, fineSet,
        twoDimensionalCoordinateLebesgueVolume, secondImage] using secondApprox
    simpa [symmDiff_comm] using bound
  have upper : coordinateMeasure (symmDiff firstSet secondSet) ≤
      ENNReal.ofReal ((2 * enlargedApproximation.areaOrderConstant) * spacing.1) := by
    calc
      coordinateMeasure (symmDiff firstSet secondSet) ≤
          coordinateMeasure (symmDiff firstSet fineSet) +
            coordinateMeasure (symmDiff fineSet secondSet) := triangle
      _ ≤ ENNReal.ofReal (enlargedApproximation.areaOrderConstant * spacing.1) +
          ENNReal.ofReal (enlargedApproximation.areaOrderConstant * spacing.1) :=
        add_le_add firstBound secondBound
      _ = ENNReal.ofReal ((2 * enlargedApproximation.areaOrderConstant) * spacing.1) := by
        rw [← ENNReal.ofReal_add
          (mul_nonneg enlargedApproximation.areaOrderConstant_nonnegative spacing.property.le)
          (mul_nonneg enlargedApproximation.areaOrderConstant_nonnegative spacing.property.le)]
        congr 1
        ring
  have strict : ENNReal.ofReal ((2 * enlargedApproximation.areaOrderConstant) * spacing.1) <
      ENNReal.ofReal (enlarged.faceArea first) := by
    exact ENNReal.ofReal_lt_ofReal_iff
      (enlarged.faceArea_pos first) |>.mpr hsmall
  exact (not_lt_of_ge (lower.trans upper)) strict

omit [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [BorelSpace G]
    [MeasurableMul₂ G] [MeasurableInv G] in
/-- The finite continuum-to-fine face map is eventually bijective, derived from positive disjoint
face areas, symmetric-difference control, and the stored all-spacing surjectivity. -/
theorem twoDimensionalFaceMap_eventually_bijective :
    ∀ᶠ spacing in positiveLatticeSpacingAtZero,
      Function.Bijective (enlargedApproximation.faceMap spacing) := by
  have eventuallyInjective : ∀ᶠ spacing in positiveLatticeSpacingAtZero,
      Function.Injective (enlargedApproximation.faceMap spacing) := by
    change ∀ᶠ spacing in positiveLatticeSpacingAtZero, ∀ first second,
      enlargedApproximation.faceMap spacing first =
        enlargedApproximation.faceMap spacing second → first = second
    rw [Filter.eventually_all]
    intro first
    rw [Filter.eventually_all]
    intro second
    by_cases equal : first = second
    · subst second
      exact Filter.Eventually.of_forall (fun _ _ => rfl)
    · filter_upwards [twoDimensionalFaceMap_eventually_pairwise_ne first second equal] with
        spacing ne
      intro mappedEqual
      exact False.elim (ne mappedEqual)
  filter_upwards [eventuallyInjective] with spacing injective
  exact ⟨injective, enlargedApproximation.faceMap_surjective spacing⟩

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
