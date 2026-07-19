/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Euclidean.SchwingerSpatialRay
import YangMills.Lattice.FinitePeriodicGaugeField
import YangMills.Mathematics.ContinuousBilinearWedge
import YangMills.Minkowski.WightmanLocality
import YangMills.Minkowski.WightmanTubeGeometry

/-!
# Two-dimensional nondegeneracy consistency data

Dimension two is the first project consistency regime with a genuine alternating curvature slot,
a spatial clustering direction, spacelike-separated test functions, and an elementary lattice
plaquette. This module constructs exact witnesses for all four facts.

The lattice witness realizes any element of an arbitrary gauge group as one selected plaquette
holonomy on a concrete `2 × 2` periodic lattice. For every admissible plaquette potential, its
nontriviality field therefore gives a selected plaquette with strictly positive local density.

These are kinematic and finite-cutoff consistency witnesses only. They do not construct a
continuum two-dimensional Yang--Mills theory, an OS measure, a Wightman theory, or a mass gap, and
they cannot satisfy any three- or four-dimensional acceptance contract.
-/

namespace YangMills.Dimensions

open YangMills.Lattice
open YangMills.Minkowski

noncomputable section

/-- Time-coordinate index in two-dimensional spacetime. -/
def twoDimensionalTimeIndex : EuclideanDimension.two.CoordinateIndex := ⟨0, by decide⟩

/-- The unique coordinate after time in two-dimensional spacetime. -/
def twoDimensionalSpatialIndex : EuclideanDimension.two.CoordinateIndex := ⟨1, by decide⟩

/-- The time index precedes the spatial index, so dimension two has one ordered plaquette plane. -/
theorem twoDimensional_time_lt_spatial :
    twoDimensionalTimeIndex < twoDimensionalSpatialIndex := by
  decide

/-- Continuous coordinate functional on two-dimensional Euclidean spacetime. -/
noncomputable def twoDimensionalCoordinate
    (i : EuclideanDimension.two.CoordinateIndex) :
    EuclideanDimension.two.Spacetime →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj i).comp
    (PiLp.continuousLinearEquiv 2 ℝ
      (fun _ : EuclideanDimension.two.CoordinateIndex => ℝ)).toContinuousLinearMap

/-- Coordinate functional represented as a continuous alternating one-form. -/
noncomputable def twoDimensionalCoordinateOneForm
    (i : EuclideanDimension.two.CoordinateIndex) :
    EuclideanDimension.two.Spacetime [⋀^Fin 1]→L[ℝ] ℝ :=
  ContinuousAlternatingMap.ofSubsingleton ℝ EuclideanDimension.two.Spacetime ℝ
    (0 : Fin 1) (twoDimensionalCoordinate i)

/-- Canonical oriented area form `dx⁰ ∧ dx¹` on two-dimensional Euclidean spacetime. -/
noncomputable def twoDimensionalAreaForm :
    EuclideanDimension.two.Spacetime [⋀^Fin 2]→L[ℝ] ℝ :=
  ContinuousAlternatingMap.continuousBilinearWedgeOneMany
    (ContinuousLinearMap.mul ℝ ℝ) 1
    (twoDimensionalCoordinateOneForm twoDimensionalTimeIndex)
    (twoDimensionalCoordinateOneForm twoDimensionalSpatialIndex)

/-- Standard time basis vector in dimension two. -/
noncomputable def twoDimensionalTimeBasisVector : EuclideanDimension.two.Spacetime :=
  EuclideanSpace.single twoDimensionalTimeIndex 1

/-- Standard spatial basis vector in dimension two. -/
noncomputable def twoDimensionalSpatialBasisVector : EuclideanDimension.two.Spacetime :=
  EuclideanSpace.single twoDimensionalSpatialIndex 1

/-- The canonical area form evaluates to one on the ordered standard basis. -/
@[simp]
theorem twoDimensionalAreaForm_standardBasis :
    twoDimensionalAreaForm (fun i =>
      if i = 0 then twoDimensionalTimeBasisVector else twoDimensionalSpatialBasisVector) = 1 := by
  unfold twoDimensionalAreaForm
  rw [ContinuousAlternatingMap.continuousBilinearWedgeOneMany_one_apply]
  simp [twoDimensionalCoordinateOneForm, twoDimensionalCoordinate,
    twoDimensionalTimeBasisVector, twoDimensionalSpatialBasisVector,
    twoDimensionalTimeIndex, twoDimensionalSpatialIndex]

/-- Unlike dimension one, dimension two supports a nonzero continuous alternating two-form. -/
theorem twoDimensionalAreaForm_ne_zero : twoDimensionalAreaForm ≠ 0 := by
  intro zero_area
  have evaluated := congrArg (fun form => form (fun i =>
    if i = 0 then twoDimensionalTimeBasisVector else twoDimensionalSpatialBasisVector)) zero_area
  rw [twoDimensionalAreaForm_standardBasis] at evaluated
  simp at evaluated

/-- Exact kinematic nondegeneracy witnesses in dimension two. -/
structure TwoDimensionalKinematicNondegeneracyData where
  spatialDirection : EuclideanUnitSpatialDirection EuclideanDimension.two
  areaForm : EuclideanDimension.two.Spacetime [⋀^Fin 2]→L[ℝ] ℝ
  areaFormNonzero : areaForm ≠ 0
  nonzeroSpacelikeTests :
    ∃ f g : ScalarMinkowskiSchwartzTestFunction EuclideanDimension.two,
      f ≠ 0 ∧ g ≠ 0 ∧ HaveSpacelikeSeparatedTopologicalSupports f g
  backwardTubeNonempty :
    (wightmanBackwardTube EuclideanDimension.two 1).Nonempty

/-- The dimension-two kinematic consistency data are explicitly inhabited without a theory. -/
noncomputable def twoDimensionalKinematicNondegeneracyData :
    TwoDimensionalKinematicNondegeneracyData where
  spatialDirection :=
    canonicalEuclideanUnitSpatialDirection EuclideanDimension.two (by decide)
  areaForm := twoDimensionalAreaForm
  areaFormNonzero := twoDimensionalAreaForm_ne_zero
  nonzeroSpacelikeTests :=
    exists_nonzero_spacelikeSeparated_scalarMinkowskiSchwartzTests
      EuclideanDimension.two (by decide)
  backwardTubeNonempty := wightmanBackwardTube_nonempty EuclideanDimension.two 1

/-- Concrete two-site-per-axis periodic lattice used for the elementary plaquette witness. -/
def twoDimensionalPlaquetteLattice : FinitePeriodicLattice := ⟨1⟩

/-- Origin vertex on the concrete two-dimensional lattice. -/
def twoDimensionalPlaquetteOrigin :
    Vertex EuclideanDimension.two twoDimensionalPlaquetteLattice :=
  fun _ => ⟨0, by decide⟩

/-- A gauge field supported on the time-oriented link at the selected origin. -/
def twoDimensionalSingleLinkGaugeField
    {G : Type*} [Group G] (u : G) :
    GaugeField EuclideanDimension.two twoDimensionalPlaquetteLattice G := fun link =>
  if link = ⟨twoDimensionalPlaquetteOrigin, twoDimensionalTimeIndex⟩ then u else 1

/-- A spatial shift changes the origin on the concrete two-site lattice. -/
theorem twoDimensional_shiftSpatial_origin_ne :
    shiftForward twoDimensionalPlaquetteOrigin twoDimensionalSpatialIndex ≠
      twoDimensionalPlaquetteOrigin := by
  intro equality
  have at_spatial := congrFun equality twoDimensionalSpatialIndex
  simp [shiftForward, twoDimensionalPlaquetteOrigin, twoDimensionalSpatialIndex,
    cyclicSucc, twoDimensionalPlaquetteLattice, FinitePeriodicLattice.extent] at at_spatial

/-- The selected elementary plaquette has exactly the prescribed holonomy `u`. -/
@[simp]
theorem twoDimensionalSingleLinkGaugeField_plaquetteHolonomy
    {G : Type*} [Group G] (u : G) :
    plaquetteHolonomy (twoDimensionalSingleLinkGaugeField u)
      twoDimensionalPlaquetteOrigin twoDimensionalTimeIndex twoDimensionalSpatialIndex = u := by
  have directions_ne : twoDimensionalSpatialIndex ≠ twoDimensionalTimeIndex := by decide
  have second_link_ne :
      (⟨shiftForward twoDimensionalPlaquetteOrigin twoDimensionalTimeIndex,
          twoDimensionalSpatialIndex⟩ :
        PositiveOrientedLink EuclideanDimension.two twoDimensionalPlaquetteLattice) ≠
        ⟨twoDimensionalPlaquetteOrigin, twoDimensionalTimeIndex⟩ := by
    intro equality
    exact directions_ne (congrArg PositiveOrientedLink.direction equality)
  have third_link_ne :
      (⟨shiftForward twoDimensionalPlaquetteOrigin twoDimensionalSpatialIndex,
          twoDimensionalTimeIndex⟩ :
        PositiveOrientedLink EuclideanDimension.two twoDimensionalPlaquetteLattice) ≠
        ⟨twoDimensionalPlaquetteOrigin, twoDimensionalTimeIndex⟩ := by
    intro equality
    exact twoDimensional_shiftSpatial_origin_ne
      (congrArg PositiveOrientedLink.base equality)
  have fourth_link_ne :
      (⟨twoDimensionalPlaquetteOrigin, twoDimensionalSpatialIndex⟩ :
        PositiveOrientedLink EuclideanDimension.two twoDimensionalPlaquetteLattice) ≠
        ⟨twoDimensionalPlaquetteOrigin, twoDimensionalTimeIndex⟩ := by
    intro equality
    exact directions_ne (congrArg PositiveOrientedLink.direction equality)
  simp [plaquetteHolonomy, twoDimensionalSingleLinkGaugeField,
    second_link_ne, third_link_ne, fourth_link_ne]

/-- For an admissible potential, a concrete selected two-dimensional plaquette has positive local
action density. This is finite-cutoff evidence, not a continuum construction. -/
structure TwoDimensionalPositivePlaquetteData
    {G : Type*} [Group G] (potential : PlaquettePotentialData G) where
  holonomyElement : G
  potentialPositive : 0 < potential.potential holonomyElement
  gaugeField : GaugeField EuclideanDimension.two twoDimensionalPlaquetteLattice G
  exactHolonomy : plaquetteHolonomy gaugeField twoDimensionalPlaquetteOrigin
    twoDimensionalTimeIndex twoDimensionalSpatialIndex = holonomyElement

/-- Every admissible nontrivial potential supplies the concrete positive plaquette witness. -/
noncomputable def twoDimensionalPositivePlaquetteData
    {G : Type*} [Group G] (potential : PlaquettePotentialData G) :
    TwoDimensionalPositivePlaquetteData potential := by
  choose u positive using potential.nontrivial
  exact {
    holonomyElement := u
    potentialPositive := positive
    gaugeField := twoDimensionalSingleLinkGaugeField u
    exactHolonomy := twoDimensionalSingleLinkGaugeField_plaquetteHolonomy u
  }

end

end YangMills.Dimensions
