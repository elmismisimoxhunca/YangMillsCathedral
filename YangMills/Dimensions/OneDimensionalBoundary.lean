/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Euclidean.SchwingerSpatialRay
import YangMills.Lattice.WilsonLoopObservable
import YangMills.Minkowski.WightmanLocality
import YangMills.Minkowski.WightmanTubeGeometry
import Mathlib.Topology.Algebra.Module.Alternating.Basic
import Mathlib.LinearAlgebra.Dimension.Finite

/-!
# One-dimensional degenerate/topological boundary contract

Euclidean spacetime dimension one is project consistency infrastructure, never a substitute for the
four-dimensional Clay quantifier. Degree-two alternating local curvature vanishes, there is no
spatial clustering direction and no spacelike-separated pair, and the plaquette lattice action is
zero. Nevertheless, periodic global holonomy and nonempty Wightman tube geometry may remain.

This module proves boundary facts only. It constructs no one-dimensional quantum theory and gives
no coercion into any higher-dimensional acceptance contract.
-/

namespace YangMills.Dimensions

open YangMills.Lattice
open YangMills.Minkowski

/-- Every real continuous alternating two-form on one-dimensional spacetime is zero. -/
theorem oneDimensional_continuousAlternatingMap_two_eq_zero
    {N : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N]
    (ω : (Spacetime EuclideanDimension.one) [⋀^Fin 2]→L[ℝ] N) : ω = 0 := by
  ext v
  apply ω.toAlternatingMap.map_linearDependent
  intro hlinear
  have hcard := hlinear.fintype_card_le_finrank
  simp at hcard

/-- Canonical kinematic boundary facts for Euclidean dimension one. -/
structure OneDimensionalKinematicBoundaryData where
  noSpatialClusteringDirection :
    IsEmpty (EuclideanUnitSpatialDirection EuclideanDimension.one)
  noSpacelikePointPair :
    spacelikeSeparatedPointPairSet EuclideanDimension.one = ∅
  noNonzeroSpacelikeTests :
    ∀ {f g : ScalarMinkowskiSchwartzTestFunction EuclideanDimension.one},
      f ≠ 0 → g ≠ 0 → ¬ HaveSpacelikeSeparatedTopologicalSupports f g
  backwardTubeNonempty :
    (wightmanBackwardTube EuclideanDimension.one 1).Nonempty

/-- The boundary facts are derived from exact dimension-one geometry, without a theory witness. -/
def oneDimensionalKinematicBoundaryData : OneDimensionalKinematicBoundaryData where
  noSpatialClusteringDirection := oneDimensional_no_unitSpatialDirection
  noSpacelikePointPair := oneDimensional_spacelikeSeparatedPointPairSet_eq_empty
  noNonzeroSpacelikeTests := fun hf hg =>
    oneDimensional_no_nonzero_spacelikeSeparated_schwartzTests hf hg
  backwardTubeNonempty := wightmanBackwardTube_nonempty EuclideanDimension.one 1

/-- Exact dimension-one finite-lattice boundary for a fixed potential/coupling. -/
structure OneDimensionalLatticeBoundaryData
    (Λ : FinitePeriodicLattice) {G : Type*} [Group G]
    (potential : PlaquettePotentialData G) (coupling : LatticeCouplingData) where
  noPlaquetteDirections : ∀ μ ν : EuclideanDimension.one.CoordinateIndex, ¬ μ < ν
  actionZero : ∀ U : GaugeField EuclideanDimension.one Λ G,
    wilsonTypeLatticeAction Λ potential coupling U = 0

/-- The exact finite-lattice boundary is derived for every group/potential/coupling. -/
def oneDimensionalLatticeBoundaryData
    (Λ : FinitePeriodicLattice) {G : Type*} [Group G]
    (potential : PlaquettePotentialData G) (coupling : LatticeCouplingData) :
    OneDimensionalLatticeBoundaryData Λ potential coupling where
  noPlaquetteDirections := oneDimensional_no_plaquetteDirections
  actionZero := oneDimensional_wilsonTypeLatticeAction_zero Λ potential coupling

/-- Unique one-site vertex in dimension one. -/
def oneDimensionalOneSiteVertex :
    Vertex EuclideanDimension.one (⟨0⟩ : FinitePeriodicLattice) :=
  fun _ => ⟨0, by simp [FinitePeriodicLattice.extent]⟩

/-- Unique dimension-one coordinate direction. -/
def oneDimensionalDirection : EuclideanDimension.one.CoordinateIndex :=
  ⟨0, by decide⟩

/-- A one-step path closes on the one-site periodic lattice. -/
theorem oneDimensional_oneSite_forwardPath_closed :
    IsClosedPath oneDimensionalOneSiteVertex [.forward oneDimensionalDirection] := by
  funext i
  fin_cases i
  simp [pathEndpoint, stepEndpoint, oneDimensionalOneSiteVertex,
    oneDimensionalDirection, shiftForward, cyclicSucc, FinitePeriodicLattice.extent]

/-- Zero plaquette action does not erase nonidentity global holonomy around the periodic loop: the
one-site constant link field has exact closed-loop holonomy `u`. No winding or homotopy claim is
made. -/
theorem oneDimensional_oneSite_holonomy_exact
    {G : Type*} [Group G] (u : G) :
    pathHolonomy
      (fun _ : PositiveOrientedLink EuclideanDimension.one ⟨0⟩ => u)
      oneDimensionalOneSiteVertex [.forward oneDimensionalDirection] = u := by
  simp [pathHolonomy, orientedLinkValue]

end YangMills.Dimensions
