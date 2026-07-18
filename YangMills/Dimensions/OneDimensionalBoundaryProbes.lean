/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Dimensions.OneDimensionalBoundary

/-!
# Hostile probes for the one-dimensional boundary

The probes expose vanishing local two-form/plaquette sectors while retaining possible global
holonomy and analytic tube geometry. They reject using dimension one as dimension four.
-/

namespace YangMills.Dimensions.OneDimensionalBoundary.Probes

open YangMills.Lattice
open YangMills.Minkowski

/-- Every continuous alternating two-form on one-dimensional spacetime vanishes. -/
theorem exact_degree_two_degeneracy
    {N : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N]
    (ω : (Spacetime EuclideanDimension.one) [⋀^Fin 2]→L[ℝ] N) : ω = 0 :=
  oneDimensional_continuousAlternatingMap_two_eq_zero ω

/-- The canonical kinematic boundary simultaneously records all dimension-one obstructions. -/
theorem exact_kinematic_boundary :
    IsEmpty (EuclideanUnitSpatialDirection EuclideanDimension.one) ∧
    spacelikeSeparatedPointPairSet EuclideanDimension.one = ∅ ∧
    (∀ {f g : ScalarMinkowskiSchwartzTestFunction EuclideanDimension.one},
      f ≠ 0 → g ≠ 0 → ¬ HaveSpacelikeSeparatedTopologicalSupports f g) ∧
    (wightmanBackwardTube EuclideanDimension.one 1).Nonempty :=
  ⟨oneDimensionalKinematicBoundaryData.noSpatialClusteringDirection,
    oneDimensionalKinematicBoundaryData.noSpacelikePointPair,
    oneDimensionalKinematicBoundaryData.noNonzeroSpacelikeTests,
    oneDimensionalKinematicBoundaryData.backwardTubeNonempty⟩

/-- Every dimension-one plaquette action is exactly zero. -/
theorem exact_lattice_action_boundary
    (Λ : FinitePeriodicLattice) {G : Type*} [Group G]
    (potential : PlaquettePotentialData G) (coupling : LatticeCouplingData)
    (U : GaugeField EuclideanDimension.one Λ G) :
    wilsonTypeLatticeAction Λ potential coupling U = 0 :=
  (oneDimensionalLatticeBoundaryData Λ potential coupling).actionZero U

/-- Local action degeneracy does not force global holonomy to be trivial. -/
theorem nontrivial_global_holonomy_can_remain
    {G : Type*} [Group G]
    (potential : PlaquettePotentialData G) (coupling : LatticeCouplingData)
    (u : G) (hu : u ≠ 1) :
    ∃ U : GaugeField EuclideanDimension.one (⟨0⟩ : FinitePeriodicLattice) G,
      wilsonTypeLatticeAction ⟨0⟩ potential coupling U = 0 ∧
      IsClosedPath oneDimensionalOneSiteVertex [.forward oneDimensionalDirection] ∧
      pathHolonomy U oneDimensionalOneSiteVertex [.forward oneDimensionalDirection] ≠ 1 := by
  refine ⟨fun _ => u,
    oneDimensional_wilsonTypeLatticeAction_zero ⟨0⟩ potential coupling _,
    oneDimensional_oneSite_forwardPath_closed, ?_⟩
  rw [oneDimensional_oneSite_holonomy_exact]
  exact hu

/-- The lower-dimensional boundary index cannot be confused with the Clay endpoint. -/
theorem one_dimension_cannot_be_four :
    EuclideanDimension.one ≠ EuclideanDimension.four := by
  intro h
  have := congrArg EuclideanDimension.value h
  norm_num at this

end YangMills.Dimensions.OneDimensionalBoundary.Probes
