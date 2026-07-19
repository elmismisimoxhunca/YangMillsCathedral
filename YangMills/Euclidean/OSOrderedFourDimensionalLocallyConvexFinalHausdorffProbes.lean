/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Euclidean.OSOrderedFourDimensionalLocallyConvexFinalHausdorff

/-!
# Hostile probes for Hausdorff exact-source locally convex topology

The probes require exact scalar/component coordinates, injectivity, an admissible separating
coordinate topology, continuity of the coordinate CLM, nonzero-coordinate retention, and actual
disjoint open neighborhoods for every unequal source-sequence pair.
-/

namespace YangMills.OSOrderedFourDimensionalLocallyConvexFinalHausdorff.Probes

noncomputable section

noncomputable local instance sourceAddCommGroupForProbes (arity : PositiveArity) :
    AddCommGroup (OSPositiveTimeOrderedFourDimensionalSourceSpace arity) :=
  OSPositiveTimeOrderedFourDimensionalSourceSpace.addCommGroup arity

noncomputable local instance sourceModuleForProbes (arity : PositiveArity) :
    Module ℂ (OSPositiveTimeOrderedFourDimensionalSourceSpace arity) :=
  OSPositiveTimeOrderedFourDimensionalSourceSpace.module arity

noncomputable local instance sourceT2ForProbes (arity : PositiveArity) :
    T2Space (OSPositiveTimeOrderedFourDimensionalSourceSpace arity) :=
  OSPositiveTimeOrderedFourDimensionalSourceSpace.t2Space arity

noncomputable local instance sequenceTopologyForProbes :
    TopologicalSpace OSPositiveTimeOrderedFourDimensionalTestSequence :=
  osPositiveTimeOrderedFourDimensionalLocallyConvexFinalTopology

noncomputable local instance sequenceAddCommGroupForProbes :
    AddCommGroup OSPositiveTimeOrderedFourDimensionalTestSequence :=
  osPositiveTimeOrderedFourDimensionalSequenceAddCommGroup

noncomputable local instance sequenceModuleForProbes :
    Module ℂ OSPositiveTimeOrderedFourDimensionalTestSequence :=
  osPositiveTimeOrderedFourDimensionalSequenceModule

/-- The separating map retains both the scalar and every exact source component. -/
theorem exact_all_coordinates
    (f : OSPositiveTimeOrderedFourDimensionalTestSequence) (arity : PositiveArity) :
    (osPositiveTimeOrderedFourDimensionalSequenceToAllCoordinatesLinearMap f).1 = f.zeroPoint ∧
    (osPositiveTimeOrderedFourDimensionalSequenceToAllCoordinatesLinearMap f).2 arity =
      f.component arity :=
  ⟨rfl, rfl⟩

/-- Disconnected replacement of one sequence by another with the same coordinate image is blocked. -/
theorem exact_coordinate_injectivity :
    Function.Injective osPositiveTimeOrderedFourDimensionalSequenceToAllCoordinatesLinearMap :=
  osPositiveTimeOrderedFourDimensionalSequenceToAllCoordinatesLinearMap_injective

/-- The auxiliary separating coordinate topology satisfies every locally convex final requirement. -/
theorem exact_coordinate_topology_admissible :
    IsOSPositiveTimeOrderedFourDimensionalLocallyConvexFinalTopology
      osPositiveTimeOrderedFourDimensionalAllCoordinatesInducedTopology :=
  isOSPositiveTimeOrderedFourDimensionalLocallyConvexFinalTopology_allCoordinatesInduced

/-- The all-coordinate CLM is exactly the algebraic coordinate map. -/
theorem exact_continuous_coordinate_map
    (f : OSPositiveTimeOrderedFourDimensionalTestSequence) :
    osPositiveTimeOrderedFourDimensionalSequenceToAllCoordinatesContinuousLinearMap f =
      osPositiveTimeOrderedFourDimensionalSequenceToAllCoordinatesLinearMap f :=
  rfl

/-- The explicit nonzero singleton remains visible in its arity-one coordinate. -/
theorem nonzero_singleton_coordinate_retained :
    ((osPositiveTimeOrderedFourDimensionalSequenceToAllCoordinatesLinearMap
      singletonPositiveTimeBumpFourDimensionalOSSourceSequence).2
        PositiveArity.one).toSchwartz ≠ 0 := by
  change (singletonPositiveTimeBumpFourDimensionalOSSourceSequence.component
    PositiveArity.one).toSchwartz ≠ 0
  rw [singletonPositiveTimeBumpFourDimensionalOSSourceSequence,
    MathlibStrictPositiveTimeTestSequence.toFourDimensionalOSSourceSequence_component,
    singletonPositiveTimeBumpSequence_component_one]
  exact positiveTimeBumpSchwartz_ne_zero EuclideanDimension.four

/-- Installing the named Hausdorff structure separates every unequal exact source-sequence pair by
disjoint open neighborhoods. -/
theorem exact_disjoint_open_separation
    (f g : OSPositiveTimeOrderedFourDimensionalTestSequence) (hfg : f ≠ g) :
    letI : T2Space OSPositiveTimeOrderedFourDimensionalTestSequence :=
      osPositiveTimeOrderedFourDimensionalLocallyConvexFinalT2Space
    ∃ U V : Set OSPositiveTimeOrderedFourDimensionalTestSequence,
      IsOpen U ∧ IsOpen V ∧ f ∈ U ∧ g ∈ V ∧ Disjoint U V := by
  letI : T2Space OSPositiveTimeOrderedFourDimensionalTestSequence :=
    osPositiveTimeOrderedFourDimensionalLocallyConvexFinalT2Space
  exact t2_separation hfg

end

end YangMills.OSOrderedFourDimensionalLocallyConvexFinalHausdorff.Probes
