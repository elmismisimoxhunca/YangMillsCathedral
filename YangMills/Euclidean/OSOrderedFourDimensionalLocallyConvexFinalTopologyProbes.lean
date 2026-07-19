/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Euclidean.OSOrderedFourDimensionalLocallyConvexFinalTopology

/-!
# Hostile probes for the exact-source locally convex final topology

The probes install the named aggregate structures, require genuine stage continuity and convex
neighborhoods, retain the nonzero source sequence, and expose raw-topology equality only through
the exact admissibility gate.
-/

namespace YangMills.OSOrderedFourDimensionalLocallyConvexFinalTopology.Probes

open scoped Topology
open Filter

noncomputable section

noncomputable local instance sourceAddCommGroupForProbes (arity : PositiveArity) :
    AddCommGroup (OSPositiveTimeOrderedFourDimensionalSourceSpace arity) :=
  OSPositiveTimeOrderedFourDimensionalSourceSpace.addCommGroup arity

noncomputable local instance sourceModuleForProbes (arity : PositiveArity) :
    Module ℂ (OSPositiveTimeOrderedFourDimensionalSourceSpace arity) :=
  OSPositiveTimeOrderedFourDimensionalSourceSpace.module arity

noncomputable local instance sequenceTopologyForProbes :
    TopologicalSpace OSPositiveTimeOrderedFourDimensionalTestSequence :=
  osPositiveTimeOrderedFourDimensionalLocallyConvexFinalTopology

noncomputable local instance sequenceAddCommGroupForProbes :
    AddCommGroup OSPositiveTimeOrderedFourDimensionalTestSequence :=
  osPositiveTimeOrderedFourDimensionalSequenceAddCommGroup

noncomputable local instance sequenceModuleForProbes :
    Module ℂ OSPositiveTimeOrderedFourDimensionalTestSequence :=
  osPositiveTimeOrderedFourDimensionalSequenceModule

/-- The defining family contains the constructed topology itself, preventing an empty-family
interpretation of the `sInf`. -/
theorem exact_self_admissibility :
    IsOSPositiveTimeOrderedFourDimensionalLocallyConvexFinalTopology
      osPositiveTimeOrderedFourDimensionalLocallyConvexFinalTopology :=
  isOSPositiveTimeOrderedFourDimensionalLocallyConvexFinalTopology_self

/-- Installing the named topological additive group exposes genuine joint sequence addition. -/
theorem exact_joint_addition :
    letI : IsTopologicalAddGroup OSPositiveTimeOrderedFourDimensionalTestSequence :=
      osPositiveTimeOrderedFourDimensionalLocallyConvexFinalIsTopologicalAddGroup
    Continuous (fun p : OSPositiveTimeOrderedFourDimensionalTestSequence ×
      OSPositiveTimeOrderedFourDimensionalTestSequence => p.1 + p.2) := by
  letI : IsTopologicalAddGroup OSPositiveTimeOrderedFourDimensionalTestSequence :=
    osPositiveTimeOrderedFourDimensionalLocallyConvexFinalIsTopologicalAddGroup
  exact continuous_add

/-- Installing the named scalar structure exposes genuine joint complex scalar continuity. -/
theorem exact_joint_scalar_action :
    letI : ContinuousSMul ℂ OSPositiveTimeOrderedFourDimensionalTestSequence :=
      osPositiveTimeOrderedFourDimensionalLocallyConvexFinalContinuousSMul
    Continuous (fun p : ℂ × OSPositiveTimeOrderedFourDimensionalTestSequence => p.1 • p.2) := by
  letI : ContinuousSMul ℂ OSPositiveTimeOrderedFourDimensionalTestSequence :=
    osPositiveTimeOrderedFourDimensionalLocallyConvexFinalContinuousSMul
  exact continuous_smul

/-- Named local convexity gives an actual convex refinement of every zero neighborhood. -/
theorem exact_convex_zero_neighborhood
    (U : Set OSPositiveTimeOrderedFourDimensionalTestSequence)
    (hU : U ∈ 𝓝 (0 : OSPositiveTimeOrderedFourDimensionalTestSequence)) :
    ∃ V ∈ 𝓝 (0 : OSPositiveTimeOrderedFourDimensionalTestSequence),
      Convex ℝ V ∧ V ⊆ U := by
  letI : IsTopologicalAddGroup OSPositiveTimeOrderedFourDimensionalTestSequence :=
    osPositiveTimeOrderedFourDimensionalLocallyConvexFinalIsTopologicalAddGroup
  letI : LocallyConvexSpace ℝ OSPositiveTimeOrderedFourDimensionalTestSequence :=
    osPositiveTimeOrderedFourDimensionalLocallyConvexFinalLocallyConvexSpace
  have hb := (locallyConvexSpace_iff_zero ℝ
    OSPositiveTimeOrderedFourDimensionalTestSequence).mp inferInstance
  rcases hb.mem_iff.mp hU with ⟨V, hV, hsub⟩
  exact ⟨V, hV.1, hV.2, hsub⟩

/-- Every exact finite-stage extension remains the same map after continuous-linear bundling. -/
theorem exact_stage_map (s : Finset PositiveArity)
    (x : OSPositiveTimeOrderedFourDimensionalStage s) :
    osPositiveTimeOrderedFourDimensionalStageToLocallyConvexFinalContinuousLinearMap s x =
      osPositiveTimeOrderedFourDimensionalStageToSequence s x :=
  rfl

/-- The nonzero singleton is recovered exactly through its support stage in the new topology. -/
theorem nonzero_singleton_stage_retained :
    osPositiveTimeOrderedFourDimensionalStageToLocallyConvexFinalContinuousLinearMap
      singletonPositiveTimeBumpFourDimensionalOSSourceSequence.support
      (osPositiveTimeOrderedFourDimensionalSequenceToSupportStage
        singletonPositiveTimeBumpFourDimensionalOSSourceSequence) =
      singletonPositiveTimeBumpFourDimensionalOSSourceSequence := by
  rw [osPositiveTimeOrderedFourDimensionalStageToLocallyConvexFinalContinuousLinearMap_apply]
  exact osPositiveTimeOrderedFourDimensionalStage_recover
    singletonPositiveTimeBumpFourDimensionalOSSourceSequence

/-- The raw topology comparison has the proved direction only. -/
theorem exact_raw_comparison :
    osPositiveTimeOrderedFourDimensionalFiniteStageFinalTopology ≤
      osPositiveTimeOrderedFourDimensionalLocallyConvexFinalTopology :=
  osPositiveTimeOrderedFourDimensionalFiniteStageFinalTopology_le_locallyConvexFinal

/-- Equality with the raw final topology is never inferred without all raw admissibility fields. -/
theorem exact_raw_equality_gate :
    osPositiveTimeOrderedFourDimensionalLocallyConvexFinalTopology =
        osPositiveTimeOrderedFourDimensionalFiniteStageFinalTopology ↔
      IsOSPositiveTimeOrderedFourDimensionalLocallyConvexFinalTopology
        osPositiveTimeOrderedFourDimensionalFiniteStageFinalTopology :=
  osPositiveTimeOrderedFourDimensionalLocallyConvexFinalTopology_eq_raw_iff

end

end YangMills.OSOrderedFourDimensionalLocallyConvexFinalTopology.Probes
