/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Euclidean.OSOrderedFourDimensionalFiniteStageLocallyConvex

/-!
# Hostile probes for exact OS finite-stage local convexity

The probes install each named aggregate, exercise joint addition and scalar continuity and convex
zero neighborhoods, and ensure the independent scalar survives even at the empty positive stage.
-/

namespace YangMills.OSOrderedFourDimensionalFiniteStageLocallyConvex.Probes

open scoped Topology
open Filter

noncomputable section

noncomputable local instance sourceAddCommGroupForProbes (arity : PositiveArity) :
    AddCommGroup (OSPositiveTimeOrderedFourDimensionalSourceSpace arity) :=
  OSPositiveTimeOrderedFourDimensionalSourceSpace.addCommGroup arity

noncomputable local instance sourceModuleForProbes (arity : PositiveArity) :
    Module ℂ (OSPositiveTimeOrderedFourDimensionalSourceSpace arity) :=
  OSPositiveTimeOrderedFourDimensionalSourceSpace.module arity

noncomputable local instance sourceTopologicalAddGroupForProbes (arity : PositiveArity) :
    IsTopologicalAddGroup (OSPositiveTimeOrderedFourDimensionalSourceSpace arity) :=
  OSPositiveTimeOrderedFourDimensionalSourceSpace.isTopologicalAddGroup arity

noncomputable local instance sourceContinuousSMulForProbes (arity : PositiveArity) :
    ContinuousSMul ℂ (OSPositiveTimeOrderedFourDimensionalSourceSpace arity) :=
  OSPositiveTimeOrderedFourDimensionalSourceSpace.continuousSMul arity

noncomputable local instance sourceLocallyConvexForProbes (arity : PositiveArity) :
    LocallyConvexSpace ℝ (OSPositiveTimeOrderedFourDimensionalSourceSpace arity) :=
  OSPositiveTimeOrderedFourDimensionalSourceSpace.locallyConvexSpace arity

/-- Installing the named finite-stage topological group yields joint addition continuity. -/
theorem exact_stage_continuous_add (s : Finset PositiveArity) :
    letI : IsTopologicalAddGroup (OSPositiveTimeOrderedFourDimensionalStage s) :=
      osPositiveTimeOrderedFourDimensionalStageIsTopologicalAddGroup s
    Continuous (fun p : OSPositiveTimeOrderedFourDimensionalStage s ×
      OSPositiveTimeOrderedFourDimensionalStage s => p.1 + p.2) := by
  letI : IsTopologicalAddGroup (OSPositiveTimeOrderedFourDimensionalStage s) :=
    osPositiveTimeOrderedFourDimensionalStageIsTopologicalAddGroup s
  exact continuous_add

/-- Installing the named finite-stage scalar structure yields the exact joint complex action. -/
theorem exact_stage_continuous_smul (s : Finset PositiveArity) :
    letI : ContinuousSMul ℂ (OSPositiveTimeOrderedFourDimensionalStage s) :=
      osPositiveTimeOrderedFourDimensionalStageContinuousSMul s
    Continuous (fun p : ℂ × OSPositiveTimeOrderedFourDimensionalStage s => p.1 • p.2) := by
  letI : ContinuousSMul ℂ (OSPositiveTimeOrderedFourDimensionalStage s) :=
    osPositiveTimeOrderedFourDimensionalStageContinuousSMul s
  exact continuous_smul

/-- Installing named stage local convexity supplies an actual convex zero-neighborhood refinement. -/
theorem exact_stage_convex_zero_neighborhood (s : Finset PositiveArity)
    (U : Set (OSPositiveTimeOrderedFourDimensionalStage s))
    (hU : U ∈ 𝓝 (0 : OSPositiveTimeOrderedFourDimensionalStage s)) :
    ∃ V ∈ 𝓝 (0 : OSPositiveTimeOrderedFourDimensionalStage s),
      Convex ℝ V ∧ V ⊆ U := by
  letI : IsTopologicalAddGroup (OSPositiveTimeOrderedFourDimensionalStage s) :=
    osPositiveTimeOrderedFourDimensionalStageIsTopologicalAddGroup s
  letI : LocallyConvexSpace ℝ (OSPositiveTimeOrderedFourDimensionalStage s) :=
    osPositiveTimeOrderedFourDimensionalStageLocallyConvexSpace s
  have hb := (locallyConvexSpace_iff_zero ℝ
    (OSPositiveTimeOrderedFourDimensionalStage s)).mp inferInstance
  rcases hb.mem_iff.mp hU with ⟨V, hV, hsub⟩
  exact ⟨V, hV.1, hV.2, hsub⟩

/-- The empty positive-arity stage still carries the independent nonzero scalar component. -/
def emptyStageScalarUnit : OSPositiveTimeOrderedFourDimensionalStage ∅ :=
  ⟨1, fun ⟨arity, h⟩ => by
    have hall : ∀ a : PositiveArity, a ∈ (∅ : Finset PositiveArity) → False :=
      (Finset.forall_mem_empty_iff (fun _ : PositiveArity => False)).mpr trivial
    exact False.elim (hall arity h)⟩

/-- Finite-stage topology and local convexity cannot erase the scalar coordinate. -/
@[simp]
theorem emptyStageScalarUnit_zeroPoint : emptyStageScalarUnit.1 = 1 :=
  rfl

end

end YangMills.OSOrderedFourDimensionalFiniteStageLocallyConvex.Probes
