/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Euclidean.OSOrderedFourDimensionalFiniteStageContinuousLinear
import YangMills.Euclidean.OSOrderedFourDimensionalSourceSpaceLocallyConvex

/-!
# Local convexity of exact OS finite stages

Each exact finite stage is the product of the separate scalar `f₀ ∈ ℂ` and a finite dependent
product of exact positive-arity source spaces. Their named topological additive-group, continuous
complex scalar, and real locally convex structures therefore induce corresponding named structures
on every stage.

This concerns only finite products. It does not establish joint addition or local convexity on the
final source-sequence topology, identify a locally convex direct sum, construct any completion or
completed tensor product, state `(E2)`, or perform reconstruction.
-/

namespace YangMills

noncomputable section

noncomputable local instance sourceAddCommGroupForStageLocallyConvex
    (arity : PositiveArity) :
    AddCommGroup (OSPositiveTimeOrderedFourDimensionalSourceSpace arity) :=
  OSPositiveTimeOrderedFourDimensionalSourceSpace.addCommGroup arity

noncomputable local instance sourceModuleForStageLocallyConvex
    (arity : PositiveArity) :
    Module ℂ (OSPositiveTimeOrderedFourDimensionalSourceSpace arity) :=
  OSPositiveTimeOrderedFourDimensionalSourceSpace.module arity

noncomputable local instance sourceTopologicalAddGroupForStageLocallyConvex
    (arity : PositiveArity) :
    IsTopologicalAddGroup (OSPositiveTimeOrderedFourDimensionalSourceSpace arity) :=
  OSPositiveTimeOrderedFourDimensionalSourceSpace.isTopologicalAddGroup arity

noncomputable local instance sourceContinuousSMulForStageLocallyConvex
    (arity : PositiveArity) :
    ContinuousSMul ℂ (OSPositiveTimeOrderedFourDimensionalSourceSpace arity) :=
  OSPositiveTimeOrderedFourDimensionalSourceSpace.continuousSMul arity

noncomputable local instance sourceLocallyConvexForStageLocallyConvex
    (arity : PositiveArity) :
    LocallyConvexSpace ℝ (OSPositiveTimeOrderedFourDimensionalSourceSpace arity) :=
  OSPositiveTimeOrderedFourDimensionalSourceSpace.locallyConvexSpace arity

/-- Named topological additive-group structure on an exact finite source stage. -/
@[reducible]
noncomputable def osPositiveTimeOrderedFourDimensionalStageIsTopologicalAddGroup
    (s : Finset PositiveArity) :
    IsTopologicalAddGroup (OSPositiveTimeOrderedFourDimensionalStage s) := by
  infer_instance

/-- Named jointly continuous complex scalar action on an exact finite source stage. -/
@[reducible]
noncomputable def osPositiveTimeOrderedFourDimensionalStageContinuousSMul
    (s : Finset PositiveArity) :
    ContinuousSMul ℂ (OSPositiveTimeOrderedFourDimensionalStage s) := by
  infer_instance

/-- Named real locally convex structure on an exact finite source stage. -/
@[reducible]
noncomputable def osPositiveTimeOrderedFourDimensionalStageLocallyConvexSpace
    (s : Finset PositiveArity) :
    LocallyConvexSpace ℝ (OSPositiveTimeOrderedFourDimensionalStage s) := by
  infer_instance

end

end YangMills
