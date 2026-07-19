/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Euclidean.OSOrderedFourDimensionalSourceSpaceAlgebra

/-!
# Topological algebra on exact positive-arity OS source spaces

The exact source topology is induced from ambient complex Schwartz space, and the named algebraic
operations were proved to be the ambient Schwartz operations. This module packages named
continuity structures for addition, negation, and complex scalar multiplication and a named
topological additive-group structure.

The structures remain named rather than global. No source-sequence continuity, local convexity,
direct-sum identification, `(E2)`, or reconstruction is asserted here.
-/

namespace YangMills

noncomputable section

namespace OSPositiveTimeOrderedFourDimensionalSourceSpace

noncomputable local instance addCommGroupForTopology (arity : PositiveArity) :
    AddCommGroup (OSPositiveTimeOrderedFourDimensionalSourceSpace arity) :=
  addCommGroup arity

noncomputable local instance moduleForTopology (arity : PositiveArity) :
    Module ℂ (OSPositiveTimeOrderedFourDimensionalSourceSpace arity) :=
  module arity

/-- Named continuity of exact source-space addition for the induced Schwartz topology. -/
@[reducible]
noncomputable def continuousAdd (arity : PositiveArity) :
    ContinuousAdd (OSPositiveTimeOrderedFourDimensionalSourceSpace arity) where
  continuous_add := by
    rw [continuous_induced_rng]
    change Continuous (fun p :
      OSPositiveTimeOrderedFourDimensionalSourceSpace arity ×
        OSPositiveTimeOrderedFourDimensionalSourceSpace arity =>
          p.1.toSchwartz + p.2.toSchwartz)
    fun_prop

/-- Named continuity of exact source-space negation for the induced Schwartz topology. -/
@[reducible]
noncomputable def continuousNeg (arity : PositiveArity) :
    ContinuousNeg (OSPositiveTimeOrderedFourDimensionalSourceSpace arity) where
  continuous_neg := by
    rw [continuous_induced_rng]
    change Continuous (fun f : OSPositiveTimeOrderedFourDimensionalSourceSpace arity =>
      -f.toSchwartz)
    fun_prop

/-- Named topological additive-group structure. -/
@[reducible]
noncomputable def isTopologicalAddGroup (arity : PositiveArity) :
    IsTopologicalAddGroup (OSPositiveTimeOrderedFourDimensionalSourceSpace arity) := by
  letI : ContinuousAdd (OSPositiveTimeOrderedFourDimensionalSourceSpace arity) :=
    continuousAdd arity
  letI : ContinuousNeg (OSPositiveTimeOrderedFourDimensionalSourceSpace arity) :=
    continuousNeg arity
  exact { }

/-- Named continuity of exact complex scalar multiplication for the induced Schwartz topology. -/
@[reducible]
noncomputable def continuousSMul (arity : PositiveArity) :
    ContinuousSMul ℂ (OSPositiveTimeOrderedFourDimensionalSourceSpace arity) where
  continuous_smul := by
    rw [continuous_induced_rng]
    change Continuous (fun p : ℂ × OSPositiveTimeOrderedFourDimensionalSourceSpace arity =>
      p.1 • p.2.toSchwartz)
    fun_prop

end OSPositiveTimeOrderedFourDimensionalSourceSpace

end

end YangMills
