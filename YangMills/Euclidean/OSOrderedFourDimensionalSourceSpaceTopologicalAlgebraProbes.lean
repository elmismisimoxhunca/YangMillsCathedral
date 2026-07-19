/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Euclidean.OSOrderedFourDimensionalSourceSpaceTopologicalAlgebra

/-!
# Hostile probes for exact OS source-space topological algebra

The probes tie continuity to the exact named operations and induced Schwartz topology while
retaining the explicit nonzero source test.
-/

namespace YangMills.OSOrderedFourDimensionalSourceSpaceTopologicalAlgebra.Probes

noncomputable section

open OSPositiveTimeOrderedFourDimensionalSourceSpace

noncomputable local instance sourceAddCommGroupForProbes (arity : PositiveArity) :
    AddCommGroup (OSPositiveTimeOrderedFourDimensionalSourceSpace arity) :=
  addCommGroup arity

noncomputable local instance sourceModuleForProbes (arity : PositiveArity) :
    Module ℂ (OSPositiveTimeOrderedFourDimensionalSourceSpace arity) :=
  module arity

/-- The named aggregate supplies both addition and negation continuity. -/
theorem exact_named_topological_add_group (arity : PositiveArity) :
    Continuous (fun p : OSPositiveTimeOrderedFourDimensionalSourceSpace arity ×
      OSPositiveTimeOrderedFourDimensionalSourceSpace arity => p.1 + p.2) ∧
    Continuous (fun f : OSPositiveTimeOrderedFourDimensionalSourceSpace arity => -f) := by
  letI : IsTopologicalAddGroup (OSPositiveTimeOrderedFourDimensionalSourceSpace arity) :=
    isTopologicalAddGroup arity
  exact ⟨continuous_add, continuous_neg⟩

noncomputable local instance sourceContinuousAddForProbes (arity : PositiveArity) :
    ContinuousAdd (OSPositiveTimeOrderedFourDimensionalSourceSpace arity) :=
  continuousAdd arity

noncomputable local instance sourceContinuousNegForProbes (arity : PositiveArity) :
    ContinuousNeg (OSPositiveTimeOrderedFourDimensionalSourceSpace arity) :=
  continuousNeg arity

noncomputable local instance sourceContinuousSMulForProbes (arity : PositiveArity) :
    ContinuousSMul ℂ (OSPositiveTimeOrderedFourDimensionalSourceSpace arity) :=
  continuousSMul arity

/-- Exact named addition is jointly continuous. -/
theorem exact_continuous_add (arity : PositiveArity) :
    Continuous (fun p : OSPositiveTimeOrderedFourDimensionalSourceSpace arity ×
      OSPositiveTimeOrderedFourDimensionalSourceSpace arity => p.1 + p.2) :=
  continuous_add

/-- Exact named negation is continuous. -/
theorem exact_continuous_neg (arity : PositiveArity) :
    Continuous (fun f : OSPositiveTimeOrderedFourDimensionalSourceSpace arity => -f) :=
  continuous_neg

/-- Exact named complex scalar multiplication is jointly continuous. -/
theorem exact_continuous_smul (arity : PositiveArity) :
    Continuous (fun p : ℂ × OSPositiveTimeOrderedFourDimensionalSourceSpace arity =>
      p.1 • p.2) :=
  continuous_smul

/-- Continuity structures do not collapse the explicit nonzero source test. -/
theorem nonzero_source_test_retained :
    OSPositiveTimeOrderedFourDimensionalSourceSpace.positiveTimeBump.toSchwartz ≠ 0 :=
  OSPositiveTimeOrderedFourDimensionalSourceSpace.positiveTimeBump_toSchwartz_ne_zero

end

end YangMills.OSOrderedFourDimensionalSourceSpaceTopologicalAlgebra.Probes
