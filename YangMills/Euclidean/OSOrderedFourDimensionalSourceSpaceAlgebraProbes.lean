/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Euclidean.OSOrderedFourDimensionalSourceSpaceAlgebra

/-!
# Hostile probes for exact OS source-space algebra

The probes ensure transported operations act on the same underlying Schwartz functions and do not
degenerate to disconnected algebraic data.
-/

namespace YangMills.OSOrderedFourDimensionalSourceSpaceAlgebra.Probes

noncomputable section

open OSPositiveTimeOrderedFourDimensionalSourceSpace

/-- Algebraic equivalence retains exactly the designated ambient Schwartz function. -/
theorem exact_submodule_equivalence
    (arity : PositiveArity)
    (f : OSPositiveTimeOrderedFourDimensionalSourceSpace arity) :
    (equivSubmodule arity f).1 = f.toSchwartz :=
  rfl

/-- Named zero, addition and negation are exact ambient operations. -/
theorem exact_additive_operations
    (arity : PositiveArity)
    (f g : OSPositiveTimeOrderedFourDimensionalSourceSpace arity) :
    @toSchwartz arity (@OfNat.ofNat _ 0 (addCommGroup arity).toZero.toOfNat0) = 0 ∧
      @toSchwartz arity (@Add.add _ (addCommGroup arity).toAdd f g) =
        f.toSchwartz + g.toSchwartz ∧
      @toSchwartz arity (@Neg.neg _ (addCommGroup arity).toNeg f) = -f.toSchwartz :=
  ⟨instance_zero_toSchwartz arity,
    instance_add_toSchwartz arity f g,
    instance_neg_toSchwartz arity f⟩

/-- Named scalar multiplication retains the exact complex scalar and source test. -/
theorem exact_scalar_action
    (arity : PositiveArity) (c : ℂ)
    (f : OSPositiveTimeOrderedFourDimensionalSourceSpace arity) :
    @toSchwartz arity (@SMul.smul ℂ _ (module arity).toSMul c f) =
      c • f.toSchwartz :=
  instance_smul_toSchwartz arity c f

/-- The explicit nonzero source test remains nonzero under the algebraic presentation. -/
theorem nonzero_source_test_retained :
    (equivSubmodule PositiveArity.one
      OSPositiveTimeOrderedFourDimensionalSourceSpace.positiveTimeBump).1 ≠ 0 := by
  change OSPositiveTimeOrderedFourDimensionalSourceSpace.positiveTimeBump.toSchwartz ≠ 0
  exact OSPositiveTimeOrderedFourDimensionalSourceSpace.positiveTimeBump_toSchwartz_ne_zero

end

end YangMills.OSOrderedFourDimensionalSourceSpaceAlgebra.Probes
