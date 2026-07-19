/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Euclidean.OSOrderedFourDimensionalSourceSpace

/-!
# Named complex-module structures on exact OS source spaces

The exact positive-arity source predicate was proved equivalent to a complex Schwartz submodule.
This module packages that exact equivalence and transports the additive commutative group and
complex module structures to the source-space presentation. The structures are named rather than
global, matching the repository's controlled-instance policy.

No continuity, local convexity, sequence direct-sum identification, `(E2)`, or reconstruction is
asserted here.
-/

namespace YangMills

noncomputable section

namespace OSPositiveTimeOrderedFourDimensionalSourceSpace

/-- Exact algebraic equivalence between source-syntax membership and the established complex
Schwartz submodule. -/
def equivSubmodule (arity : PositiveArity) :
    OSPositiveTimeOrderedFourDimensionalSourceSpace arity ≃
      osPositiveTimeOrderedDerivativeSubmodule EuclideanDimension.four arity.value where
  toFun f := ⟨f.1,
    (osPositiveTimeOrderedFourDimensionalSourceTest_iff_frechet arity f.1).mp f.2⟩
  invFun f := ⟨f.1,
    (osPositiveTimeOrderedFourDimensionalSourceTest_iff_frechet arity f.1).mpr f.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Named additive commutative group transported from the exact Schwartz submodule. -/
@[reducible]
noncomputable def addCommGroup (arity : PositiveArity) :
    AddCommGroup (OSPositiveTimeOrderedFourDimensionalSourceSpace arity) :=
  Equiv.addCommGroup (equivSubmodule arity)

/-- Named complex module transported from the exact Schwartz submodule. Install the named additive
group locally first. -/
@[reducible]
noncomputable def module (arity : PositiveArity) :
    @Module ℂ (OSPositiveTimeOrderedFourDimensionalSourceSpace arity)
      Complex.instSemiring (addCommGroup arity).toAddCommMonoid :=
  Equiv.module ℂ (equivSubmodule arity)

/-- Transported zero has exactly the ambient zero Schwartz function. -/
theorem instance_zero_toSchwartz (arity : PositiveArity) :
    @toSchwartz arity (@OfNat.ofNat _ 0 (addCommGroup arity).toZero.toOfNat0) = 0 :=
  rfl

/-- Transported addition is exact ambient Schwartz addition. -/
theorem instance_add_toSchwartz (arity : PositiveArity)
    (f g : OSPositiveTimeOrderedFourDimensionalSourceSpace arity) :
    @toSchwartz arity (@Add.add _ (addCommGroup arity).toAdd f g) =
      f.toSchwartz + g.toSchwartz :=
  rfl

/-- Transported negation is exact ambient Schwartz negation. -/
theorem instance_neg_toSchwartz (arity : PositiveArity)
    (f : OSPositiveTimeOrderedFourDimensionalSourceSpace arity) :
    @toSchwartz arity (@Neg.neg _ (addCommGroup arity).toNeg f) = -f.toSchwartz :=
  rfl

/-- Transported complex scalar multiplication is exact ambient Schwartz scalar multiplication. -/
theorem instance_smul_toSchwartz (arity : PositiveArity) (c : ℂ)
    (f : OSPositiveTimeOrderedFourDimensionalSourceSpace arity) :
    @toSchwartz arity (@SMul.smul ℂ _ (module arity).toSMul c f) =
      c • f.toSchwartz :=
  rfl

end OSPositiveTimeOrderedFourDimensionalSourceSpace

end

end YangMills
