/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Euclidean.OSOrderedFourDimensionalFiniteStageTopology
import YangMills.Euclidean.OSOrderedFourDimensionalSourceSpaceAlgebra
import Mathlib.Data.DFinsupp.Defs

/-!
# Named complex-module structure on exact OS source sequences

An exact source sequence is algebraically equivalent to the product of its separate scalar
component with a dependent finitely supported family of exact positive-arity source tests. This
module constructs that equivalence and transports named additive-group and complex-module
structures to the sequence carrier. Every operation is proved exact on the scalar and underlying
Schwartz components.

The structures are named and not globally installed. No continuity, topological-vector-space
structure, local convexity, direct-sum identification, source product/involution, `(E2)`, or
reconstruction is asserted here.
-/

namespace YangMills

noncomputable section

noncomputable local instance osSourceSpaceAddCommGroupLocal (arity : PositiveArity) :
    AddCommGroup (OSPositiveTimeOrderedFourDimensionalSourceSpace arity) :=
  OSPositiveTimeOrderedFourDimensionalSourceSpace.addCommGroup arity

noncomputable local instance osSourceSpaceModuleLocal (arity : PositiveArity) :
    Module ℂ (OSPositiveTimeOrderedFourDimensionalSourceSpace arity) :=
  OSPositiveTimeOrderedFourDimensionalSourceSpace.module arity

/-- Dependent finitely supported positive-arity source-test family. -/
abbrev OSPositiveTimeOrderedFourDimensionalSourceDFinsupp :=
  Π₀ arity : PositiveArity, OSPositiveTimeOrderedFourDimensionalSourceSpace arity

/-- Exact algebraic coordinates: separate scalar plus finitely supported positive source tests. -/
abbrev OSPositiveTimeOrderedFourDimensionalSequenceCoordinates :=
  ℂ × OSPositiveTimeOrderedFourDimensionalSourceDFinsupp

/-- A source test is zero in its transported algebra exactly when its underlying Schwartz function
is zero. -/
theorem osPositiveTimeOrderedFourDimensionalSourceSpace_eq_zero_iff
    (arity : PositiveArity)
    (f : OSPositiveTimeOrderedFourDimensionalSourceSpace arity) :
    f.toSchwartz = 0 ↔ f = 0 := by
  constructor
  · intro h
    apply Subtype.ext
    change f.toSchwartz =
      @OSPositiveTimeOrderedFourDimensionalSourceSpace.toSchwartz arity 0
    rw [OSPositiveTimeOrderedFourDimensionalSourceSpace.instance_zero_toSchwartz]
    exact h
  · rintro rfl
    exact OSPositiveTimeOrderedFourDimensionalSourceSpace.instance_zero_toSchwartz arity

/-- Forget exact-support proofs into scalar-plus-DFinsupp coordinates. -/
def osPositiveTimeOrderedFourDimensionalSequenceToCoordinates
    (f : OSPositiveTimeOrderedFourDimensionalTestSequence) :
    OSPositiveTimeOrderedFourDimensionalSequenceCoordinates :=
  ⟨f.zeroPoint, {
    toFun := f.component
    support' := Trunc.mk ⟨f.support.1, fun arity => by
      by_cases h : arity ∈ f.support
      · exact Or.inl h
      · exact Or.inr
          ((osPositiveTimeOrderedFourDimensionalSourceSpace_eq_zero_iff
            arity (f.component arity)).mp
            (f.component_toSchwartz_eq_zero_of_not_mem arity h))⟩ }⟩

/-- Recover an exact-support source sequence from scalar-plus-DFinsupp coordinates. -/
def osPositiveTimeOrderedFourDimensionalCoordinatesToSequence
    (x : OSPositiveTimeOrderedFourDimensionalSequenceCoordinates) :
    OSPositiveTimeOrderedFourDimensionalTestSequence := by
  classical
  exact {
    zeroPoint := x.1
    support := x.2.support
    component := x.2
    mem_support_iff := by
      intro arity
      rw [DFinsupp.mem_support_iff]
      constructor
      · intro h hzero
        exact h ((osPositiveTimeOrderedFourDimensionalSourceSpace_eq_zero_iff
          arity (x.2 arity)).mp hzero)
      · intro h hzero
        exact h ((osPositiveTimeOrderedFourDimensionalSourceSpace_eq_zero_iff
          arity (x.2 arity)).mpr hzero) }

/-- Exact algebraic equivalence between source sequences and scalar-plus-DFinsupp coordinates. -/
def osPositiveTimeOrderedFourDimensionalSequenceCoordinatesEquiv :
    OSPositiveTimeOrderedFourDimensionalTestSequence ≃
      OSPositiveTimeOrderedFourDimensionalSequenceCoordinates where
  toFun := osPositiveTimeOrderedFourDimensionalSequenceToCoordinates
  invFun := osPositiveTimeOrderedFourDimensionalCoordinatesToSequence
  left_inv f := by
    apply OSPositiveTimeOrderedFourDimensionalTestSequence.ext
    · rfl
    · intro arity
      rfl
  right_inv x := by
    apply Prod.ext
    · rfl
    · apply DFinsupp.ext
      intro arity
      rfl

/-- Named additive commutative group transported from scalar-plus-DFinsupp coordinates. -/
@[reducible]
noncomputable def osPositiveTimeOrderedFourDimensionalSequenceAddCommGroup :
    AddCommGroup OSPositiveTimeOrderedFourDimensionalTestSequence :=
  Equiv.addCommGroup osPositiveTimeOrderedFourDimensionalSequenceCoordinatesEquiv

/-- Named complex module transported from scalar-plus-DFinsupp coordinates. Install the named
additive group locally first. -/
@[reducible]
noncomputable def osPositiveTimeOrderedFourDimensionalSequenceModule :
    @Module ℂ OSPositiveTimeOrderedFourDimensionalTestSequence Complex.instSemiring
      osPositiveTimeOrderedFourDimensionalSequenceAddCommGroup.toAddCommMonoid :=
  Equiv.module ℂ osPositiveTimeOrderedFourDimensionalSequenceCoordinatesEquiv

/-- Transported zero has scalar zero. -/
theorem osPositiveTimeOrderedFourDimensionalSequence_instance_zeroPoint :
    (@OfNat.ofNat _ 0
      osPositiveTimeOrderedFourDimensionalSequenceAddCommGroup.toZero.toOfNat0).zeroPoint = 0 :=
  rfl

/-- Transported zero has zero at every positive-arity Schwartz component. -/
theorem osPositiveTimeOrderedFourDimensionalSequence_instance_zero_component
    (arity : PositiveArity) :
    ((@OfNat.ofNat _ 0
      osPositiveTimeOrderedFourDimensionalSequenceAddCommGroup.toZero.toOfNat0).component
        arity).toSchwartz = 0 :=
  rfl

/-- Transported addition is exact scalar addition. -/
theorem osPositiveTimeOrderedFourDimensionalSequence_instance_add_zeroPoint
    (f g : OSPositiveTimeOrderedFourDimensionalTestSequence) :
    (@Add.add _ osPositiveTimeOrderedFourDimensionalSequenceAddCommGroup.toAdd f g).zeroPoint =
      f.zeroPoint + g.zeroPoint :=
  rfl

/-- Transported addition is exact ambient Schwartz addition at every positive arity. -/
theorem osPositiveTimeOrderedFourDimensionalSequence_instance_add_component
    (f g : OSPositiveTimeOrderedFourDimensionalTestSequence) (arity : PositiveArity) :
    ((@Add.add _ osPositiveTimeOrderedFourDimensionalSequenceAddCommGroup.toAdd f g).component
      arity).toSchwartz =
        (f.component arity).toSchwartz + (g.component arity).toSchwartz :=
  rfl

/-- Transported complex scalar multiplication is exact on the separate scalar. -/
theorem osPositiveTimeOrderedFourDimensionalSequence_instance_smul_zeroPoint
    (c : ℂ) (f : OSPositiveTimeOrderedFourDimensionalTestSequence) :
    (@SMul.smul ℂ _ osPositiveTimeOrderedFourDimensionalSequenceModule.toSMul c f).zeroPoint =
      c * f.zeroPoint :=
  rfl

/-- Transported complex scalar multiplication is exact at every positive-arity Schwartz component. -/
theorem osPositiveTimeOrderedFourDimensionalSequence_instance_smul_component
    (c : ℂ) (f : OSPositiveTimeOrderedFourDimensionalTestSequence)
    (arity : PositiveArity) :
    ((@SMul.smul ℂ _ osPositiveTimeOrderedFourDimensionalSequenceModule.toSMul c f).component
      arity).toSchwartz = c • (f.component arity).toSchwartz :=
  rfl

end

end YangMills
