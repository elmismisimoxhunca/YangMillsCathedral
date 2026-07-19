/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Euclidean.OSOrderedFourDimensionalMultiIndexPermutation
import YangMills.Euclidean.OSOrderedDerivativeClosed

/-!
# Exact four-dimensional OS-I ordered positive-arity source spaces

Osterwalder–Schrader I, printed p. 86, writes
`D^α = (∂/∂x₁)^{α₁} ⋯ (∂/∂x_{4n})^{α_{4n}}` and defines the closed ordered
subspaces by requiring every such partial derivative to vanish unless
`s < x₁⁰ < ⋯ < xₙ⁰ < t`; `𝒮₊` is the case `(s,t) = (0,∞)`.

The preceding modules established every ingredient needed to interpret this notation exactly for
smooth Schwartz functions: point-major flattening of `x₁,…,xₙ`, natural coordinate
multiplicities, exact occurrence enumeration, recovery of arbitrary ordered coordinate tuples, and
permutation independence of iterated directional derivatives. This module therefore names the
canonical repeated-coordinate evaluation as the formal `D^α` interpretation and proves its
positive-arity vanishing predicate equivalent to the existing Fréchet candidate. It transports the
previously proved closedness and packages the exact induced Schwartz topology at every positive
arity. OS-I's separate scalar zero-point sequence component is deliberately not represented by this
source-space subtype.

These are only the positive-arity ordered source spaces. It does not settle whether the earlier strict
support carrier is sufficient/dense, identify the finite-sequence topology with OS-I's locally
convex direct sum, construct the distinct completed positive-half-space tensor product, state
source-facing `(E2)`, supply OS-II growth, or prove reconstruction. No theory inhabitant, existence
claim, or mass gap is asserted.
-/

namespace YangMills

open Set

noncomputable section

/-- Formal interpretation of OS-I's four-dimensional coordinate operator `D^α`: evaluate the
`|α|`-fold real Fréchet derivative on the canonical tuple in which flattened coordinate `i` occurs
exactly `αᵢ` times. Proven permutation independence makes the chosen occurrence ordering
irrelevant. -/
def fourDimensionalOSMultiIndexPartialDerivative
    (arity : PositiveArity) (α : FourDimensionalMultiIndex arity.value)
    (f : ScalarSchwartzTestFunction EuclideanDimension.four arity.value)
    (x : EuclideanNPointSpace EuclideanDimension.four arity.value) : ℂ :=
  fourDimensionalMultiIndexDerivative α f x

/-- Exact expansion of the source-facing partial derivative into the established iterated Fréchet
derivative and repeated coordinate-basis tuple. -/
@[simp]
theorem fourDimensionalOSMultiIndexPartialDerivative_apply
    (arity : PositiveArity) (α : FourDimensionalMultiIndex arity.value)
    (f : ScalarSchwartzTestFunction EuclideanDimension.four arity.value)
    (x : EuclideanNPointSpace EuclideanDimension.four arity.value) :
    fourDimensionalOSMultiIndexPartialDerivative arity α f x =
      iteratedFDeriv ℝ (fourDimensionalMultiIndexOrder α)
        (f : EuclideanNPointSpace EuclideanDimension.four arity.value → ℂ) x
        (fourDimensionalMultiIndexDirections α) :=
  rfl

/-- The source-facing `D^α` value agrees with every exact occurrence enumeration, not only the
canonical ordering. -/
theorem fourDimensionalOSMultiIndexPartialDerivative_eq_enumerated
    (arity : PositiveArity) {k : ℕ} {α : FourDimensionalMultiIndex arity.value}
    (enumeration : FourDimensionalMultiIndexEnumeration α k)
    (f : ScalarSchwartzTestFunction EuclideanDimension.four arity.value)
    (x : EuclideanNPointSpace EuclideanDimension.four arity.value) :
    fourDimensionalOSMultiIndexPartialDerivative arity α f x =
      fourDimensionalEnumeratedMultiIndexDerivative enumeration f x :=
  (fourDimensionalEnumeratedMultiIndexDerivative_eq_canonical enumeration f x).symm

/-- Exact four-dimensional positive-arity OS-I `𝒮₊` membership predicate: all interpreted `D^α`
derivatives vanish outside strict positive time order. OS-I keeps the scalar zero-point component
separate, so this source-facing predicate is indexed by `PositiveArity`. -/
def IsOSPositiveTimeOrderedFourDimensionalSourceTest
    (arity : PositiveArity)
    (f : ScalarSchwartzTestFunction EuclideanDimension.four arity.value) : Prop :=
  ∀ α : FourDimensionalMultiIndex arity.value,
    ∀ x : EuclideanNPointSpace EuclideanDimension.four arity.value,
      x ∉ strictPositiveTimeOrderedConfigurationSet EuclideanDimension.four arity.value →
        fourDimensionalOSMultiIndexPartialDerivative arity α f x = 0

/-- Exact positive-arity source-syntax membership is equivalent to the coordinate-free Fréchet
predicate. -/
theorem osPositiveTimeOrderedFourDimensionalSourceTest_iff_frechet
    (arity : PositiveArity)
    (f : ScalarSchwartzTestFunction EuclideanDimension.four arity.value) :
    IsOSPositiveTimeOrderedFourDimensionalSourceTest arity f ↔
      IsOSPositiveTimeOrderedDerivativeVanishing f := by
  change IsOSPositiveTimeOrderedMultiIndexVanishing f ↔ _
  exact (osPositiveTimeOrderedFrechet_iff_canonicalMultiIndex f).symm

/-- The exact four-dimensional positive-arity OS-I source carrier is closed in ambient Schwartz
space. -/
theorem isClosed_osPositiveTimeOrderedFourDimensionalSourceTest (arity : PositiveArity) :
    IsClosed {f : ScalarSchwartzTestFunction EuclideanDimension.four arity.value |
      IsOSPositiveTimeOrderedFourDimensionalSourceTest arity f} := by
  have heq : {f : ScalarSchwartzTestFunction EuclideanDimension.four arity.value |
      IsOSPositiveTimeOrderedFourDimensionalSourceTest arity f} =
      ((osPositiveTimeOrderedDerivativeSubmodule EuclideanDimension.four arity.value :
        Submodule ℂ (ScalarSchwartzTestFunction EuclideanDimension.four arity.value)) : Set _) := by
    ext f
    exact osPositiveTimeOrderedFourDimensionalSourceTest_iff_frechet arity f
  rw [heq]
  exact isClosed_osPositiveTimeOrderedDerivativeSubmodule EuclideanDimension.four arity.value

/-- Exact four-dimensional, positive-arity OS-I ordered source space with its source membership law.
The scalar arity-zero sequence component remains separate. -/
def OSPositiveTimeOrderedFourDimensionalSourceSpace (arity : PositiveArity) :=
  {f : ScalarSchwartzTestFunction EuclideanDimension.four arity.value //
    IsOSPositiveTimeOrderedFourDimensionalSourceTest arity f}

namespace OSPositiveTimeOrderedFourDimensionalSourceSpace

/-- Forgetful map to the exact ambient Mathlib Schwartz function. -/
def toSchwartz {arity : PositiveArity}
    (f : OSPositiveTimeOrderedFourDimensionalSourceSpace arity) :
    ScalarSchwartzTestFunction EuclideanDimension.four arity.value :=
  f.1

instance {arity : PositiveArity} : Coe (OSPositiveTimeOrderedFourDimensionalSourceSpace arity)
    (ScalarSchwartzTestFunction EuclideanDimension.four arity.value) :=
  ⟨toSchwartz⟩

/-- Exact topology induced at each positive arity from ambient Schwartz space, as specified on OS-I
p. 86. -/
instance {arity : PositiveArity} : TopologicalSpace
    (OSPositiveTimeOrderedFourDimensionalSourceSpace arity) :=
  TopologicalSpace.induced toSchwartz inferInstance

/-- The exact source-syntax and Fréchet presentations preserve the same underlying Schwartz test. -/
def equivFrechetCarrier {arity : PositiveArity} :
    OSPositiveTimeOrderedFourDimensionalSourceSpace arity ≃
      OSPositiveTimeOrderedDerivativeCarrier EuclideanDimension.four arity.value where
  toFun f := ⟨f.1,
    (osPositiveTimeOrderedFourDimensionalSourceTest_iff_frechet arity f.1).mp f.2⟩
  invFun f := ⟨f.1,
    (osPositiveTimeOrderedFourDimensionalSourceTest_iff_frechet arity f.1).mpr f.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The positive-arity source-space forgetful map is a closed topological embedding. -/
theorem closedEmbedding_toSchwartz (arity : PositiveArity) :
    Topology.IsClosedEmbedding
      (toSchwartz : OSPositiveTimeOrderedFourDimensionalSourceSpace arity →
        ScalarSchwartzTestFunction EuclideanDimension.four arity.value) := by
  exact (isClosed_osPositiveTimeOrderedFourDimensionalSourceTest arity).isClosedEmbedding_subtypeVal

/-- The explicit strict positive-time bump supplies a genuine nonzero source-space element at
positive arity one. -/
def positiveTimeBump : OSPositiveTimeOrderedFourDimensionalSourceSpace PositiveArity.one := by
  let candidate := OSPositiveTimeOrderedDerivativeCarrier.positiveTimeBump
    EuclideanDimension.four
  exact ⟨candidate.toSchwartz,
    (osPositiveTimeOrderedFourDimensionalSourceTest_iff_frechet PositiveArity.one
      candidate.toSchwartz).mpr candidate.2⟩

/-- The source-space bump remains nonzero in ambient Schwartz space. -/
theorem positiveTimeBump_toSchwartz_ne_zero :
    toSchwartz positiveTimeBump ≠ 0 :=
  OSPositiveTimeOrderedDerivativeCarrier.positiveTimeBump_toSchwartz_ne_zero
    EuclideanDimension.four

end OSPositiveTimeOrderedFourDimensionalSourceSpace

end

end YangMills
