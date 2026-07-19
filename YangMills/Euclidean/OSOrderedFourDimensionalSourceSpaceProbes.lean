/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Euclidean.OSOrderedFourDimensionalSourceSpace

/-!
# Hostile probes for exact four-dimensional OS-I positive-arity source spaces

These probes lock the named `D^α` interpretation, exact source membership, closed induced topology,
four-dimensional and positive-arity scope, and nonzero content. They do not conflate the per-arity space with OS-I's
finite direct sum, completed positive-half-space tensor product, `(E2)`, or reconstruction theorem.
-/

namespace YangMills.OSOrderedFourDimensionalSourceSpace.Probes

open Set

noncomputable section

/-- The named positive-arity source partial derivative is exactly the repeated-coordinate Fréchet
value, not an unrelated or constant-zero field. -/
theorem exact_source_partial_derivative
    (arity : PositiveArity) (α : FourDimensionalMultiIndex arity.value)
    (f : ScalarSchwartzTestFunction EuclideanDimension.four arity.value)
    (x : EuclideanNPointSpace EuclideanDimension.four arity.value) :
    fourDimensionalOSMultiIndexPartialDerivative arity α f x =
      iteratedFDeriv ℝ (fourDimensionalMultiIndexOrder α)
        (f : EuclideanNPointSpace EuclideanDimension.four arity.value → ℂ) x
        (fourDimensionalMultiIndexDirections α) :=
  fourDimensionalOSMultiIndexPartialDerivative_apply arity α f x

/-- Every occurrence enumeration computes the same exact positive-arity source partial derivative. -/
theorem exact_enumerated_source_partial_derivative
    (arity : PositiveArity) {k : ℕ} {α : FourDimensionalMultiIndex arity.value}
    (enumeration : FourDimensionalMultiIndexEnumeration α k)
    (f : ScalarSchwartzTestFunction EuclideanDimension.four arity.value)
    (x : EuclideanNPointSpace EuclideanDimension.four arity.value) :
    fourDimensionalOSMultiIndexPartialDerivative arity α f x =
      fourDimensionalEnumeratedMultiIndexDerivative enumeration f x :=
  fourDimensionalOSMultiIndexPartialDerivative_eq_enumerated arity enumeration f x

/-- Positive-arity source-syntax membership and the established Fréchet carrier are exactly
equivalent on the same Schwartz test. -/
theorem exact_source_frechet_membership
    (arity : PositiveArity)
    (f : ScalarSchwartzTestFunction EuclideanDimension.four arity.value) :
    IsOSPositiveTimeOrderedFourDimensionalSourceTest arity f ↔
      IsOSPositiveTimeOrderedDerivativeVanishing f :=
  osPositiveTimeOrderedFourDimensionalSourceTest_iff_frechet arity f

/-- The exact positive-arity source carrier is closed in the actual ambient Schwartz topology. -/
theorem exact_source_carrier_closed (arity : PositiveArity) :
    IsClosed {f : ScalarSchwartzTestFunction EuclideanDimension.four arity.value |
      IsOSPositiveTimeOrderedFourDimensionalSourceTest arity f} :=
  isClosed_osPositiveTimeOrderedFourDimensionalSourceTest arity

/-- The positive-arity source-space subtype uses the exact induced topology and has closed image. -/
theorem exact_closed_embedding (arity : PositiveArity) :
    Topology.IsClosedEmbedding
      (OSPositiveTimeOrderedFourDimensionalSourceSpace.toSchwartz :
        OSPositiveTimeOrderedFourDimensionalSourceSpace arity →
          ScalarSchwartzTestFunction EuclideanDimension.four arity.value) :=
  OSPositiveTimeOrderedFourDimensionalSourceSpace.closedEmbedding_toSchwartz arity

/-- A nonzero interpreted `D^α` value outside strict order blocks every positive-arity source-space
surrogate with the same underlying Schwartz function. -/
theorem nonzero_source_partial_derivative_blocks_carrier
    (arity : PositiveArity)
    (f : ScalarSchwartzTestFunction EuclideanDimension.four arity.value)
    (α : FourDimensionalMultiIndex arity.value)
    (x : EuclideanNPointSpace EuclideanDimension.four arity.value)
    (hx : x ∉ strictPositiveTimeOrderedConfigurationSet EuclideanDimension.four arity.value)
    (hne : fourDimensionalOSMultiIndexPartialDerivative arity α f x ≠ 0) :
    ¬ ∃ accepted : OSPositiveTimeOrderedFourDimensionalSourceSpace arity,
      accepted.toSchwartz = f := by
  rintro ⟨accepted, equality⟩
  apply hne
  rw [← equality]
  exact accepted.2 α x hx

/-- The explicit nonzero positive-arity-one element blocks empty and zero-only source-space
replacements. -/
theorem nonzero_source_test_exists :
    ∃ f : OSPositiveTimeOrderedFourDimensionalSourceSpace PositiveArity.one,
      f.toSchwartz ≠ 0 :=
  ⟨OSPositiveTimeOrderedFourDimensionalSourceSpace.positiveTimeBump,
    OSPositiveTimeOrderedFourDimensionalSourceSpace.positiveTimeBump_toSchwartz_ne_zero⟩

end

end YangMills.OSOrderedFourDimensionalSourceSpace.Probes
