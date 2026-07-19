/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Euclidean.OSOrderedFourDimensionalSequenceAlgebra

/-!
# Hostile probes for exact OS source-sequence algebra

The probes lock scalar-plus-DFinsupp coordinates and transported operations to the exact same scalar
and positive-arity Schwartz components, including designated zero and nonzero source sequences.
-/

namespace YangMills.OSOrderedFourDimensionalSequenceAlgebra.Probes

noncomputable section

/-- Coordinate equivalence retains the exact scalar and every source component. -/
theorem exact_sequence_coordinates
    (f : OSPositiveTimeOrderedFourDimensionalTestSequence)
    (arity : PositiveArity) :
    (osPositiveTimeOrderedFourDimensionalSequenceCoordinatesEquiv f).1 = f.zeroPoint ∧
      ((osPositiveTimeOrderedFourDimensionalSequenceCoordinatesEquiv f).2 arity).toSchwartz =
        (f.component arity).toSchwartz :=
  ⟨rfl, rfl⟩

/-- Algebraic zero is exactly the previously designated all-zero source sequence. -/
theorem algebraic_zero_eq_designated_zero :
    @OfNat.ofNat _ 0
      osPositiveTimeOrderedFourDimensionalSequenceAddCommGroup.toZero.toOfNat0 =
        zeroOSPositiveTimeOrderedFourDimensionalTestSequence := by
  apply OSPositiveTimeOrderedFourDimensionalTestSequence.ext
  · exact osPositiveTimeOrderedFourDimensionalSequence_instance_zeroPoint
  · intro arity
    exact osPositiveTimeOrderedFourDimensionalSequence_instance_zero_component arity

/-- Addition preserves the exact scalar and every underlying positive Schwartz component. -/
theorem exact_addition
    (f g : OSPositiveTimeOrderedFourDimensionalTestSequence)
    (arity : PositiveArity) :
    (@Add.add _ osPositiveTimeOrderedFourDimensionalSequenceAddCommGroup.toAdd f g).zeroPoint =
        f.zeroPoint + g.zeroPoint ∧
      ((@Add.add _ osPositiveTimeOrderedFourDimensionalSequenceAddCommGroup.toAdd f g).component
        arity).toSchwartz =
          (f.component arity).toSchwartz + (g.component arity).toSchwartz :=
  ⟨osPositiveTimeOrderedFourDimensionalSequence_instance_add_zeroPoint f g,
    osPositiveTimeOrderedFourDimensionalSequence_instance_add_component f g arity⟩

/-- Scalar multiplication preserves the exact complex scalar and every positive Schwartz component. -/
theorem exact_scalar_action
    (c : ℂ) (f : OSPositiveTimeOrderedFourDimensionalTestSequence)
    (arity : PositiveArity) :
    (@SMul.smul ℂ _ osPositiveTimeOrderedFourDimensionalSequenceModule.toSMul c f).zeroPoint =
        c * f.zeroPoint ∧
      ((@SMul.smul ℂ _ osPositiveTimeOrderedFourDimensionalSequenceModule.toSMul c f).component
        arity).toSchwartz = c • (f.component arity).toSchwartz :=
  ⟨osPositiveTimeOrderedFourDimensionalSequence_instance_smul_zeroPoint c f,
    osPositiveTimeOrderedFourDimensionalSequence_instance_smul_component c f arity⟩

/-- The explicit nonzero singleton remains visible in algebraic coordinates. -/
theorem nonzero_singleton_retained :
    ((osPositiveTimeOrderedFourDimensionalSequenceCoordinatesEquiv
      singletonPositiveTimeBumpFourDimensionalOSSourceSequence).2
        PositiveArity.one).toSchwartz ≠ 0 := by
  change (singletonPositiveTimeBumpFourDimensionalOSSourceSequence.component
    PositiveArity.one).toSchwartz ≠ 0
  rw [singletonPositiveTimeBumpFourDimensionalOSSourceSequence,
    MathlibStrictPositiveTimeTestSequence.toFourDimensionalOSSourceSequence_component,
    singletonPositiveTimeBumpSequence_component_one]
  exact positiveTimeBumpSchwartz_ne_zero EuclideanDimension.four

end

end YangMills.OSOrderedFourDimensionalSequenceAlgebra.Probes
