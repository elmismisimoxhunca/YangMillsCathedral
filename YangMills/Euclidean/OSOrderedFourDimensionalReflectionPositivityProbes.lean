/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Euclidean.OSOrderedFourDimensionalReflectionPositivity

/-!
# Hostile probes for exact-source reflection positivity

These probes lock the exact source carrier, unrestricted reflected-star convolution, positive-arity
content, strict-subdomain bridge, and real-valued positivity semantics. They do not construct a
positive Schwinger family or an OS reconstruction.
-/

namespace YangMills.OSOrderedFourDimensionalReflectionPositivity.Probes

open YangMills

/-- Forgetting source evidence keeps the scalar as the genuine zero-arity Schwartz function. -/
example (f : OSPositiveTimeOrderedFourDimensionalTestSequence) :
    f.toFiniteSchwartzSequence.component 0 =
      scalarZeroAritySchwartz EuclideanDimension.four f.zeroPoint :=
  rfl

/-- Forgetting source evidence keeps every exact positive-arity Schwartz component. -/
example (f : OSPositiveTimeOrderedFourDimensionalTestSequence) (arity : PositiveArity) :
    f.toFiniteSchwartzSequence.component arity.value =
      (f.component arity).toSchwartz :=
  f.extendedComponent_positive arity

/-- The concrete source bump remains genuinely positive-arity after forgetting source evidence. -/
theorem source_bump_positive_component_nonzero :
    singletonPositiveTimeBumpFourDimensionalOSSourceSequence.toFiniteSchwartzSequence.component 1 ≠
      0 := by
  change positiveTimeBumpSchwartz EuclideanDimension.four ≠ 0
  exact positiveTimeBumpSchwartz_ne_zero EuclideanDimension.four

/-- The source expression uses the exact unrestricted reflected-star convolution, not a stored
positivity bit. -/
example (family : ScalarSchwingerDistributionFamily EuclideanDimension.four)
    (f : OSPositiveTimeOrderedFourDimensionalTestSequence) :
    osSourceFourDimensionalReflectionPositivityExpression family f =
      finiteSequenceSchwingerEvaluation family
        (finiteSchwartzSequenceConvolution EuclideanDimension.four
          (finiteSchwartzSequenceReflectedStar EuclideanDimension.four
            f.toFiniteSchwartzSequence)
          f.toFiniteSchwartzSequence) :=
  rfl

/-- Source positivity retains the zero-imaginary-part obligation. -/
example {family : ScalarSchwingerDistributionFamily EuclideanDimension.four}
    (positive : OSSourceFourDimensionalReflectionPositivity family)
    (f : OSPositiveTimeOrderedFourDimensionalTestSequence) :
    (osSourceFourDimensionalReflectionPositivityExpression family f).im = 0 :=
  (positive f).imaginary_eq_zero

/-- Source positivity retains nonnegativity of the actual real part. -/
example {family : ScalarSchwingerDistributionFamily EuclideanDimension.four}
    (positive : OSSourceFourDimensionalReflectionPositivity family)
    (f : OSPositiveTimeOrderedFourDimensionalTestSequence) :
    0 ≤ (osSourceFourDimensionalReflectionPositivityExpression family f).re :=
  (positive f).real_nonnegative

/-- Restriction to the old strict carrier changes neither support nor any Schwartz component. -/
example (f : MathlibStrictPositiveTimeTestSequence EuclideanDimension.four) :
    f.toFourDimensionalOSSourceSequence.toFiniteSchwartzSequence =
      f.toFiniteSchwartzSequence :=
  OSPositiveTimeOrderedFourDimensionalTestSequence.toFiniteSchwartzSequence_ofStrict f

/-- Exact source positivity implies strict-subdomain positivity in the valid direction. -/
example {family : ScalarSchwingerDistributionFamily EuclideanDimension.four}
    (positive : OSSourceFourDimensionalReflectionPositivity family) :
    MathlibStrictScalarReflectionPositivity family :=
  positive.toMathlibStrict

/-- A nonzero imaginary value cannot be accepted as a nonnegative complex real. -/
theorem imaginary_positivity_blocked :
    ¬ IsNonnegativeComplexReal Complex.I := by
  intro accepted
  have impossible := accepted.imaginary_eq_zero
  norm_num at impossible

end YangMills.OSOrderedFourDimensionalReflectionPositivity.Probes
