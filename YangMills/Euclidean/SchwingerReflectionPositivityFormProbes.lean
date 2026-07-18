/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Euclidean.SchwingerReflectionPositivityForm

/-!
# Hostile probes for the algebraic reflection-positivity form

These probes force zero-arity normalization, exact support evaluation, a genuinely nonzero strict
input, the order `(Θ f*) × f`, and both realness and nonnegativity. They assume the candidate
predicate only to inspect its consequences; they construct no reflection-positive family.
-/

namespace YangMills.Euclidean.SchwingerReflectionPositivityForm.Probes

/-- Evaluation of the unrestricted zero sequence is exactly zero. -/
theorem zero_sequence_evaluates_to_zero
    {d : EuclideanDimension} (family : ScalarSchwingerDistributionFamily d) :
    finiteSequenceSchwingerEvaluation family (zeroScalarFiniteSchwartzSequence d) = 0 :=
  finiteSequenceSchwingerEvaluation_zero family

/-- The actual arity-zero Schwartz unit evaluates to the normalized value one. -/
theorem scalar_unit_evaluates_to_one
    {d : EuclideanDimension} (family : ScalarSchwingerDistributionFamily d) :
    finiteSequenceSchwingerEvaluation family (scalarUnitFiniteSchwartzSequence d) = 1 :=
  finiteSequenceSchwingerEvaluation_unit family

/-- Finite evaluation reaches the concrete positive-arity component rather than retaining only the
normalized zero-point term. -/
theorem singleton_bump_evaluates_at_positive_arity
    (d : EuclideanDimension) (family : ScalarSchwingerDistributionFamily d) :
    finiteSequenceSchwingerEvaluation family
        (singletonPositiveTimeBumpSequence d).toFiniteSchwartzSequence =
      family.positivePoint PositiveArity.one (positiveTimeBumpSchwartz d) :=
  finiteSequenceSchwingerEvaluation_singletonPositiveTimeBump d family

/-- The positivity form has the exact source order: reflected star first, original sequence second. -/
theorem exact_reflected_star_convolution
    {d : EuclideanDimension} (family : ScalarSchwingerDistributionFamily d)
    (f : MathlibStrictPositiveTimeTestSequence d) :
    mathlibStrictReflectionPositivityExpression family f =
      finiteSequenceSchwingerEvaluation family
        (finiteSchwartzSequenceConvolution d
          (finiteSchwartzSequenceReflectedStar d f.toFiniteSchwartzSequence)
          f.toFiniteSchwartzSequence) :=
  rfl

/-- The quantified strict domain contains the explicit sequence with a nonzero arity-one bump. -/
theorem strict_domain_has_nonzero_bump
    (d : EuclideanDimension) :
    (singletonPositiveTimeBumpSequence d).component PositiveArity.one ≠ 0 := by
  rw [singletonPositiveTimeBumpSequence_component_one]
  exact positiveTimeBumpSchwartz_ne_zero d

/-- Candidate positivity specializes to the explicit nonzero bump input. -/
theorem candidate_forces_bump_nonnegative
    {d : EuclideanDimension} {family : ScalarSchwingerDistributionFamily d}
    (h : MathlibStrictScalarReflectionPositivity family) :
    IsNonnegativeComplexReal
      (mathlibStrictReflectionPositivityExpression family
        (singletonPositiveTimeBumpSequence d)) :=
  h (singletonPositiveTimeBumpSequence d)

/-- Candidate positivity cannot silently accept a nonzero imaginary bump-form value. -/
theorem imaginary_bump_value_blocked
    {d : EuclideanDimension} {family : ScalarSchwingerDistributionFamily d}
    (h : MathlibStrictScalarReflectionPositivity family)
    (hvalue : mathlibStrictReflectionPositivityExpression family
      (singletonPositiveTimeBumpSequence d) = Complex.I) : False := by
  have hreal := (candidate_forces_bump_nonnegative h).imaginary_eq_zero
  rw [hvalue] at hreal
  norm_num at hreal

/-- Candidate positivity cannot silently accept a negative real bump-form value. -/
theorem negative_bump_value_blocked
    {d : EuclideanDimension} {family : ScalarSchwingerDistributionFamily d}
    (h : MathlibStrictScalarReflectionPositivity family)
    (hvalue : mathlibStrictReflectionPositivityExpression family
      (singletonPositiveTimeBumpSequence d) = -1) : False := by
  have hnonnegative := (candidate_forces_bump_nonnegative h).real_nonnegative
  rw [hvalue] at hnonnegative
  norm_num at hnonnegative

/-- Exact support controls sequence evaluation; a purported extra omitted nonzero component is
incompatible with the carrier invariant before positivity is considered. -/
theorem omitted_evaluation_component_blocked
    {d : EuclideanDimension} (f : ScalarFiniteSchwartzSequence d) (n : ℕ)
    (hnotmem : n ∉ f.support) (hnonzero : f.component n ≠ 0) : False := by
  exact hnotmem ((f.mem_support_iff n).2 hnonzero)

end YangMills.Euclidean.SchwingerReflectionPositivityForm.Probes
