/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Euclidean.SchwingerConvolutionSequence
import YangMills.Euclidean.SchwingerSequenceInvolution

/-!
# Algebraic scalar reflection-positivity form

Osterwalder–Schrader I `(E2)` evaluates the Schwinger family on `(Θ f*) × f` and requires the result
to be a nonnegative real number. This module wires that exact algebraic expression on the project's
strict positive-time ordered/flat Mathlib test sequences.

The resulting predicate is deliberately named `MathlibStrictScalarReflectionPositivity`, not
`OSIReflectionPositivity`: the strict topological-support carrier is stronger than OS-I's printed
derivative-vanishing carrier, and the comparison plus induced/direct-sum/completed-tensor topology
bridges remain unproved. No inhabitant of the predicate is constructed.
-/

namespace YangMills

/-- The zero-point Schwinger functional on the actual zero-arity Schwartz representation. -/
noncomputable def zeroAritySchwingerLinear
    {d : EuclideanDimension} (family : ScalarSchwingerDistributionFamily d) :
    ScalarSchwartzTestFunction d 0 →ₗ[ℂ] ℂ where
  toFun f := family.zeroPoint * f (fun i => Fin.elim0 i)
  map_add' f g := by
    change family.zeroPoint * (f _ + g _) = _
    ring
  map_smul' c f := by
    change family.zeroPoint * (c * f _) = c * (family.zeroPoint * f _)
    ring

@[simp] theorem zeroAritySchwingerLinear_apply
    {d : EuclideanDimension} (family : ScalarSchwingerDistributionFamily d)
    (f : ScalarSchwartzTestFunction d 0) :
    zeroAritySchwingerLinear family f =
      family.zeroPoint * f (fun i => Fin.elim0 i) :=
  rfl

/-- The normalized family as one algebraic linear functional at every natural arity. -/
noncomputable def schwingerDistributionAtNaturalArity
    {d : EuclideanDimension} (family : ScalarSchwingerDistributionFamily d)
    (n : ℕ) : ScalarSchwartzTestFunction d n →ₗ[ℂ] ℂ :=
  match n with
  | 0 => zeroAritySchwingerLinear family
  | k + 1 => (family.positivePoint ⟨k + 1, Nat.zero_lt_succ k⟩).toLinearMap

@[simp] theorem schwingerDistributionAtNaturalArity_zero
    {d : EuclideanDimension} (family : ScalarSchwingerDistributionFamily d)
    (f : ScalarSchwartzTestFunction d 0) :
    schwingerDistributionAtNaturalArity family 0 f =
      family.zeroPoint * f (fun i => Fin.elim0 i) :=
  rfl

@[simp] theorem schwingerDistributionAtNaturalArity_succ
    {d : EuclideanDimension} (family : ScalarSchwingerDistributionFamily d)
    (k : ℕ) (f : ScalarSchwartzTestFunction d (k + 1)) :
    schwingerDistributionAtNaturalArity family (k + 1) f =
      family.positivePoint ⟨k + 1, Nat.zero_lt_succ k⟩ f :=
  rfl

/-- Evaluation of a normalized Schwinger family on an unrestricted finite sequence. The exact
support finset controls precisely which natural-arity functionals are summed. -/
noncomputable def finiteSequenceSchwingerEvaluation
    {d : EuclideanDimension} (family : ScalarSchwingerDistributionFamily d)
    (f : ScalarFiniteSchwartzSequence d) : ℂ :=
  ∑ n ∈ f.support, schwingerDistributionAtNaturalArity family n (f.component n)

@[simp] theorem finiteSequenceSchwingerEvaluation_zero
    {d : EuclideanDimension} (family : ScalarSchwingerDistributionFamily d) :
    finiteSequenceSchwingerEvaluation family (zeroScalarFiniteSchwartzSequence d) = 0 := by
  simp [finiteSequenceSchwingerEvaluation, zeroScalarFiniteSchwartzSequence]

/-- Normalization at arity zero makes evaluation of the scalar sequence unit exactly one. -/
@[simp] theorem finiteSequenceSchwingerEvaluation_unit
    {d : EuclideanDimension} (family : ScalarSchwingerDistributionFamily d) :
    finiteSequenceSchwingerEvaluation family (scalarUnitFiniteSchwartzSequence d) = 1 := by
  simp [finiteSequenceSchwingerEvaluation, scalarUnitFiniteSchwartzSequence,
    MathlibStrictPositiveTimeTestSequence.naturalSupport,
    unitZeroPointTestSequence, schwingerDistributionAtNaturalArity,
    zeroAritySchwingerLinear, family.zeroPoint_normalized]

/-- Evaluation of the explicit positive-arity singleton is the actual arity-one distribution,
so finite evaluation cannot silently retain only the zero-point term. -/
theorem finiteSequenceSchwingerEvaluation_singletonPositiveTimeBump
    (d : EuclideanDimension) (family : ScalarSchwingerDistributionFamily d) :
    finiteSequenceSchwingerEvaluation family
        (singletonPositiveTimeBumpSequence d).toFiniteSchwartzSequence =
      family.positivePoint PositiveArity.one (positiveTimeBumpSchwartz d) := by
  have hone : (⟨1, Nat.zero_lt_succ 0⟩ : PositiveArity) = PositiveArity.one :=
    PositiveArity.ext rfl
  simp [hone, finiteSequenceSchwingerEvaluation,
    MathlibStrictPositiveTimeTestSequence.naturalSupport,
    singletonPositiveTimeBumpSequence, singletonPositiveTimeBumpComponent,
    schwingerDistributionAtNaturalArity]
  congr 2

/-- A complex number regarded as an actual nonnegative real: its imaginary part vanishes and its
real part is nonnegative. -/
structure IsNonnegativeComplexReal (z : ℂ) : Prop where
  /-- Positivity cannot silently discard a nonzero imaginary part. -/
  imaginary_eq_zero : z.im = 0
  /-- The remaining real value is nonnegative. -/
  real_nonnegative : 0 ≤ z.re

@[simp] theorem zero_isNonnegativeComplexReal :
    IsNonnegativeComplexReal 0 :=
  ⟨by simp, by simp⟩

/-- The exact algebraic `(Θ f*) × f` Schwinger evaluation on the strict Mathlib domain. -/
noncomputable def mathlibStrictReflectionPositivityExpression
    {d : EuclideanDimension} (family : ScalarSchwingerDistributionFamily d)
    (f : MathlibStrictPositiveTimeTestSequence d) : ℂ :=
  finiteSequenceSchwingerEvaluation family
    (finiteSchwartzSequenceConvolution d
      (finiteSchwartzSequenceReflectedStar d f.toFiniteSchwartzSequence)
      f.toFiniteSchwartzSequence)

/-- Reflection positivity on the current strict Mathlib test domain.

This is a strict-subdomain candidate predicate only until the source-space and topology bridges
are proved; it is not declared to be OS-I `(E2)`. -/
def MathlibStrictScalarReflectionPositivity
    {d : EuclideanDimension} (family : ScalarSchwingerDistributionFamily d) : Prop :=
  ∀ f : MathlibStrictPositiveTimeTestSequence d,
    IsNonnegativeComplexReal (mathlibStrictReflectionPositivityExpression family f)

/-- The predicate exposes its exact reflected-star convolution expression for every strict input. -/
theorem MathlibStrictScalarReflectionPositivity.apply
    {d : EuclideanDimension} {family : ScalarSchwingerDistributionFamily d}
    (h : MathlibStrictScalarReflectionPositivity family)
    (f : MathlibStrictPositiveTimeTestSequence d) :
    IsNonnegativeComplexReal (mathlibStrictReflectionPositivityExpression family f) :=
  h f

end YangMills
