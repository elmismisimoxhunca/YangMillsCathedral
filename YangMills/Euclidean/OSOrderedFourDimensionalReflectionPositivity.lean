/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Euclidean.OSOrderedFourDimensionalTestSequence
import YangMills.Euclidean.SchwingerReflectionPositivityForm

/-!
# Reflection positivity on the exact four-dimensional OS-I source carrier

OS-I `(E2)` evaluates the Schwinger functional on the reflected-star product of every finite
positive-time source sequence. This module forgets the exact derivative-vanishing source evidence
into the unrestricted finite Schwartz sequence without changing any component, and states that
algebraic positivity condition.

This is exact source-carrier `(E2)` data. The completed positive-half-space tensor carriers,
nuclearity, OS-II growth, and reconstruction are distinct obligations rather than prerequisites for
this algebraic positivity condition. No positive Schwinger family is constructed.
-/

namespace YangMills

noncomputable section

namespace OSPositiveTimeOrderedFourDimensionalTestSequence

/-- Uniform natural-arity Schwartz component of an exact source sequence. -/
noncomputable def extendedComponent
    (f : OSPositiveTimeOrderedFourDimensionalTestSequence) :
    (n : ℕ) → ScalarSchwartzTestFunction EuclideanDimension.four n
  | 0 => scalarZeroAritySchwartz EuclideanDimension.four f.zeroPoint
  | n + 1 => (f.component ⟨n + 1, Nat.zero_lt_succ n⟩).toSchwartz

@[simp] theorem extendedComponent_zero
    (f : OSPositiveTimeOrderedFourDimensionalTestSequence) :
    f.extendedComponent 0 =
      scalarZeroAritySchwartz EuclideanDimension.four f.zeroPoint :=
  rfl

@[simp] theorem extendedComponent_positive
    (f : OSPositiveTimeOrderedFourDimensionalTestSequence) (arity : PositiveArity) :
    f.extendedComponent arity.value = (f.component arity).toSchwartz := by
  rcases arity with ⟨_ | n, positive⟩
  · omega
  · rfl

/-- Exact finite natural-number support, including zero precisely when the scalar is nonzero. -/
noncomputable def naturalSupport
    (f : OSPositiveTimeOrderedFourDimensionalTestSequence) : Finset ℕ :=
  (if f.zeroPoint = 0 then ∅ else {0}) ∪ f.support.image PositiveArity.value

/-- Natural support is tied to nonvanishing of the exact extended Schwartz component. -/
theorem mem_naturalSupport_iff
    (f : OSPositiveTimeOrderedFourDimensionalTestSequence) (n : ℕ) :
    n ∈ f.naturalSupport ↔ f.extendedComponent n ≠ 0 := by
  cases n with
  | zero =>
      constructor
      · intro hmem
        have hscalar : f.zeroPoint ≠ 0 := by
          intro hzero
          rw [naturalSupport, if_pos hzero] at hmem
          rcases Finset.mem_union.mp hmem with hempty | himage
          · simp at hempty
          · rcases Finset.mem_image.mp himage with ⟨arity, _, hzeroValue⟩
            exact arity.value_ne_zero hzeroValue
        simpa using hscalar
      · intro hnonzero
        have hscalar : f.zeroPoint ≠ 0 := by
          intro hzero
          apply hnonzero
          simp [hzero]
        rw [naturalSupport, if_neg hscalar]
        simp
  | succ n =>
      let arity : PositiveArity := ⟨n + 1, Nat.zero_lt_succ n⟩
      have himage :
          n + 1 ∈ f.support.image PositiveArity.value ↔ arity ∈ f.support := by
        constructor
        · intro h
          rcases Finset.mem_image.mp h with ⟨other, hother, hvalue⟩
          have equality : other = arity := PositiveArity.ext hvalue
          simpa [equality] using hother
        · intro h
          exact Finset.mem_image.mpr ⟨arity, h, rfl⟩
      rw [naturalSupport, Finset.mem_union, himage, f.mem_support_iff arity]
      have hnotzero : n + 1 ∉
          (if f.zeroPoint = 0 then (∅ : Finset ℕ) else {0}) := by
        split <;> simp
      simp only [hnotzero, false_or]
      rfl

/-- Forget source membership while preserving the exact scalar, all positive components, and exact
finite support. The output is unrestricted because reflected products do not stay positive-time. -/
noncomputable def toFiniteSchwartzSequence
    (f : OSPositiveTimeOrderedFourDimensionalTestSequence) :
    ScalarFiniteSchwartzSequence EuclideanDimension.four where
  support := f.naturalSupport
  component := f.extendedComponent
  mem_support_iff := f.mem_naturalSupport_iff

@[simp] theorem toFiniteSchwartzSequence_support
    (f : OSPositiveTimeOrderedFourDimensionalTestSequence) :
    f.toFiniteSchwartzSequence.support = f.naturalSupport :=
  rfl

@[simp] theorem toFiniteSchwartzSequence_component
    (f : OSPositiveTimeOrderedFourDimensionalTestSequence) (n : ℕ) :
    f.toFiniteSchwartzSequence.component n = f.extendedComponent n :=
  rfl

/-- The strict-to-source inclusion forgets back to the exact same unrestricted Schwartz
sequence; no component or support is changed. -/
theorem toFiniteSchwartzSequence_ofStrict
    (f : MathlibStrictPositiveTimeTestSequence EuclideanDimension.four) :
    f.toFourDimensionalOSSourceSequence.toFiniteSchwartzSequence =
      f.toFiniteSchwartzSequence := by
  apply ScalarFiniteSchwartzSequence.ext
  intro n
  cases n with
  | zero => rfl
  | succ n => rfl

end OSPositiveTimeOrderedFourDimensionalTestSequence

/-- Exact source-carrier `(Θ f*) × f` evaluation in four Euclidean dimensions. -/
noncomputable def osSourceFourDimensionalReflectionPositivityExpression
    (family : ScalarSchwingerDistributionFamily EuclideanDimension.four)
    (f : OSPositiveTimeOrderedFourDimensionalTestSequence) : ℂ :=
  finiteSequenceSchwingerEvaluation family
    (finiteSchwartzSequenceConvolution EuclideanDimension.four
      (finiteSchwartzSequenceReflectedStar EuclideanDimension.four
        f.toFiniteSchwartzSequence)
      f.toFiniteSchwartzSequence)

/-- Algebraic OS-I `(E2)` on the exact four-dimensional derivative-vanishing source carrier.

This predicate alone is insufficient for corrected OS-II reconstruction. -/
def OSSourceFourDimensionalReflectionPositivity
    (family : ScalarSchwingerDistributionFamily EuclideanDimension.four) : Prop :=
  ∀ f : OSPositiveTimeOrderedFourDimensionalTestSequence,
    IsNonnegativeComplexReal
      (osSourceFourDimensionalReflectionPositivityExpression family f)

/-- Source reflection positivity exposes the exact reflected-star convolution for every source
sequence, including source tests not known to have strict topological support. -/
theorem OSSourceFourDimensionalReflectionPositivity.apply
    {family : ScalarSchwingerDistributionFamily EuclideanDimension.four}
    (positive : OSSourceFourDimensionalReflectionPositivity family)
    (f : OSPositiveTimeOrderedFourDimensionalTestSequence) :
    IsNonnegativeComplexReal
      (osSourceFourDimensionalReflectionPositivityExpression family f) :=
  positive f

/-- On the embedded strict carrier, the source expression is exactly the earlier strict expression. -/
theorem osSourceFourDimensionalReflectionPositivityExpression_ofStrict
    (family : ScalarSchwingerDistributionFamily EuclideanDimension.four)
    (f : MathlibStrictPositiveTimeTestSequence EuclideanDimension.four) :
    osSourceFourDimensionalReflectionPositivityExpression family
        f.toFourDimensionalOSSourceSequence =
      mathlibStrictReflectionPositivityExpression family f := by
  unfold osSourceFourDimensionalReflectionPositivityExpression
    mathlibStrictReflectionPositivityExpression
  rw [OSPositiveTimeOrderedFourDimensionalTestSequence.toFiniteSchwartzSequence_ofStrict]

/-- Exact source-carrier positivity implies the earlier strict-subdomain predicate. The converse is
not claimed without a density/completion bridge. -/
theorem OSSourceFourDimensionalReflectionPositivity.toMathlibStrict
    {family : ScalarSchwingerDistributionFamily EuclideanDimension.four}
    (positive : OSSourceFourDimensionalReflectionPositivity family) :
    MathlibStrictScalarReflectionPositivity family := by
  intro f
  rw [← osSourceFourDimensionalReflectionPositivityExpression_ofStrict]
  exact positive f.toFourDimensionalOSSourceSequence

end

end YangMills
