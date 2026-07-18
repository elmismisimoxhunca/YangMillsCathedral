/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Euclidean.SchwingerExtendedSequence

/-!
# Per-arity convolution of finite Schwinger test sequences

Osterwalder–Schrader I defines the sequence product by
`(f × g)ₙ = ∑ᵣ fₙ₋ᵣ × gᵣ`. This module constructs that finite sum as an exact bundled `n`-point
Schwartz test, including both arity-zero endpoints.

Only the per-arity component is defined in this module.
`YangMills.Euclidean.SchwingerConvolutionSequence` proves exact finite support and packages all
components in the unrestricted sequence carrier. Installing a direct-sum
topology remains separate work. The convolution output is not claimed to preserve the strict
positive-time ordered subspace.
-/

namespace YangMills

/-- Transport a scalar Schwartz test along equality of its natural arity. -/
noncomputable def castScalarSchwartzArity
    {d : EuclideanDimension} {n m : ℕ} (h : n = m)
    (f : ScalarSchwartzTestFunction d n) : ScalarSchwartzTestFunction d m :=
  h ▸ f

@[simp] theorem castScalarSchwartzArity_rfl
    {d : EuclideanDimension} {n : ℕ} (f : ScalarSchwartzTestFunction d n) :
    castScalarSchwartzArity rfl f = f :=
  rfl

@[simp] theorem castScalarSchwartzArity_zero
    {d : EuclideanDimension} {n m : ℕ} (h : n = m) :
    castScalarSchwartzArity h (0 : ScalarSchwartzTestFunction d n) = 0 := by
  subst m
  rfl

/-- The exact `N`-point component of the finite sequence convolution. -/
noncomputable def schwingerSequenceConvolutionComponent
    (d : EuclideanDimension) (f g : MathlibStrictPositiveTimeTestSequence d) (N : ℕ) :
    ScalarSchwartzTestFunction d N :=
  ∑ r : Fin (N + 1),
    castScalarSchwartzArity
      (Nat.sub_add_cancel (Nat.le_of_lt_succ r.isLt))
      (scalarSchwartzTensorProductOnConfiguration d
        (f.extendedComponent (N - r)) (g.extendedComponent r))

/-- At arity zero, convolution is multiplication of the two scalar zero-point components. -/
theorem schwingerSequenceConvolutionComponent_zero
    (d : EuclideanDimension) (f g : MathlibStrictPositiveTimeTestSequence d) :
    schwingerSequenceConvolutionComponent d f g 0 =
      scalarZeroAritySchwartz d (f.zeroPoint * g.zeroPoint) := by
  ext x
  simp [schwingerSequenceConvolutionComponent, castScalarSchwartzArity]
  rw [scalarSchwartzTensorProductOnConfiguration_apply]
  simp [scalarSchwartzRawTensorKernel]

/-- At arity one, the exact two endpoint terms are `f₁ × g₀` and `f₀ × g₁`. -/
theorem schwingerSequenceConvolutionComponent_one
    (d : EuclideanDimension) (f g : MathlibStrictPositiveTimeTestSequence d) :
    schwingerSequenceConvolutionComponent d f g 1 =
      scalarSchwartzTensorProductOnConfiguration d
          (f.extendedComponent 1) (g.extendedComponent 0) +
        scalarSchwartzTensorProductOnConfiguration d
          (f.extendedComponent 0) (g.extendedComponent 1) := by
  simp [schwingerSequenceConvolutionComponent, castScalarSchwartzArity, Fin.sum_univ_two]

/-- Convolving the two singleton arity-one bump sequences gives exactly the two-bump tensor at
arity two. -/
theorem singletonPositiveTimeBump_convolutionComponent_two
    (d : EuclideanDimension) :
    schwingerSequenceConvolutionComponent d
        (singletonPositiveTimeBumpSequence d)
        (singletonPositiveTimeBumpSequence d) 2 =
      scalarSchwartzTensorProductOnConfiguration d
        (positiveTimeBumpSchwartz d) (positiveTimeBumpSchwartz d) := by
  have htwo : (⟨2, by decide⟩ : PositiveArity) ≠ PositiveArity.one := by
    intro h
    have := congrArg PositiveArity.value h
    norm_num at this
  have hone : (⟨1, by decide⟩ : PositiveArity) = PositiveArity.one :=
    PositiveArity.ext rfl
  simp [schwingerSequenceConvolutionComponent, castScalarSchwartzArity,
    Fin.sum_univ_succ, singletonPositiveTimeBumpSequence,
    singletonPositiveTimeBumpComponent, htwo, hone]

end YangMills
