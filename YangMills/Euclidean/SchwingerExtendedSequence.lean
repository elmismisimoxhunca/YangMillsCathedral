/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Euclidean.SchwingerTensorProduct

/-!
# Uniform natural-arity views of finite Schwinger sequences

The Osterwalder–Schrader sequence product sums over all natural arities, including arity zero. This
module realizes a scalar as a genuine Schwartz test on the zero-point configuration space, extends a
finite sequence uniformly to every natural arity, and constructs the exact finite natural-number
support.

This is algebraic infrastructure. No sequence convolution, involution, direct-sum topology, or
reflection positivity is defined here.
-/

namespace YangMills

/-- Two positive arities are equal whenever their underlying natural arities are equal. -/
@[ext] theorem PositiveArity.ext {a b : PositiveArity} (h : a.value = b.value) : a = b := by
  cases a with
  | mk av ap =>
    cases b with
    | mk bv bp =>
      simp only at h
      subst bv
      rfl

/-- The natural value of a positive arity is never zero. -/
theorem PositiveArity.value_ne_zero (a : PositiveArity) : a.value ≠ 0 :=
  Nat.ne_of_gt a.positive

/-- A scalar represented as a Schwartz function on the zero-point Euclidean configuration space. -/
noncomputable def scalarZeroAritySchwartz
    (d : EuclideanDimension) (c : ℂ) : ScalarSchwartzTestFunction d 0 := by
  let f : EuclideanNPointSpace d 0 → ℂ := fun _ => c
  have compact : HasCompactSupport f := HasCompactSupport.of_compactSpace f
  have smooth : ContDiff ℝ (⊤ : ℕ∞) f := contDiff_const
  exact compact.toSchwartzMap smooth

/-- Zero-arity scalar Schwartz evaluation is the original scalar. -/
@[simp] theorem scalarZeroAritySchwartz_apply
    (d : EuclideanDimension) (c : ℂ) (x : EuclideanNPointSpace d 0) :
    scalarZeroAritySchwartz d c x = c :=
  rfl

@[simp] theorem scalarZeroAritySchwartz_zero (d : EuclideanDimension) :
    scalarZeroAritySchwartz d 0 = 0 := by
  ext x
  simp

@[simp] theorem scalarZeroAritySchwartz_add
    (d : EuclideanDimension) (a b : ℂ) :
    scalarZeroAritySchwartz d (a + b) =
      scalarZeroAritySchwartz d a + scalarZeroAritySchwartz d b := by
  ext x
  simp

@[simp] theorem scalarZeroAritySchwartz_smul
    (d : EuclideanDimension) (a b : ℂ) :
    scalarZeroAritySchwartz d (a * b) =
      a • scalarZeroAritySchwartz d b := by
  ext x
  simp [smul_eq_mul]

/-- The zero-arity Schwartz representation is injective. -/
theorem scalarZeroAritySchwartz_injective (d : EuclideanDimension) :
    Function.Injective (scalarZeroAritySchwartz d) := by
  intro a b h
  have atPoint := congrArg (fun f : ScalarSchwartzTestFunction d 0 =>
    f (fun i => Fin.elim0 i)) h
  simpa using atPoint

@[simp] theorem scalarZeroAritySchwartz_eq_zero_iff
    (d : EuclideanDimension) (c : ℂ) :
    scalarZeroAritySchwartz d c = 0 ↔ c = 0 := by
  constructor
  · intro h
    have atPoint := congrArg (fun f : ScalarSchwartzTestFunction d 0 =>
      f (fun i => Fin.elim0 i)) h
    simpa using atPoint
  · rintro rfl
    exact scalarZeroAritySchwartz_zero d

/-- Uniformly view a finite test sequence as one exact Schwartz component at every natural arity. -/
noncomputable def MathlibStrictPositiveTimeTestSequence.extendedComponent
    {d : EuclideanDimension} (f : MathlibStrictPositiveTimeTestSequence d) :
    (n : ℕ) → ScalarSchwartzTestFunction d n
  | 0 => scalarZeroAritySchwartz d f.zeroPoint
  | n + 1 => f.component ⟨n + 1, Nat.zero_lt_succ n⟩

@[simp] theorem MathlibStrictPositiveTimeTestSequence.extendedComponent_zero
    {d : EuclideanDimension} (f : MathlibStrictPositiveTimeTestSequence d) :
    f.extendedComponent 0 = scalarZeroAritySchwartz d f.zeroPoint :=
  rfl

@[simp] theorem MathlibStrictPositiveTimeTestSequence.extendedComponent_succ
    {d : EuclideanDimension} (f : MathlibStrictPositiveTimeTestSequence d) (n : ℕ) :
    f.extendedComponent (n + 1) = f.component ⟨n + 1, Nat.zero_lt_succ n⟩ :=
  rfl

@[simp] theorem MathlibStrictPositiveTimeTestSequence.extendedComponent_positive
    {d : EuclideanDimension} (f : MathlibStrictPositiveTimeTestSequence d)
    (n : PositiveArity) :
    f.extendedComponent n.value = f.component n := by
  rcases n with ⟨_ | k, hpos⟩
  · omega
  · rfl

/-- The exact finite support on all natural arities, including zero when the scalar component is
nonzero. -/
noncomputable def MathlibStrictPositiveTimeTestSequence.naturalSupport
    {d : EuclideanDimension} (f : MathlibStrictPositiveTimeTestSequence d) : Finset ℕ :=
  (if f.zeroPoint = 0 then ∅ else {0}) ∪ f.support.image PositiveArity.value

/-- Natural support membership is exactly nonvanishing of the same extended component. -/
theorem MathlibStrictPositiveTimeTestSequence.mem_naturalSupport_iff
    {d : EuclideanDimension} (f : MathlibStrictPositiveTimeTestSequence d) (n : ℕ) :
    n ∈ f.naturalSupport ↔ f.extendedComponent n ≠ 0 := by
  cases n with
  | zero =>
      constructor
      · intro hmem
        have hscalar : f.zeroPoint ≠ 0 := by
          intro hzero
          rw [MathlibStrictPositiveTimeTestSequence.naturalSupport, if_pos hzero] at hmem
          rcases Finset.mem_union.mp hmem with hempty | himage
          · simp at hempty
          · rcases Finset.mem_image.mp himage with ⟨q, hq, hqzero⟩
            exact q.value_ne_zero hqzero
        simpa using hscalar
      · intro hnonzero
        have hscalar : f.zeroPoint ≠ 0 := by
          intro hzero
          apply hnonzero
          simp [hzero]
        rw [MathlibStrictPositiveTimeTestSequence.naturalSupport, if_neg hscalar]
        simp
  | succ k =>
      let p : PositiveArity := ⟨k + 1, Nat.zero_lt_succ k⟩
      have himage : k + 1 ∈ f.support.image PositiveArity.value ↔ p ∈ f.support := by
        constructor
        · intro h
          rcases Finset.mem_image.mp h with ⟨q, hq, hvalue⟩
          have hqp : q = p := PositiveArity.ext hvalue
          simpa [hqp] using hq
        · intro hp
          exact Finset.mem_image.mpr ⟨p, hp, rfl⟩
      rw [MathlibStrictPositiveTimeTestSequence.naturalSupport,
        Finset.mem_union, himage, f.mem_support_iff p]
      have hnotzero : k + 1 ∉
          (if f.zeroPoint = 0 then (∅ : Finset ℕ) else {0}) := by
        split <;> simp
      simp only [hnotzero, false_or]
      rfl

/-- The sequence with scalar zero-point component one and every positive component zero. -/
noncomputable def unitZeroPointTestSequence (d : EuclideanDimension) :
    MathlibStrictPositiveTimeTestSequence d where
  zeroPoint := 1
  support := ∅
  component := fun _ => 0
  component_ordered := fun n => zero_hasStrictPositiveTimeOrderedSupport d n.value
  component_flat := fun n => zero_isFlatAtPointCoincidences d n.value
  mem_support_iff := by simp

end YangMills
