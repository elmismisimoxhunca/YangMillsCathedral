/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Euclidean.SchwingerFiniteSequence
import YangMills.Euclidean.SchwingerConvolutionComponent

/-!
# Finite convolution of unrestricted Schwinger sequences

This module packages the Osterwalder–Schrader convolution as an unrestricted finite Schwartz
sequence. Support finiteness is proved from the exact finite supports of the two inputs: beyond the
sum of their support suprema, every split has at least one zero factor.

The strict positive-time convolution component already defined is proved to agree definitionally
with convolution after forgetting to the unrestricted carrier. No direct-sum topology or reflection
positivity is introduced.
-/

namespace YangMills

/-- A numerical upper bound for exact support of an unrestricted finite sequence. -/
noncomputable def finiteSequenceSupportBound
    (d : EuclideanDimension) (f : ScalarFiniteSchwartzSequence d) : ℕ :=
  f.support.sup id

/-- Every component strictly above the support bound vanishes. -/
theorem finiteSequence_component_eq_zero_above_bound
    (d : EuclideanDimension) (f : ScalarFiniteSchwartzSequence d) (n : ℕ)
    (h : finiteSequenceSupportBound d f < n) : f.component n = 0 := by
  by_contra hnonzero
  have hmem := (f.mem_support_iff n).2 hnonzero
  have hle : n ≤ finiteSequenceSupportBound d f := by
    exact Finset.le_sup (f := id) hmem
  omega

/-- The exact convolution component for unrestricted finite Schwartz sequences. -/
noncomputable def finiteSchwartzSequenceConvolutionComponent
    (d : EuclideanDimension) (f g : ScalarFiniteSchwartzSequence d) (N : ℕ) :
    ScalarSchwartzTestFunction d N :=
  ∑ r : Fin (N + 1),
    castScalarSchwartzArity
      (Nat.sub_add_cancel (Nat.le_of_lt_succ r.isLt))
      (scalarSchwartzTensorProductOnConfiguration d
        (f.component (N - r)) (g.component r))

/-- The convolution component vanishes above the sum of input support bounds. -/
theorem finiteSchwartzSequenceConvolutionComponent_eq_zero_above_bound
    (d : EuclideanDimension) (f g : ScalarFiniteSchwartzSequence d) (N : ℕ)
    (h : finiteSequenceSupportBound d f + finiteSequenceSupportBound d g < N) :
    finiteSchwartzSequenceConvolutionComponent d f g N = 0 := by
  unfold finiteSchwartzSequenceConvolutionComponent
  apply Finset.sum_eq_zero
  intro r hr
  by_cases hrg : r.val ≤ finiteSequenceSupportBound d g
  · have hfout : finiteSequenceSupportBound d f < N - r.val := by omega
    rw [finiteSequence_component_eq_zero_above_bound d f _ hfout]
    simp
  · have hgout : finiteSequenceSupportBound d g < r.val := by omega
    rw [finiteSequence_component_eq_zero_above_bound d g _ hgout]
    simp

/-- Exact finite support of the unrestricted convolution, filtered within the proved bound. -/
noncomputable def finiteSchwartzSequenceConvolutionSupport
    (d : EuclideanDimension) (f g : ScalarFiniteSchwartzSequence d) : Finset ℕ := by
  classical
  exact (Finset.range
    (finiteSequenceSupportBound d f + finiteSequenceSupportBound d g + 1)).filter
      (fun N => finiteSchwartzSequenceConvolutionComponent d f g N ≠ 0)

/-- Convolution-support membership is exactly nonvanishing of the same convolution component. -/
theorem mem_finiteSchwartzSequenceConvolutionSupport_iff
    (d : EuclideanDimension) (f g : ScalarFiniteSchwartzSequence d) (N : ℕ) :
    N ∈ finiteSchwartzSequenceConvolutionSupport d f g ↔
      finiteSchwartzSequenceConvolutionComponent d f g N ≠ 0 := by
  classical
  constructor
  · exact fun h => (Finset.mem_filter.mp h).2
  · intro hnonzero
    apply Finset.mem_filter.mpr
    constructor
    · rw [Finset.mem_range]
      by_contra hout
      have habove :
          finiteSequenceSupportBound d f + finiteSequenceSupportBound d g < N := by
        omega
      exact hnonzero
        (finiteSchwartzSequenceConvolutionComponent_eq_zero_above_bound d f g N habove)
    · exact hnonzero

/-- The unrestricted finite convolution/product of two finite scalar Schwartz sequences. -/
noncomputable def finiteSchwartzSequenceConvolution
    (d : EuclideanDimension) (f g : ScalarFiniteSchwartzSequence d) :
    ScalarFiniteSchwartzSequence d where
  support := finiteSchwartzSequenceConvolutionSupport d f g
  component := finiteSchwartzSequenceConvolutionComponent d f g
  mem_support_iff := mem_finiteSchwartzSequenceConvolutionSupport_iff d f g

/-- Convolution after forgetting strict positive-time evidence agrees with the earlier exact
per-arity formula. -/
theorem finiteSchwartzSequenceConvolutionComponent_forget_positive
    (d : EuclideanDimension) (f g : MathlibStrictPositiveTimeTestSequence d) (N : ℕ) :
    finiteSchwartzSequenceConvolutionComponent d
        f.toFiniteSchwartzSequence g.toFiniteSchwartzSequence N =
      schwingerSequenceConvolutionComponent d f g N :=
  rfl

end YangMills
