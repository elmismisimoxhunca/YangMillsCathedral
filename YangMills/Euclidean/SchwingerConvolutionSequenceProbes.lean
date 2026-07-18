/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Euclidean.SchwingerConvolutionSequence
import YangMills.Euclidean.SchwingerConvolutionComponentProbes

/-!
# Hostile probes for finite convolution packaging

The probes ensure the bound controls the exact dependent components, output support is not a
finite-but-disconnected witness, and forgetting positive-time evidence preserves the earlier
nonzero internal convolution split.
-/

namespace YangMills.Euclidean.SchwingerConvolutionSequence.Probes

/-- Components above the exact support bound must vanish. -/
theorem component_above_support_bound_blocked
    (d : EuclideanDimension) (f : ScalarFiniteSchwartzSequence d) (n : ℕ)
    (habove : finiteSequenceSupportBound d f < n) : f.component n = 0 :=
  finiteSequence_component_eq_zero_above_bound d f n habove

/-- Packaged convolution support is exactly nonvanishing of the same output component. -/
theorem exact_convolution_support
    (d : EuclideanDimension) (f g : ScalarFiniteSchwartzSequence d) (N : ℕ) :
    N ∈ (finiteSchwartzSequenceConvolution d f g).support ↔
      (finiteSchwartzSequenceConvolution d f g).component N ≠ 0 :=
  (finiteSchwartzSequenceConvolution d f g).mem_support_iff N

/-- Forgetting positive-time evidence before convolution preserves the exact earlier component. -/
theorem exact_forget_positive_convolution
    (d : EuclideanDimension) (f g : MathlibStrictPositiveTimeTestSequence d) (N : ℕ) :
    (finiteSchwartzSequenceConvolution d
      f.toFiniteSchwartzSequence g.toFiniteSchwartzSequence).component N =
      schwingerSequenceConvolutionComponent d f g N :=
  finiteSchwartzSequenceConvolutionComponent_forget_positive d f g N

/-- The product of two singleton bump sequences has a nonzero arity-two output component. -/
theorem singleton_bump_product_component_two_ne_zero
    (d : EuclideanDimension) :
    (finiteSchwartzSequenceConvolution d
      (singletonPositiveTimeBumpSequence d).toFiniteSchwartzSequence
      (singletonPositiveTimeBumpSequence d).toFiniteSchwartzSequence).component 2 ≠ 0 := by
  change finiteSchwartzSequenceConvolutionComponent d
    (singletonPositiveTimeBumpSequence d).toFiniteSchwartzSequence
    (singletonPositiveTimeBumpSequence d).toFiniteSchwartzSequence 2 ≠ 0
  rw [finiteSchwartzSequenceConvolutionComponent_forget_positive]
  exact _root_.YangMills.Euclidean.SchwingerConvolutionComponent.Probes.singleton_bump_convolution_two_ne_zero d

/-- Exact output support cannot omit the nonzero arity-two internal split. -/
theorem singleton_bump_product_two_mem_support
    (d : EuclideanDimension) :
    2 ∈ (finiteSchwartzSequenceConvolution d
      (singletonPositiveTimeBumpSequence d).toFiniteSchwartzSequence
      (singletonPositiveTimeBumpSequence d).toFiniteSchwartzSequence).support :=
  ((finiteSchwartzSequenceConvolution d
    (singletonPositiveTimeBumpSequence d).toFiniteSchwartzSequence
    (singletonPositiveTimeBumpSequence d).toFiniteSchwartzSequence).mem_support_iff 2).2
      (singleton_bump_product_component_two_ne_zero d)

/-- A finite support that omitted the nonzero arity-two product term is rejected. -/
theorem omitted_product_support_blocked
    (d : EuclideanDimension)
    (homitted : 2 ∉ (finiteSchwartzSequenceConvolution d
      (singletonPositiveTimeBumpSequence d).toFiniteSchwartzSequence
      (singletonPositiveTimeBumpSequence d).toFiniteSchwartzSequence).support) : False :=
  homitted (singleton_bump_product_two_mem_support d)

end YangMills.Euclidean.SchwingerConvolutionSequence.Probes
