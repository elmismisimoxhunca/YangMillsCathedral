/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Euclidean.SchwingerConvolutionComponent
import YangMills.Euclidean.SchwingerTensorProductProbes

/-!
# Hostile probes for per-arity Schwinger convolution

The probes retain arity-zero multiplication, both arity-one endpoint terms, and the nonzero internal
split produced by two singleton bump sequences. They do not package a finite output sequence.
-/

namespace YangMills.Euclidean.SchwingerConvolutionComponent.Probes

/-- Arity-zero convolution is tied to multiplication of the exact stored scalars. -/
theorem exact_zero_arity_convolution
    (d : EuclideanDimension) (f g : MathlibStrictPositiveTimeTestSequence d) :
    schwingerSequenceConvolutionComponent d f g 0 =
      scalarZeroAritySchwartz d (f.zeroPoint * g.zeroPoint) :=
  schwingerSequenceConvolutionComponent_zero d f g

/-- Both endpoint terms remain visible at arity one. -/
theorem exact_one_arity_convolution
    (d : EuclideanDimension) (f g : MathlibStrictPositiveTimeTestSequence d) :
    schwingerSequenceConvolutionComponent d f g 1 =
      scalarSchwartzTensorProductOnConfiguration d
          (f.extendedComponent 1) (g.extendedComponent 0) +
        scalarSchwartzTensorProductOnConfiguration d
          (f.extendedComponent 0) (g.extendedComponent 1) :=
  schwingerSequenceConvolutionComponent_one d f g

/-- The internal `1+1=2` split of two singleton bump sequences is the exact bundled tensor. -/
theorem exact_singleton_bump_convolution_two
    (d : EuclideanDimension) :
    schwingerSequenceConvolutionComponent d
        (singletonPositiveTimeBumpSequence d)
        (singletonPositiveTimeBumpSequence d) 2 =
      scalarSchwartzTensorProductOnConfiguration d
        (positiveTimeBumpSchwartz d) (positiveTimeBumpSchwartz d) :=
  singletonPositiveTimeBump_convolutionComponent_two d

/-- The arity-two singleton convolution is genuinely nonzero. -/
theorem singleton_bump_convolution_two_ne_zero
    (d : EuclideanDimension) :
    schwingerSequenceConvolutionComponent d
      (singletonPositiveTimeBumpSequence d)
      (singletonPositiveTimeBumpSequence d) 2 ≠ 0 := by
  rw [singletonPositiveTimeBump_convolutionComponent_two]
  exact _root_.YangMills.Euclidean.SchwingerTensorProduct.Probes.bundled_positiveTimeBump_tensor_ne_zero d

/-- Replacing the exact arity-two convolution by zero contradicts its internal split. -/
theorem singleton_bump_convolution_replacement_blocked
    (d : EuclideanDimension)
    (hzero : schwingerSequenceConvolutionComponent d
      (singletonPositiveTimeBumpSequence d)
      (singletonPositiveTimeBumpSequence d) 2 = 0) : False :=
  singleton_bump_convolution_two_ne_zero d hzero

end YangMills.Euclidean.SchwingerConvolutionComponent.Probes
