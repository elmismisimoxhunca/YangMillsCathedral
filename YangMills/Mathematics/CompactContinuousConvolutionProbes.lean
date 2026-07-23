/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Mathematics.CompactContinuousConvolution

/-!
# Hostile probes for continuous compact-group convolution
-/

namespace YangMills
namespace Mathematics
namespace CompactContinuousConvolution
namespace Probes

noncomputable section

universe uG

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]

/-- Packaging preserves the exact raw `f(x)g(x⁻¹z)` convolution. -/
theorem exact_packaging (f g : C(G, ℂ)) (z : G) :
    normalizedCompactHaarContinuousConvolution f g z =
      normalizedCompactHaarComplexConvolution G f g z :=
  normalizedCompactHaarContinuousConvolution_apply f g z

/-- The packaged convolution is genuinely continuous. -/
theorem exact_continuity (f g : C(G, ℂ)) :
    Continuous (normalizedCompactHaarContinuousConvolution f g) :=
  (normalizedCompactHaarContinuousConvolution f g).continuous

/-- The probability-Haar sup-norm estimate is exposed exactly. -/
theorem exact_norm_bound (f g : C(G, ℂ)) :
    ‖normalizedCompactHaarContinuousConvolution f g‖ ≤ ‖f‖ * ‖g‖ :=
  norm_normalizedCompactHaarContinuousConvolution_le f g

/-- Hostile bound probe: an asserted strict violation of the convolution estimate is contradictory. -/
theorem norm_bound_violation_blocked (f g : C(G, ℂ))
    (violation : ‖f‖ * ‖g‖ < ‖normalizedCompactHaarContinuousConvolution f g‖) : False :=
  (not_lt_of_ge (norm_normalizedCompactHaarContinuousConvolution_le f g)) violation

/-- Fixing the right input gives exactly the same ordered convolution. -/
theorem exact_right_operator (f g : C(G, ℂ)) :
    normalizedCompactHaarContinuousConvolutionRight g f =
      normalizedCompactHaarContinuousConvolution f g :=
  normalizedCompactHaarContinuousConvolutionRight_apply g f

/-- Fixing the left input gives exactly the same ordered convolution. -/
theorem exact_left_operator (f g : C(G, ℂ)) :
    normalizedCompactHaarContinuousConvolutionLeft f g =
      normalizedCompactHaarContinuousConvolution f g :=
  normalizedCompactHaarContinuousConvolutionLeft_apply f g

/-- Fixed-right convolution exposes its expected operator-norm bound. -/
theorem exact_right_operator_norm_bound (g : C(G, ℂ)) :
    ‖normalizedCompactHaarContinuousConvolutionRight g‖ ≤ ‖g‖ :=
  norm_normalizedCompactHaarContinuousConvolutionRight_le g

/-- Fixed-left convolution exposes its expected operator-norm bound. -/
theorem exact_left_operator_norm_bound (f : C(G, ℂ)) :
    ‖normalizedCompactHaarContinuousConvolutionLeft f‖ ≤ ‖f‖ :=
  norm_normalizedCompactHaarContinuousConvolutionLeft_le f

/-- Hostile fixed-input bound probe. -/
theorem right_operator_norm_violation_blocked (g : C(G, ℂ))
    (violation : ‖g‖ < ‖normalizedCompactHaarContinuousConvolutionRight g‖) : False :=
  (not_lt_of_ge (norm_normalizedCompactHaarContinuousConvolutionRight_le g)) violation

/-- Hostile order probe: packaging cannot turn a witnessed noncommutative convolution pair into a
commutative one. -/
theorem ambient_commutativity_not_introduced (f g : C(G, ℂ)) (z : G)
    (orderedDifferent : normalizedCompactHaarComplexConvolution G f g z ≠
      normalizedCompactHaarComplexConvolution G g f z) :
    normalizedCompactHaarContinuousConvolution f g z ≠
      normalizedCompactHaarContinuousConvolution g f z := by
  simpa only [normalizedCompactHaarContinuousConvolution_apply] using orderedDifferent

end

end Probes
end CompactContinuousConvolution
end Mathematics
end YangMills
