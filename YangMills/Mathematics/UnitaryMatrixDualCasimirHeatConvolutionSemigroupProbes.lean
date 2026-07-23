/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Mathematics.UnitaryMatrixDualCasimirHeatConvolutionSemigroup

/-!
# Hostile probes for the candidate Casimir spectral convolution law
-/

namespace YangMills
namespace Mathematics
namespace UnitaryMatrixDualCasimirHeatConvolutionSemigroup
namespace Probes

noncomputable section

universe uG

variable {G : Type uG} [Group G] [TopologicalSpace G]

/-- The inverse-dimension convolution product of candidate coefficients is exactly the coefficient
at the sum of the times. -/
theorem exact_coefficient_addition
    (data : UnitaryMatrixDualHeatTraceSummabilityData (G := G))
    (s t : ℝ) (q : UnitaryMatrixDual G) :
    unitaryMatrixDualUniformCharacterConvolutionCoefficient
      (unitaryMatrixDualCasimirHeatCoefficient data s)
      (unitaryMatrixDualCasimirHeatCoefficient data t) q =
      unitaryMatrixDualCasimirHeatCoefficient data (s + t) q :=
  unitaryMatrixDualCasimirHeatConvolutionCoefficient data s t q

/-- Hostile coefficient probe: changing the exact time-addition coefficient is contradictory. -/
theorem changed_coefficient_addition_blocked
    (data : UnitaryMatrixDualHeatTraceSummabilityData (G := G))
    (s t : ℝ) (q : UnitaryMatrixDual G) (changed : ℂ)
    (hchanged : changed ≠ unitaryMatrixDualCasimirHeatCoefficient data (s + t) q)
    (changedProduct : unitaryMatrixDualUniformCharacterConvolutionCoefficient
      (unitaryMatrixDualCasimirHeatCoefficient data s)
      (unitaryMatrixDualCasimirHeatCoefficient data t) q = changed) : False := by
  apply hchanged
  rw [← changedProduct]
  exact unitaryMatrixDualCasimirHeatConvolutionCoefficient data s t q

variable [CompactSpace G] [IsTopologicalGroup G] [T2Space G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

/-- Exact positive-time convolution addition law in `C(G, ℂ)`. -/
theorem exact_positive_time_convolution
    (data : UnitaryMatrixDualHeatTraceSummabilityData (G := G))
    {s t : ℝ} (hs : 0 < s) (ht : 0 < t) :
    normalizedCompactHaarContinuousConvolution
      (unitaryMatrixDualCasimirHeatCharacterSeries data s)
      (unitaryMatrixDualCasimirHeatCharacterSeries data t) =
      unitaryMatrixDualCasimirHeatCharacterSeries data (s + t) :=
  normalizedCompactHaarContinuousConvolution_casimirHeatCharacterSeries data hs ht

/-- The same law retains the exact pointwise `f(x)g(x⁻¹z)` integral convention. -/
theorem exact_positive_time_pointwise_convolution
    (data : UnitaryMatrixDualHeatTraceSummabilityData (G := G))
    {s t : ℝ} (hs : 0 < s) (ht : 0 < t) (z : G) :
    normalizedCompactHaarComplexConvolution G
      (unitaryMatrixDualCasimirHeatCharacterSeries data s)
      (unitaryMatrixDualCasimirHeatCharacterSeries data t) z =
      unitaryMatrixDualCasimirHeatCharacterSeries data (s + t) z :=
  normalizedCompactHaarComplexConvolution_casimirHeatCharacterSeries data hs ht z

/-- Hostile family probe: replacing the exact sum-time spectral series by a genuinely different
continuous function is contradictory. -/
theorem changed_positive_time_convolution_blocked
    (data : UnitaryMatrixDualHeatTraceSummabilityData (G := G))
    {s t : ℝ} (hs : 0 < s) (ht : 0 < t) (changed : C(G, ℂ))
    (hchanged : changed ≠ unitaryMatrixDualCasimirHeatCharacterSeries data (s + t))
    (changedConvolution : normalizedCompactHaarContinuousConvolution
      (unitaryMatrixDualCasimirHeatCharacterSeries data s)
      (unitaryMatrixDualCasimirHeatCharacterSeries data t) = changed) : False := by
  apply hchanged
  rw [← changedConvolution]
  exact normalizedCompactHaarContinuousConvolution_casimirHeatCharacterSeries data hs ht

/-- The sum time remains in the positive-time domain needed for uniform convergence. -/
theorem sum_time_positive {s t : ℝ} (hs : 0 < s) (ht : 0 < t) : 0 < s + t :=
  add_pos hs ht

end

end Probes
end UnitaryMatrixDualCasimirHeatConvolutionSemigroup
end Mathematics
end YangMills
