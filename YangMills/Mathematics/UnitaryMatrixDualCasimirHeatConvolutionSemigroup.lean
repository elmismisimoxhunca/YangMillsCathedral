/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Mathematics.UnitaryMatrixDualCasimirHeatCharacterSeries
import YangMills.Mathematics.UnitaryMatrixDualUniformCharacterConvolution

/-!
# Positive-time convolution law for the candidate Casimir spectral series

From caller-supplied `UnitaryMatrixDualHeatTraceSummabilityData`, the existing construction provides
the uniformly convergent central spectral series with coefficient

`d_q exp (-(t/2)c_q)`.

The exact inverse-dimension character convolution law now forces

`K_s ⋆ K_t = K_{s+t}`

for `s,t > 0`. This file proves that law first coefficientwise and then in `C(G, ℂ)` by the weighted
uniform-series convolution theorem. It also exposes the corresponding pointwise normalized-Haar
integral formula with the unchanged convention `f(x)g(x⁻¹z)`.

This is a conditional positive-time convolution-semigroup law for the candidate spectral family. It
does **not** construct the summability data, identify `c_q` with the geometric Laplacian, prove the
heat equation, prove positivity or Haar normalization, supply a time-zero identity, or establish
heat-kernel status.
-/

namespace YangMills
namespace Mathematics

noncomputable section

universe uG

variable {G : Type uG} [Group G] [TopologicalSpace G]

/-- After the inverse-dimension factor forced by character convolution, the product of two candidate
Casimir heat coefficients is exactly the coefficient at the sum of the times. -/
theorem unitaryMatrixDualCasimirHeatConvolutionCoefficient
    (data : UnitaryMatrixDualHeatTraceSummabilityData (G := G))
    (s t : ℝ) (q : UnitaryMatrixDual G) :
    unitaryMatrixDualUniformCharacterConvolutionCoefficient
      (unitaryMatrixDualCasimirHeatCoefficient data s)
      (unitaryMatrixDualCasimirHeatCoefficient data t) q =
      unitaryMatrixDualCasimirHeatCoefficient data (s + t) q := by
  unfold unitaryMatrixDualUniformCharacterConvolutionCoefficient
    unitaryMatrixDualCasimirHeatCoefficient
  have hd : (unitaryMatrixDualDimension q : ℂ) ≠ 0 := by
    exact_mod_cast (unitaryMatrixDualRepresentative q).dimension_pos.ne'
  have hadd :
      (unitaryMatrixDualDimension q : ℂ) *
          (unitaryMatrixDualCasimirHeatCoefficientReal data (s + t) q : ℂ) =
        (unitaryMatrixDualCasimirHeatCoefficientReal data s q : ℂ) *
          (unitaryMatrixDualCasimirHeatCoefficientReal data t q : ℂ) := by
    exact_mod_cast unitaryMatrixDualCasimirHeatCoefficientReal_add data s t q
  rw [← hadd]
  field_simp

variable [CompactSpace G] [IsTopologicalGroup G] [T2Space G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

/-- The caller-supplied positive-time Casimir spectral family satisfies the exact normalized-Haar
convolution addition law in the global uniform norm. -/
theorem normalizedCompactHaarContinuousConvolution_casimirHeatCharacterSeries
    (data : UnitaryMatrixDualHeatTraceSummabilityData (G := G))
    {s t : ℝ} (hs : 0 < s) (ht : 0 < t) :
    normalizedCompactHaarContinuousConvolution
      (unitaryMatrixDualCasimirHeatCharacterSeries data s)
      (unitaryMatrixDualCasimirHeatCharacterSeries data t) =
      unitaryMatrixDualCasimirHeatCharacterSeries data (s + t) := by
  unfold unitaryMatrixDualCasimirHeatCharacterSeries
  rw [normalizedCompactHaarContinuousConvolution_uniformCharacterSeries _ _
    (summable_norm_unitaryMatrixDualCasimirHeatCoefficient_mul_dimension data hs)
    (summable_norm_unitaryMatrixDualCasimirHeatCoefficient_mul_dimension data ht)]
  apply congrArg unitaryMatrixDualUniformCharacterSeries
  funext q
  exact unitaryMatrixDualCasimirHeatConvolutionCoefficient data s t q

/-- Pointwise integral form of the same positive-time convolution-addition law, retaining the exact
`f(x)g(x⁻¹z)` order. -/
theorem normalizedCompactHaarComplexConvolution_casimirHeatCharacterSeries
    (data : UnitaryMatrixDualHeatTraceSummabilityData (G := G))
    {s t : ℝ} (hs : 0 < s) (ht : 0 < t) (z : G) :
    normalizedCompactHaarComplexConvolution G
      (unitaryMatrixDualCasimirHeatCharacterSeries data s)
      (unitaryMatrixDualCasimirHeatCharacterSeries data t) z =
      unitaryMatrixDualCasimirHeatCharacterSeries data (s + t) z := by
  have h := congrArg (fun f : C(G, ℂ) => f z)
    (normalizedCompactHaarContinuousConvolution_casimirHeatCharacterSeries data hs ht)
  exact h

end

end Mathematics
end YangMills
