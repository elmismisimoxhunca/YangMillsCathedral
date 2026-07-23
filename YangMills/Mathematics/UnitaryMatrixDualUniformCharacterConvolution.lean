/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Mathematics.CompactContinuousConvolution
import YangMills.Mathematics.UnitaryMatrixDualCharacterConvolution
import YangMills.Mathematics.UnitaryMatrixDualCharacterUniformSeries

/-!
# Convolution of uniformly summable selected-character series

For coefficient families satisfying the explicit weighted premises

`Summable (fun q => ‖a q‖ * dim(q))`,

this file extends the finite selected-character convolution formula through unconditional uniform
limits. With the project's fixed convention `(f⋆g)(z)=∫f(x)g(x⁻¹z)dμ_H(x)`, it proves

`series(a) ⋆ series(b) = series(fun q => a(q)b(q)dim(q)⁻¹)`.

The extension uses the bounded linear convolution operators on `C(G, ℂ)` and their `map_tsum`
theorems. It therefore does not exchange an unjustified infinite sum with an integral. No
Peter–Weyl completeness, general Fourier inversion, or heat-kernel claim is used.
-/

namespace YangMills
namespace Mathematics

noncomputable section

universe uG

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]

/-- Exact convolution of two selected characters, now as an equality in `C(G, ℂ)`. -/
theorem normalizedCompactHaarContinuousConvolution_continuousCharacter
    (q r : UnitaryMatrixDual G) :
    normalizedCompactHaarContinuousConvolution
      (unitaryMatrixDualContinuousCharacter q)
      (unitaryMatrixDualContinuousCharacter r) =
      if q = r then
        (unitaryMatrixDualDimension q : ℂ)⁻¹ • unitaryMatrixDualContinuousCharacter q
      else 0 := by
  by_cases hqr : q = r
  · subst r
    ext z
    simpa [normalizedCompactHaarContinuousConvolution_apply,
      unitaryMatrixDualContinuousCharacter] using
      (normalizedCompactHaar_unitaryMatrixDualCharacter_convolution_self q z)
  · ext z
    simpa [hqr, normalizedCompactHaarContinuousConvolution_apply,
      unitaryMatrixDualContinuousCharacter] using
      (normalizedCompactHaar_unitaryMatrixDualCharacter_convolution_ne hqr z)

/-- Convolving one selected character on the left with a weighted uniformly summable character
series extracts the matching coefficient and divides by the representation dimension. -/
theorem normalizedCompactHaarContinuousConvolution_continuousCharacter_uniformCharacterSeries
    (q : UnitaryMatrixDual G) (b : UnitaryMatrixDual G → ℂ)
    (hb : Summable (fun r => ‖b r‖ * (unitaryMatrixDualDimension r : ℝ))) :
    normalizedCompactHaarContinuousConvolution
      (unitaryMatrixDualContinuousCharacter q)
      (unitaryMatrixDualUniformCharacterSeries b) =
      (b q * (unitaryMatrixDualDimension q : ℂ)⁻¹) •
        unitaryMatrixDualContinuousCharacter q := by
  change normalizedCompactHaarContinuousConvolutionLeft
    (unitaryMatrixDualContinuousCharacter q)
    (∑' r, b r • unitaryMatrixDualContinuousCharacter r) = _
  rw [(normalizedCompactHaarContinuousConvolutionLeft
    (unitaryMatrixDualContinuousCharacter q)).map_tsum
      (summable_unitaryMatrixDualContinuousCharacter_smul b hb)]
  rw [tsum_eq_single q]
  · rw [map_smul, normalizedCompactHaarContinuousConvolutionLeft_apply,
      normalizedCompactHaarContinuousConvolution_continuousCharacter, if_pos rfl]
    module
  · intro r hrq
    rw [map_smul, normalizedCompactHaarContinuousConvolutionLeft_apply,
      normalizedCompactHaarContinuousConvolution_continuousCharacter, if_neg (Ne.symm hrq)]
    simp

/-- Convolving a weighted uniformly summable character series on the left with one selected
character extracts the matching coefficient with the same inverse-dimension normalization. -/
theorem normalizedCompactHaarContinuousConvolution_uniformCharacterSeries_continuousCharacter
    (a : UnitaryMatrixDual G → ℂ)
    (ha : Summable (fun q => ‖a q‖ * (unitaryMatrixDualDimension q : ℝ)))
    (r : UnitaryMatrixDual G) :
    normalizedCompactHaarContinuousConvolution
      (unitaryMatrixDualUniformCharacterSeries a)
      (unitaryMatrixDualContinuousCharacter r) =
      (a r * (unitaryMatrixDualDimension r : ℂ)⁻¹) •
        unitaryMatrixDualContinuousCharacter r := by
  change normalizedCompactHaarContinuousConvolutionRight
    (unitaryMatrixDualContinuousCharacter r)
    (∑' q, a q • unitaryMatrixDualContinuousCharacter q) = _
  rw [(normalizedCompactHaarContinuousConvolutionRight
    (unitaryMatrixDualContinuousCharacter r)).map_tsum
      (summable_unitaryMatrixDualContinuousCharacter_smul a ha)]
  rw [tsum_eq_single r]
  · rw [map_smul, normalizedCompactHaarContinuousConvolutionRight_apply,
      normalizedCompactHaarContinuousConvolution_continuousCharacter, if_pos rfl]
    module
  · intro q hqr
    rw [map_smul, normalizedCompactHaarContinuousConvolutionRight_apply,
      normalizedCompactHaarContinuousConvolution_continuousCharacter, if_neg hqr]
    simp

/-- Coefficientwise inverse-dimension product forced by normalized-Haar character convolution. -/
noncomputable def unitaryMatrixDualUniformCharacterConvolutionCoefficient
    (a b : UnitaryMatrixDual G → ℂ) (q : UnitaryMatrixDual G) : ℂ :=
  a q * b q * (unitaryMatrixDualDimension q : ℂ)⁻¹

/-- Exact convolution formula for two weighted uniformly summable selected-character series. The
proof passes each unconditional `tsum` through a bounded linear convolution operator. -/
theorem normalizedCompactHaarContinuousConvolution_uniformCharacterSeries
    (a b : UnitaryMatrixDual G → ℂ)
    (ha : Summable (fun q => ‖a q‖ * (unitaryMatrixDualDimension q : ℝ)))
    (hb : Summable (fun q => ‖b q‖ * (unitaryMatrixDualDimension q : ℝ))) :
    normalizedCompactHaarContinuousConvolution
      (unitaryMatrixDualUniformCharacterSeries a)
      (unitaryMatrixDualUniformCharacterSeries b) =
      unitaryMatrixDualUniformCharacterSeries
        (unitaryMatrixDualUniformCharacterConvolutionCoefficient a b) := by
  change normalizedCompactHaarContinuousConvolutionRight
    (unitaryMatrixDualUniformCharacterSeries b)
    (∑' q, a q • unitaryMatrixDualContinuousCharacter q) = _
  rw [(normalizedCompactHaarContinuousConvolutionRight
    (unitaryMatrixDualUniformCharacterSeries b)).map_tsum
      (summable_unitaryMatrixDualContinuousCharacter_smul a ha)]
  unfold unitaryMatrixDualUniformCharacterSeries
  apply tsum_congr
  intro q
  rw [map_smul, normalizedCompactHaarContinuousConvolutionRight_apply]
  change a q • normalizedCompactHaarContinuousConvolution
    (unitaryMatrixDualContinuousCharacter q)
    (unitaryMatrixDualUniformCharacterSeries b) = _
  rw [normalizedCompactHaarContinuousConvolution_continuousCharacter_uniformCharacterSeries
    q b hb]
  unfold unitaryMatrixDualUniformCharacterConvolutionCoefficient
  module

end

end Mathematics
end YangMills
