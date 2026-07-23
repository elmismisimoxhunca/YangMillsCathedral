/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Mathematics.UnitaryMatrixDualUniformCharacterConvolution

/-!
# Hostile probes for uniformly summable character-series convolution
-/

namespace YangMills
namespace Mathematics
namespace UnitaryMatrixDualUniformCharacterConvolution
namespace Probes

noncomputable section

universe uG

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]

/-- One character on the left extracts exactly one coefficient with inverse-dimension weight. -/
theorem exact_left_character_extraction
    (q : UnitaryMatrixDual G) (b : UnitaryMatrixDual G → ℂ)
    (hb : Summable (fun r => ‖b r‖ * (unitaryMatrixDualDimension r : ℝ))) :
    normalizedCompactHaarContinuousConvolution
      (unitaryMatrixDualContinuousCharacter q)
      (unitaryMatrixDualUniformCharacterSeries b) =
      (b q * (unitaryMatrixDualDimension q : ℂ)⁻¹) •
        unitaryMatrixDualContinuousCharacter q :=
  normalizedCompactHaarContinuousConvolution_continuousCharacter_uniformCharacterSeries q b hb

/-- One character on the right extracts exactly one coefficient with inverse-dimension weight. -/
theorem exact_right_character_extraction
    (a : UnitaryMatrixDual G → ℂ)
    (ha : Summable (fun q => ‖a q‖ * (unitaryMatrixDualDimension q : ℝ)))
    (r : UnitaryMatrixDual G) :
    normalizedCompactHaarContinuousConvolution
      (unitaryMatrixDualUniformCharacterSeries a)
      (unitaryMatrixDualContinuousCharacter r) =
      (a r * (unitaryMatrixDualDimension r : ℂ)⁻¹) •
        unitaryMatrixDualContinuousCharacter r :=
  normalizedCompactHaarContinuousConvolution_uniformCharacterSeries_continuousCharacter a ha r

/-- Two weighted unconditional series convolve by pointwise coefficient multiplication divided by
dimension. -/
theorem exact_uniform_series_convolution
    (a b : UnitaryMatrixDual G → ℂ)
    (ha : Summable (fun q => ‖a q‖ * (unitaryMatrixDualDimension q : ℝ)))
    (hb : Summable (fun q => ‖b q‖ * (unitaryMatrixDualDimension q : ℝ))) :
    normalizedCompactHaarContinuousConvolution
      (unitaryMatrixDualUniformCharacterSeries a)
      (unitaryMatrixDualUniformCharacterSeries b) =
      unitaryMatrixDualUniformCharacterSeries
        (unitaryMatrixDualUniformCharacterConvolutionCoefficient a b) :=
  normalizedCompactHaarContinuousConvolution_uniformCharacterSeries a b ha hb

/-- Hostile output probe: replacing the exact coefficientwise convolution series by a genuinely
different continuous function is contradictory. -/
theorem changed_uniform_series_convolution_blocked
    (a b : UnitaryMatrixDual G → ℂ)
    (ha : Summable (fun q => ‖a q‖ * (unitaryMatrixDualDimension q : ℝ)))
    (hb : Summable (fun q => ‖b q‖ * (unitaryMatrixDualDimension q : ℝ)))
    (changed : C(G, ℂ))
    (hchanged : changed ≠ unitaryMatrixDualUniformCharacterSeries
      (unitaryMatrixDualUniformCharacterConvolutionCoefficient a b))
    (changedConvolution : normalizedCompactHaarContinuousConvolution
      (unitaryMatrixDualUniformCharacterSeries a)
      (unitaryMatrixDualUniformCharacterSeries b) = changed) : False := by
  apply hchanged
  rw [← changedConvolution]
  exact normalizedCompactHaarContinuousConvolution_uniformCharacterSeries a b ha hb

/-- Central weighted character series commute under convolution because their scalar diagonal
coefficient products commute. This is not an ambient convolution-commutativity theorem. -/
theorem exact_uniform_character_series_convolution_comm
    (a b : UnitaryMatrixDual G → ℂ)
    (ha : Summable (fun q => ‖a q‖ * (unitaryMatrixDualDimension q : ℝ)))
    (hb : Summable (fun q => ‖b q‖ * (unitaryMatrixDualDimension q : ℝ))) :
    normalizedCompactHaarContinuousConvolution
      (unitaryMatrixDualUniformCharacterSeries a)
      (unitaryMatrixDualUniformCharacterSeries b) =
    normalizedCompactHaarContinuousConvolution
      (unitaryMatrixDualUniformCharacterSeries b)
      (unitaryMatrixDualUniformCharacterSeries a) := by
  rw [normalizedCompactHaarContinuousConvolution_uniformCharacterSeries a b ha hb,
    normalizedCompactHaarContinuousConvolution_uniformCharacterSeries b a hb ha]
  apply congrArg unitaryMatrixDualUniformCharacterSeries
  funext q
  unfold unitaryMatrixDualUniformCharacterConvolutionCoefficient
  ring

end

end Probes
end UnitaryMatrixDualUniformCharacterConvolution
end Mathematics
end YangMills
