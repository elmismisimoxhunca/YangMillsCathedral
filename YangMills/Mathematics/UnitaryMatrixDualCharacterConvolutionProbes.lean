/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Mathematics.UnitaryMatrixDualCharacterConvolution

/-!
# Hostile probes for selected-character convolution
-/

namespace YangMills
namespace Mathematics
namespace UnitaryMatrixDualCharacterConvolution
namespace Probes

noncomputable section

universe uG

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]

/-- Self-convolution has the exact inverse-dimension normalization. -/
theorem exact_character_self_convolution
    (q : UnitaryMatrixDual G) (z : G) :
    normalizedCompactHaarComplexConvolution G (unitaryMatrixDualCharacter q)
      (unitaryMatrixDualCharacter q) z =
      (unitaryMatrixDualDimension q : ℂ)⁻¹ * unitaryMatrixDualCharacter q z :=
  normalizedCompactHaar_unitaryMatrixDualCharacter_convolution_self q z

/-- Hostile normalization probe: changing the inverse-dimension self-convolution value is
contradictory. -/
theorem changed_character_self_convolution_blocked
    (q : UnitaryMatrixDual G) (z : G) {changed : ℂ}
    (hchanged : changed ≠
      (unitaryMatrixDualDimension q : ℂ)⁻¹ * unitaryMatrixDualCharacter q z)
    (changedConvolution :
      normalizedCompactHaarComplexConvolution G (unitaryMatrixDualCharacter q)
        (unitaryMatrixDualCharacter q) z = changed) : False := by
  apply hchanged
  rw [← changedConvolution]
  exact normalizedCompactHaar_unitaryMatrixDualCharacter_convolution_self q z

/-- Distinct selected irreducible characters convolve to zero. -/
theorem exact_distinct_character_convolution_zero
    {q r : UnitaryMatrixDual G} (hqr : q ≠ r) (z : G) :
    normalizedCompactHaarComplexConvolution G (unitaryMatrixDualCharacter q)
      (unitaryMatrixDualCharacter r) z = 0 :=
  normalizedCompactHaar_unitaryMatrixDualCharacter_convolution_ne hqr z

/-- Hostile distinct-class probe: a nonzero mixed convolution is contradictory. -/
theorem nonzero_distinct_character_convolution_blocked
    {q r : UnitaryMatrixDual G} (hqr : q ≠ r) (z : G)
    (nonzero : normalizedCompactHaarComplexConvolution G
      (unitaryMatrixDualCharacter q) (unitaryMatrixDualCharacter r) z ≠ 0) : False :=
  nonzero (normalizedCompactHaar_unitaryMatrixDualCharacter_convolution_ne hqr z)

/-- Unified exact Kronecker convolution formula. -/
theorem exact_character_convolution
    (q r : UnitaryMatrixDual G) (z : G) :
    normalizedCompactHaarComplexConvolution G (unitaryMatrixDualCharacter q)
      (unitaryMatrixDualCharacter r) z =
      if q = r then
        (unitaryMatrixDualDimension q : ℂ)⁻¹ * unitaryMatrixDualCharacter q z
      else 0 :=
  normalizedCompactHaar_unitaryMatrixDualCharacter_convolution q r z

/-- Although the ambient nonabelian convolution order remains fixed, irreducible central characters
commute under convolution. -/
theorem exact_character_convolution_comm
    (q r : UnitaryMatrixDual G) (z : G) :
    normalizedCompactHaarComplexConvolution G (unitaryMatrixDualCharacter q)
      (unitaryMatrixDualCharacter r) z =
    normalizedCompactHaarComplexConvolution G (unitaryMatrixDualCharacter r)
      (unitaryMatrixDualCharacter q) z := by
  by_cases hqr : q = r
  · subst r
    rfl
  · rw [normalizedCompactHaar_unitaryMatrixDualCharacter_convolution_ne hqr z,
      normalizedCompactHaar_unitaryMatrixDualCharacter_convolution_ne (Ne.symm hqr) z]

end

end Probes
end UnitaryMatrixDualCharacterConvolution
end Mathematics
end YangMills
