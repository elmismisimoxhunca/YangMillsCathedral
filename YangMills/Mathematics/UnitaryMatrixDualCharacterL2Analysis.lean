/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import Mathlib.MeasureTheory.Function.L2Space
import YangMills.Mathematics.UnitaryMatrixDualCentralL2Span
import YangMills.Mathematics.UnitaryMatrixDualL2Span

/-!
# Selected-dual character analysis in normalized-Haar L²

This file upgrades the finite normalized-Haar character pairing to Mathlib's actual `L²` carrier.
It constructs the unit `L²` vector represented by each selected irreducible character and the
continuous linear functional

`f ↦ ⟪χ_q, f⟫`.

The finite-support synthesis pairing is exactly the algebraic coefficient pairing, analysis recovers
every synthesized coefficient, and analysis of a continuous central function is the normalized-Haar
integral `∫ conj(χ_q) f`.

This is finite/algebraic Plancherel and coefficient analysis. It assumes no density, dual
countability, infinite summation, completeness, or inversion theorem.
-/

namespace YangMills
namespace Mathematics

open MeasureTheory

noncomputable section

universe uG

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]

/-- The actual normalized-Haar `L²` pairing of finite selected-character syntheses equals the
algebraic finitely supported character-coefficient pairing. -/
theorem unitaryMatrixDualL2CharacterSynthesis_inner
    (c d : UnitaryMatrixDualCharacterCoefficients G) :
    inner ℂ (unitaryMatrixDualL2CharacterSynthesis G c)
      (unitaryMatrixDualL2CharacterSynthesis G d) =
      unitaryMatrixDualCharacterCoefficientPairing c d := by
  letI : IsProbabilityMeasure (normalizedCompactHaarMeasure G) :=
    normalizedCompactHaarMeasure_isProbability G
  change inner ℂ
    (ContinuousMap.toLp 2 (normalizedCompactHaarMeasure G) ℂ
      (unitaryMatrixDualContinuousCharacterSynthesis G c))
    (ContinuousMap.toLp 2 (normalizedCompactHaarMeasure G) ℂ
      (unitaryMatrixDualContinuousCharacterSynthesis G d)) = _
  rw [ContinuousMap.inner_toLp]
  calc
    (∫ g, (unitaryMatrixDualContinuousCharacterSynthesis G d) g *
        star ((unitaryMatrixDualContinuousCharacterSynthesis G c) g)
      ∂normalizedCompactHaarMeasure G) =
      ∫ g, star (unitaryMatrixDualCharacterSynthesis G c g) *
        unitaryMatrixDualCharacterSynthesis G d g
      ∂normalizedCompactHaarMeasure G := by
        apply integral_congr_ae
        filter_upwards [] with g
        change unitaryMatrixDualCharacterSynthesis G d g *
          star (unitaryMatrixDualCharacterSynthesis G c g) =
          star (unitaryMatrixDualCharacterSynthesis G c g) *
            unitaryMatrixDualCharacterSynthesis G d g
        ring
    _ = _ := normalizedCompactHaar_unitaryMatrixDualCharacterSynthesis_pairing c d

/-- The normalized-Haar `L²` vector represented by one selected irreducible character. -/
noncomputable def unitaryMatrixDualL2CharacterVector
    (q : UnitaryMatrixDual G) : NormalizedCompactHaarL2 G :=
  unitaryMatrixDualL2CharacterSynthesis G (Finsupp.single q 1)

/-- Every selected irreducible character has normalized-Haar `L²` norm exactly one. -/
theorem norm_unitaryMatrixDualL2CharacterVector
    (q : UnitaryMatrixDual G) :
    ‖unitaryMatrixDualL2CharacterVector q‖ = 1 := by
  have hinner : inner ℂ (unitaryMatrixDualL2CharacterVector q)
      (unitaryMatrixDualL2CharacterVector q) = 1 := by
    rw [unitaryMatrixDualL2CharacterVector,
      unitaryMatrixDualL2CharacterSynthesis_inner]
    simp [unitaryMatrixDualCharacterCoefficientPairing]
  have hsquare : ‖unitaryMatrixDualL2CharacterVector q‖ ^ 2 = 1 := by
    rw [InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ), hinner]
    norm_num
  rcases sq_eq_one_iff.mp hsquare with h | h
  · exact h
  · nlinarith [norm_nonneg (unitaryMatrixDualL2CharacterVector q)]

/-- Continuous normalized-Haar `L²` analysis against one selected irreducible character. Mathlib's
complex inner product is linear in the second argument. -/
noncomputable def unitaryMatrixDualL2CharacterAnalysis
    (q : UnitaryMatrixDual G) : NormalizedCompactHaarL2 G →L[ℂ] ℂ :=
  (innerSL ℂ) (unitaryMatrixDualL2CharacterVector q)

/-- Character analysis has operator norm exactly one. -/
theorem norm_unitaryMatrixDualL2CharacterAnalysis
    (q : UnitaryMatrixDual G) :
    ‖unitaryMatrixDualL2CharacterAnalysis q‖ = 1 := by
  rw [unitaryMatrixDualL2CharacterAnalysis, innerSL_apply_norm,
    norm_unitaryMatrixDualL2CharacterVector]

/-- Analysis against a selected character exactly recovers the matching finite synthesis
coefficient. -/
@[simp]
theorem unitaryMatrixDualL2CharacterAnalysis_synthesis
    (c : UnitaryMatrixDualCharacterCoefficients G) (q : UnitaryMatrixDual G) :
    unitaryMatrixDualL2CharacterAnalysis q
      (unitaryMatrixDualL2CharacterSynthesis G c) = c q := by
  rw [unitaryMatrixDualL2CharacterAnalysis, unitaryMatrixDualL2CharacterVector,
    innerSL_apply_apply, unitaryMatrixDualL2CharacterSynthesis_inner]
  simp [unitaryMatrixDualCharacterCoefficientPairing]

omit [T2Space G] in
/-- On the continuous-central image, `L²` character analysis is exactly the source-facing
normalized-Haar integral `∫ conj(χ_q) f`. -/
theorem unitaryMatrixDualL2CharacterAnalysis_continuousCentral_eq_integral
    (f : continuousCentralFunctionStarSubalgebra G) (q : UnitaryMatrixDual G) :
    unitaryMatrixDualL2CharacterAnalysis q
      (normalizedCompactHaarCentralContinuousToL2 G f) =
      ∫ g, star (unitaryMatrixDualCharacter q g) * (f : C(G, ℂ)) g
        ∂normalizedCompactHaarMeasure G := by
  letI : IsProbabilityMeasure (normalizedCompactHaarMeasure G) :=
    normalizedCompactHaarMeasure_isProbability G
  rw [unitaryMatrixDualL2CharacterAnalysis, unitaryMatrixDualL2CharacterVector,
    innerSL_apply_apply]
  change inner ℂ
    (ContinuousMap.toLp 2 (normalizedCompactHaarMeasure G) ℂ
      (unitaryMatrixDualContinuousCharacterSynthesis G (Finsupp.single q 1)))
    (ContinuousMap.toLp 2 (normalizedCompactHaarMeasure G) ℂ (f : C(G, ℂ))) = _
  rw [ContinuousMap.inner_toLp]
  apply integral_congr_ae
  filter_upwards [] with g
  change (f : C(G, ℂ)) g *
    star (unitaryMatrixDualCharacterSynthesis G (Finsupp.single q 1) g) = _
  rw [unitaryMatrixDualCharacterSynthesis_single]
  simp
  ring

end

end Mathematics
end YangMills
