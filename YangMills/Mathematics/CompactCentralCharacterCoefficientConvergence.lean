/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Mathematics.CompactCentralCharacterApproximationSequence
import YangMills.Mathematics.UnitaryMatrixDualCharacterL2Analysis

/-!
# Coefficientwise convergence of finite central character approximants

The previously selected finite-support character approximants converge in normalized-Haar `L²`.
Applying the norm-one character-analysis functional shows that, for each selected irreducible class
`q`, their `q`-coordinate converges to

`∫ conj(χ_q(g)) f(g) dμ_H(g)`.

Thus the arbitrary finite approximants have the correct coefficientwise limit. This does not turn
them into Fourier partial sums and does not construct a countable enumeration, an infinite sum, or
an inversion identity.
-/

namespace YangMills
namespace Mathematics

open MeasureTheory

noncomputable section

universe uG

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]

/-- Every selected coordinate of the finite character approximants converges to the corresponding
normalized-Haar `L²` character analysis coefficient. -/
theorem tendsto_centralCharacterApproximationCoefficients_apply
    (density : UnitaryMatrixDual.HasCentralContinuousPeterWeylDensity G)
    (f : continuousCentralFunctionStarSubalgebra G) (q : UnitaryMatrixDual G) :
    Filter.Tendsto (fun n => centralCharacterApproximationCoefficients density f n q)
      Filter.atTop (nhds (unitaryMatrixDualL2CharacterAnalysis q
        (normalizedCompactHaarCentralContinuousToL2 G f))) := by
  have h := ((unitaryMatrixDualL2CharacterAnalysis (G := G) q).continuous.tendsto
    (normalizedCompactHaarCentralContinuousToL2 G f)).comp
      (tendsto_centralCharacterApproximationCoefficients_L2 density f)
  change Filter.Tendsto (fun n => unitaryMatrixDualL2CharacterAnalysis q
    (unitaryMatrixDualL2CharacterSynthesis G
      (centralCharacterApproximationCoefficients density f n)))
    Filter.atTop (nhds (unitaryMatrixDualL2CharacterAnalysis q
      (normalizedCompactHaarCentralContinuousToL2 G f))) at h
  simpa only [unitaryMatrixDualL2CharacterAnalysis_synthesis] using h

/-- Source-facing form: every selected approximant coordinate converges to the exact normalized-Haar
character coefficient `∫ conj(χ_q) f`. -/
theorem tendsto_centralCharacterApproximationCoefficients_apply_integral
    (density : UnitaryMatrixDual.HasCentralContinuousPeterWeylDensity G)
    (f : continuousCentralFunctionStarSubalgebra G) (q : UnitaryMatrixDual G) :
    Filter.Tendsto (fun n => centralCharacterApproximationCoefficients density f n q)
      Filter.atTop (nhds (∫ g, star (unitaryMatrixDualCharacter q g) *
        (f : C(G, ℂ)) g ∂normalizedCompactHaarMeasure G)) := by
  rw [← unitaryMatrixDualL2CharacterAnalysis_continuousCentral_eq_integral f q]
  exact tendsto_centralCharacterApproximationCoefficients_apply density f q

/-- Under faithful finite matrix coordinates and second countability, one same finite-support
coefficient sequence converges uniformly, in normalized-Haar `L²`, and coordinatewise to every exact
normalized-Haar character coefficient. -/
theorem exists_tendsto_finiteCharacterSynthesis_and_L2_and_coefficients_of_faithful
    [SecondCountableTopology G]
    (faithful : ContinuousFaithfulFiniteMatrixRepresentation G)
    (f : continuousCentralFunctionStarSubalgebra G) :
    ∃ coefficients : ℕ → UnitaryMatrixDualCharacterCoefficients G,
      Filter.Tendsto (fun n =>
        (unitaryMatrixDualCentralCharacterSynthesis G (coefficients n) : C(G, ℂ)))
          Filter.atTop (nhds (f : C(G, ℂ))) ∧
      Filter.Tendsto (fun n => unitaryMatrixDualL2CharacterSynthesis G (coefficients n))
          Filter.atTop (nhds (normalizedCompactHaarCentralContinuousToL2 G f)) ∧
      ∀ q : UnitaryMatrixDual G,
        Filter.Tendsto (fun n => coefficients n q) Filter.atTop
          (nhds (∫ g, star (unitaryMatrixDualCharacter q g) *
            (f : C(G, ℂ)) g ∂normalizedCompactHaarMeasure G)) := by
  let density := unitaryMatrixDual_hasCentralContinuousPeterWeylDensity_of_faithful faithful
  exact ⟨centralCharacterApproximationCoefficients density f,
    tendsto_centralCharacterApproximationCoefficients density f,
    tendsto_centralCharacterApproximationCoefficients_L2 density f,
    tendsto_centralCharacterApproximationCoefficients_apply_integral density f⟩

end

end Mathematics
end YangMills
