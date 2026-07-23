/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Mathematics.CompactGroupConjugationCharacterFormula

/-!
# Convergent finite character-approximation sequences

Hall concludes that each continuous central function is uniformly approximated by a sequence of
finite character combinations. Given the exact compact-group central-density target, this file
selects one finite-support character coefficient family at tolerance `1/(n+1)` and proves:

* uniform convergence in `C(G, ℂ)`;
* convergence in the exact continuous-central subtype;
* convergence after mapping into normalized-Haar `L²`.

Faithful finite matrix coordinates plus second countability supply the density premise, so they give
the source-facing existence of such a sequence.

The selected sequence is noncanonical and is not a Fourier partial-sum sequence. No dual
countability, coefficientwise inversion, pointwise infinite sum, or heat-kernel series is inferred.
-/

namespace YangMills
namespace Mathematics

noncomputable section

universe uG

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]

/-- One noncanonically selected finite-support character coefficient family at uniform tolerance
`1/(n+1)`. -/
noncomputable def centralCharacterApproximationCoefficients
    (density : UnitaryMatrixDual.HasCentralContinuousPeterWeylDensity G)
    (f : continuousCentralFunctionStarSubalgebra G) (n : ℕ) :
    UnitaryMatrixDualCharacterCoefficients G :=
  Classical.choose (density.exists_character_approximation f
    (by positivity : 0 < (1 / (n + 1 : ℝ))))

omit [IsTopologicalGroup G] [T2Space G] [MeasurableSpace G] [BorelSpace G] in
/-- The selected finite character approximant has the exact prescribed strict uniform error bound. -/
theorem centralCharacterApproximationCoefficients_norm_sub_lt
    (density : UnitaryMatrixDual.HasCentralContinuousPeterWeylDensity G)
    (f : continuousCentralFunctionStarSubalgebra G) (n : ℕ) :
    ‖(unitaryMatrixDualCentralCharacterSynthesis G
        (centralCharacterApproximationCoefficients density f n) : C(G, ℂ)) -
      (f : C(G, ℂ))‖ < (1 / (n + 1 : ℝ)) :=
  Classical.choose_spec (density.exists_character_approximation f
    (by positivity : 0 < (1 / (n + 1 : ℝ))))

omit [IsTopologicalGroup G] [T2Space G] [MeasurableSpace G] [BorelSpace G] in
/-- The finite character approximants converge uniformly as continuous functions. -/
theorem tendsto_centralCharacterApproximationCoefficients
    (density : UnitaryMatrixDual.HasCentralContinuousPeterWeylDensity G)
    (f : continuousCentralFunctionStarSubalgebra G) :
    Filter.Tendsto (fun n =>
      (unitaryMatrixDualCentralCharacterSynthesis G
        (centralCharacterApproximationCoefficients density f n) : C(G, ℂ)))
      Filter.atTop (nhds (f : C(G, ℂ))) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  apply squeeze_zero
  · intro n
    positivity
  · intro n
    exact (centralCharacterApproximationCoefficients_norm_sub_lt density f n).le
  · simpa [Nat.cast_add, Nat.cast_one] using
      (tendsto_one_div_add_atTop_nhds_zero_nat :
        Filter.Tendsto (fun n : ℕ => (1 / (n + 1 : ℝ))) Filter.atTop (nhds 0))

omit [IsTopologicalGroup G] [T2Space G] [MeasurableSpace G] [BorelSpace G] in
/-- The same sequence converges in the exact continuous-central subtype. -/
theorem tendsto_centralCharacterApproximationCoefficients_in_central
    (density : UnitaryMatrixDual.HasCentralContinuousPeterWeylDensity G)
    (f : continuousCentralFunctionStarSubalgebra G) :
    Filter.Tendsto (fun n =>
      unitaryMatrixDualCentralCharacterSynthesis G
        (centralCharacterApproximationCoefficients density f n))
      Filter.atTop (nhds f) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  apply squeeze_zero
  · intro n
    positivity
  · intro n
    exact (centralCharacterApproximationCoefficients_norm_sub_lt density f n).le
  · simpa [Nat.cast_add, Nat.cast_one] using
      (tendsto_one_div_add_atTop_nhds_zero_nat :
        Filter.Tendsto (fun n : ℕ => (1 / (n + 1 : ℝ))) Filter.atTop (nhds 0))

omit [T2Space G] in
/-- Uniform convergence of the selected finite character sequence implies convergence in
normalized-Haar `L²`. -/
theorem tendsto_centralCharacterApproximationCoefficients_L2
    (density : UnitaryMatrixDual.HasCentralContinuousPeterWeylDensity G)
    (f : continuousCentralFunctionStarSubalgebra G) :
    Filter.Tendsto (fun n =>
      unitaryMatrixDualL2CharacterSynthesis G
        (centralCharacterApproximationCoefficients density f n))
      Filter.atTop (nhds (normalizedCompactHaarCentralContinuousToL2 G f)) := by
  change Filter.Tendsto (fun n => normalizedCompactHaarCentralContinuousToL2 G
      (unitaryMatrixDualCentralCharacterSynthesis G
        (centralCharacterApproximationCoefficients density f n)))
    Filter.atTop (nhds (normalizedCompactHaarCentralContinuousToL2 G f))
  exact ((normalizedCompactHaarCentralContinuousToL2 G).continuous.tendsto f).comp
    (tendsto_centralCharacterApproximationCoefficients_in_central density f)

/-- Source-facing conditional result: faithful finite matrix coordinates and second countability
produce a uniformly convergent sequence of finite selected-character combinations. -/
theorem exists_tendsto_finiteCharacterSynthesis_of_faithful
    [SecondCountableTopology G]
    (faithful : ContinuousFaithfulFiniteMatrixRepresentation G)
    (f : continuousCentralFunctionStarSubalgebra G) :
    ∃ coefficients : ℕ → UnitaryMatrixDualCharacterCoefficients G,
      Filter.Tendsto (fun n =>
        (unitaryMatrixDualCentralCharacterSynthesis G (coefficients n) : C(G, ℂ)))
        Filter.atTop (nhds (f : C(G, ℂ))) := by
  let density := unitaryMatrixDual_hasCentralContinuousPeterWeylDensity_of_faithful faithful
  exact ⟨centralCharacterApproximationCoefficients density f,
    tendsto_centralCharacterApproximationCoefficients density f⟩

/-- The same conditional finite-character sequence converges in normalized-Haar `L²`. -/
theorem exists_tendsto_finiteCharacterSynthesis_L2_of_faithful
    [SecondCountableTopology G]
    (faithful : ContinuousFaithfulFiniteMatrixRepresentation G)
    (f : continuousCentralFunctionStarSubalgebra G) :
    ∃ coefficients : ℕ → UnitaryMatrixDualCharacterCoefficients G,
      Filter.Tendsto (fun n => unitaryMatrixDualL2CharacterSynthesis G (coefficients n))
        Filter.atTop (nhds (normalizedCompactHaarCentralContinuousToL2 G f)) := by
  let density := unitaryMatrixDual_hasCentralContinuousPeterWeylDensity_of_faithful faithful
  exact ⟨centralCharacterApproximationCoefficients density f,
    tendsto_centralCharacterApproximationCoefficients_L2 density f⟩

/-- One and the same finite-support coefficient sequence converges both uniformly and in normalized-
Haar `L²` under faithful finite matrix coordinates and second countability. -/
theorem exists_tendsto_finiteCharacterSynthesis_and_L2_of_faithful
    [SecondCountableTopology G]
    (faithful : ContinuousFaithfulFiniteMatrixRepresentation G)
    (f : continuousCentralFunctionStarSubalgebra G) :
    ∃ coefficients : ℕ → UnitaryMatrixDualCharacterCoefficients G,
      Filter.Tendsto (fun n =>
        (unitaryMatrixDualCentralCharacterSynthesis G (coefficients n) : C(G, ℂ)))
          Filter.atTop (nhds (f : C(G, ℂ))) ∧
      Filter.Tendsto (fun n => unitaryMatrixDualL2CharacterSynthesis G (coefficients n))
        Filter.atTop (nhds (normalizedCompactHaarCentralContinuousToL2 G f)) := by
  let density := unitaryMatrixDual_hasCentralContinuousPeterWeylDensity_of_faithful faithful
  exact ⟨centralCharacterApproximationCoefficients density f,
    tendsto_centralCharacterApproximationCoefficients density f,
    tendsto_centralCharacterApproximationCoefficients_L2 density f⟩

end

end Mathematics
end YangMills
